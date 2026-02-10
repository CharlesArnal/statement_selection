## INTRODUCTION

In the last five years, several challenging problems in combinatorics have been solved in an unexpected way using polynomials. This new approach is called the polynomial method, and the goal of these notes is to study and explore it.

The polynomial method has roots in some algorithms about polynomials developed in coding theory in the 80's and 90's. Ideas from these algorithms were then applied to mathematical problems that aren't obviously related to polynomials. Some problems that seemed very hard can now be solved in a couple pages with this new perspective.

The following problem is in the background of the polynomial method. Consider a field  $\mathbb{F}$  and a finite set of points  $S \subset \mathbb{F}^n$ .

Problem: Find a non-zero polynomial P that vanishes on S with degree as small as possible.

For example, consider the points  $(j, 2^j) \in \mathbb{R}^2$  with  $j = 1, ..., 10^6$ . What is the lowest degree of a (non-zero) polynomial that vanishes on all of these points? Let me try to find some polynomials that vanish on these points beginning with simple ones. One polynomial that vanishes on all these points is  $(x-1)...(x-10^6)$ . It has degree  $10^6$ . Another is (y-2)(y-4)... which also has degree  $10^6$ . I can be a little cleverer by choosing a linear polynomial  $L_1$  that vanishes on the first two points, then a second linear polynomial that vanishes on the next two points, etc. The product of these linear factors has degree only 500,000.

We can get a better perspective on the problem by thinking about the general situation of a finite set of points  $x_1, ..., x_s \in \mathbb{F}^n$ . Let V(d) be the vector space of polynomials of degree  $\leq d$  in n variables over  $\mathbb{F}$ . Let E be the evalution map defined by

$$E(P) := (E(x_1), ..., E(x_s)).$$

The map E is linear, and the kernel of E is exactly the set of polynomials of degree  $\leq d$  that vanish on the given points. Our original problem reduces to linear algebra. Using linear algebra, we can draw two important corollaries.

Corollary 0.1. There is a polynomial-time algorithm to find a minimal degree polynomial that vanishes on a given finite set.

(The running time is polynomial in the number of points s, and also in the dimension n. We will usually have a fixed n and consider  $s \to \infty$ .)

**Corollary 0.2.** If dimV(d) > s, then there is a non-zero polynomial P of degree  $\leq d$  that vanishes on the given finite set.

The dimension of V(d) is  $\binom{d+n}{n} \geq d^n/n!$ . For n fixed and d large,  $d^n/n!$  is a good approximation of the dimension. Therefore, we get the following corollary.

Corollary 0.3. For any set of s points in  $\mathbb{F}^n$ , there is a non-zero polynomial that vanishes on the set with degree  $\leq ns^{1/n}$ .

Returning to our example, we see that there is a polynomial vanishing on the million points  $\{(j, 2^j)|j=1,...,10^6\}$  with degree  $\leq 2000$ . This polynomial is much more efficient than the examples I came up with above. It's extremely messy and it would be very difficult to write down explicitly, but for simple abstract reasons we know that it exists.

Here is one moral of this discussion. Suppose that we are trying to find a polynomial with some special properties. One approach is to try to write down the polynomial and find a clever formula. But this discussion gives another approach proving that such a polynomial exists by a dimension-counting argument. Sometimes this approach is more effective than any polynomial that I could craft.

A bare outline of the polynomial method goes as follows.

- (1) Begin with a problem about some points in a vector space.
- (2) Find or consider a polynomial that vanishes at these points with degree as small as possible.
- (3) Use the polynomial to attack the problem.

After this general discussion, let's mention some of the applications of this method. I'm going to mention four applications that we'll study in this course.

#### 1. Algorithms in coding theory

Suppose  $\mathbb{F}$  is a finite field with q elements and  $P: \mathbb{F} \to \mathbb{F}$  is a polynomial of low degree,  $degP \leq q^{1/2}$ . In the coding theory scenario, we could imagine that this polynomial is a piece of data that we want to send over an unreliable channel. In transmission, the data gets corrupted, and the other side receives a function  $F: \mathbb{F} \to \mathbb{F}$ . Let's suppose that a slim majority of the data is correct: in other words F(x) = P(x) for at least (51/100)q values of x. Is it possible to recover P from F? If so, can we do it efficiently?

As long as q is sufficiently large, it is possible to recover P from F in theory because of a fundamental property of polynomials.

**Lemma 1.1.** If  $P : \mathbb{F} \to \mathbb{F}$  has degree  $\leq d$  and vanishes at more than d points, then P is the zero polynomial.

(This simple lemma will have a lot of applications in our course.)

**Corollary 1.2.** If  $q > 10^4$ , for any function  $F : \mathbb{F} \to \mathbb{F}$ , there is at most one polynomial P of degree  $\leq q^{1/2}$  so that F(x) = P(x) for at least (51/100)q values of x.

Proof. Suppose that  $P_1$  and  $P_2$  are such polynomials. Since  $P_1 = F$  51 % of the time and  $P_2 = F$  51 % of the time, it follows that  $P_1(x) = P_2(x)$  for  $\geq (2/100)q$  values of x. So  $P_1 - P_2$  is a polynomial of degree  $\leq q^{1/2}$  with at least (2/100)q zeroes. If q is big enough  $(2/100)q > q^{1/2}$  and so  $P_1 - P_2 = 0$ .

In theory, we can recover P from F by trying all the polynomials of degree  $\leq q^{1/2}$  until we find the one that agrees with F 51 % of the time. But this algorithm is very inefficient. Berlekamp and Welch found an efficient algorithm to recover P from F.

**Theorem 1.3.** (Berlekamp-Welch, 1986) There is a polynomial time algorithm to recover P from F.

Berlekamp and Welch consider the graph of P and the graph of F. The graph of P is a nice algebraic curve in  $\mathbb{F}^2$ . The graph of F contains a lot of points from the graph of P, together with some error points. We are given the graph of F. We don't know which points lie in the graph of P and which are errors. In this cloud of points, we are hoping to find a hidden algebraic structure - the graph of P. The main idea of Berlekamp and Welch is to consider a lowest degree polynomial R(x,y) that vanishes on the graph of F in  $\mathbb{F}^2$ . (In fact, they consider the lowest degree polynomial of the special form  $R(x,y) = R_0(x) + yR_1(x)$ .) As we discussed above, it's possible to find this polynomial R in polynomial time. Then it turns out that the zero set of R is exactly the graph of P together with a vertical line through each error. In other words, for each  $e \in \mathbb{F}$  where  $F(e) \neq P(e)$ , the graph of R contains the line x = e. With the help of R we can immediately tell which values of F agree with P and which were corrupted. After that, it's straightforward to recover P.

## 2. The finite field Nikodym conjecture

The next problem that we consider originates in geometry and analysis.

A set N in the cube  $[0,1]^n \subset \mathbb{R}^n$  is called a Nikodym set if, for each point  $x \in [0,1]^n$ , there is a line L(x) so that

- The point x lies in L(x).
- Except for  $x, L(x) \cap [0,1]^n$  lies in N.

For example, if I remove the line y = 1/2 from the square  $[0, 1]^2$ , the result is a Nikodym set. If I remove a circle, then it isn't. In the 1920's, Nikodym proved the following counterintuitive result:

**Theorem 2.1.** There are Nikodym sets of measure zero in each dimension  $n \geq 2$ .

The sets Nikodym constructed have full Hausdorff dimension, as do all known constructions. This suggests the following conjecture:

Conjecture 2.2. Every Nikodym set  $N \subset [0,1]^n$  has Hausdorff dimension n.

This conjecture turns out to be related to many deep problems in analysis, and it has come to play an important role. (There is also a more famous cousin, the Kakeya conjecture). Although they may look rather arbitrary at first, the Nikodym and Kakeya conjectures underlie a variety of important and natural problems in Fourier analysis, PDE, and number theory. A lot of effort has gone into studying the problem, and we are still far from resolving it. Faced with the difficult problem, mathematicians have looked at cousin problems and toy problems that might give some insight. For example, Tom Wolff formulated a finite field version.

Let  $\mathbb{F}$  be a finite field with q elements. A set  $N \subset \mathbb{F}^n$  is called a Nikodym set if, for each point  $x \in \mathbb{F}^n$ , there is an affine line L(x) so that

- The point x lies in L(x).
- Except for x, the line L(x) lies in N.

The analogue of the Nikodym problem is to ask how many points there must be in a Nikodym set. The finite field Nikodym conjecture says that every Nikodym set must have at least  $c_nq^n$  points. For a while, the two problems seemed about equally hard. About five years ago, Dvir proved the finite field Nikodym conjecture. The proof was only a page long and it shocked a lot of mathematicians in the area. The proof uses the polynomial method, somewhat in the spirit of the Berlekamp-Welch algorithm.

Here is a sketch of the proof. Suppose that N is a small Nikodym set, with only  $(2n)^{-n}q^n$  elements. By dimension counting, we can then find a non-zero polynomial P that vanishes on N with degree at most (q/2). Fix a point  $x \in \mathbb{F}^n$ , and consider the line L(x). By the definition of a Nikodym set, at least q-1 points of L(x) lie in N. Therefore, P must vanish on q-1 points of L(x). Since the degree of P is q-1, P must vanish on the whole line L(x), in particular P(x)=0. Now x was arbitrary so P(x)=0 at every point  $x \in \mathbb{F}^n$ . Given that P vanishes at every point and that the degree of P is q, it's not hard to show that P is the zero polynomial, giving a contradiction.

Filling in all details of the proof takes two more short paragraphs, and we'll do it later. Previously, people tried hard to prove the result without this polynomial trick, and it seems to be extremely difficult. The situation raises a lot of questions. Do polynomials really play such an important role in this problem? If so, why? What does the method have to do with the problem? We'll come back to these kinds of questions a number of times throughout the notes.

People tried to adapt the polynomial method to attack the original Nikodym conjecture, but there are serious difficulties. The polynomial method hasn't yet led

to any significant progress on Nikodym-type problems in Euclidean space. But it has had a lot of success in combinatorial problems involving finitely many lines in Euclidean space.

## 3. The distinct distance problem

The polynomial method has led to solutions for several challenging problems in extremal combinatorics, as well as giving new proofs and perspectives for some important known results. We will study most of these new proofs. The result that we will spend the most time tackling is an estimate for the distinct distance problem in the plane.

Suppose  $P \subset \mathbb{R}^2$  is a finite set with N elements. We let d(P) denote the set of non-zero distances between elements of P:

$$d(P) := \{ |p - q| \}_{p,q \in P, p \neq q}.$$

(We are using the standard Euclidean distance on  $\mathbb{R}^2$ .) Let's consider some examples.

- (1) N generic points in the plane gives  $|d(P)| = {N \choose 2} \sim N^2$ .
- (2) N evenly spaced points along a line gives |d(P)| = N 1.
- (3) N points arranged in a  $\sqrt{N} \times \sqrt{N}$  square grid gives  $|d(P)| \sim N(\log N)^{-1/2}$ .

In the 1940's, Erdős raised the question how small the distance set d(P) could possibly be. He worked out the example of the square grid, and he conjectured that the square grid is minimal up to constant factors: in other words, any set of N points should have  $|d(P)| \geq cN(\log N)^{-1/2}$ . A number of people have proven lower bounds for the distinct distance problem using different techniques. Before the polynomial method, the best lower bound proved that the number of distinct distances is  $\geq N^{.864}$ . The book The Erdős Distance Problem, by Garibaldi, Iosevich, and Singer, describes various approaches to the problem. Using the polynomial method, Nets Katz and I proved the following theorem.

**Theorem 3.1.** (G.-Katz, 2010) For any set of N points in the plane, the number of distinct distances is at least  $cN(\log N)^{-1}$ .

This proof is more difficult than the proof of finite field Kakeya or joints. It will take us 40-60 pages all in all. There is a new ingredient coming from topology and a new ingredient coming from ruled surfaces in algebraic geometry. Nevertheless, the proof is pretty elementary, and I hope it will be accessible to a broad range of readers.

#### 4. Number Theory

The polynomial method is also connected with work in number theory from the early 20th century. In particular, there was an important breakthrough by Thue in the study of diophantine equations. Thue was able to prove that many polynomial equations have only finitely many integer solutions. Here are a couple of examples.

- A. The polynomial  $y^3 2x^3 = 1$  has only finitely many integer solutions.
- B. The polynomial  $y^4+6x^2y^2+7x^3y+101x^4$  has only finitely many integer solutions. These are just special cases of Thue's general theorem.

**Theorem 4.1.** (Thue 1908) If P(x, y) is an irreducible homogeneous polynomial of degree  $\geq 3$ , and A is an integer, then the equation P(x, y) = A has only finitely many integer solutions.

Before Thue, people usually studied single equations or small families of equations. Thue's theorem was much more general. Looking at irreducible polynomials is not that big a restriction, because one can study reducible polynomials by considering the factors. Being homogeneous is a restriction, but Siegel was able to generalize Thue's work to develop a systematic theory of diophantine equations in two variables.

Thue's argument involved some 'auxiliary polynomials'. In order to study a particular diophantine equation, like equation A above, Thue needed an infinite sequence of 'auxiliary polynomials' with special properties. Thue tried to construct these polynomials explicitly. He was able to do it in some examples like equation A, but he couldn't do it for many other equations. Then he realized that the auxiliary polynomials needed to exist for every equation because of a simple counting argument like the one at the beginning of this section. This was probably the most important idea in Thue's breakthrough.

Reviewing Thue's work at the 1974 ICM, Schmidt described it as follows: "The idea of asserting the existence of certain polynomials rather than explicitly constructing them is the essential new idea in Thue's work. As Siegel [1970] points out, a study of Thue's papers reveals that Thue at first tried hard to construct the polynomials explicity (and he could actually do so [for equations of the form  $y^d - Bx^d = A$ ])."

#### 5. Goals of the course

The polynomial method gives several strikingly short applications. The first goal of the course is to study these. I'll emphasize three examples: the Berlekamp-Welch algorithm, the finite field Nikodym and Kakeya problems, and the joints problem.

These short proofs are hard to appreciate without context. The next goal is to learn the context of these results. In particular, we will learn about incidence geometry: combinatorial estimates about how lines and other basic geometric objects intersect each other. The third goal of the course is to prove the estimate about the distinct distance problem.

The fourth goal is to explore connections between the polynomial method and different parts of mathematics. We will see some connections involving computer science, algebraic geometry, topology, harmonic analysis, and number theory.

The fifth goal is to mull over some philosophical questions related to the polynomial method. For example, what is special about polynomials? Why are polynomials involved in these problems?

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## THE BERLEKAMP-WELCH ALGORITHM

Suppose that we have a polynomial P of fairly low degree over a finite field  $\mathbb{F}$ . The data is corrupted, leaving a function  $F: \mathbb{F} \to \mathbb{F}$ , and we know that F(x) = P(x) for a certain fraction of  $x \in \mathbb{F}$ . We want to understand whether we can recover P from F with an efficient algorithm. In particular, our main goal is to explain the Berlekamp-Welch algorithm. We present here the following case of the Berlekamp-Welch result. (We're not trying to be as general as possible, but just to get a flavor of the subject and see the key ideas in the proof.)

**Theorem 0.1.** (Berlekamp-Welch, 1986) Suppose that

- $\mathbb{F}$  has q elements,
- the degree of P is < q/100, and
- F(x) = P(x) for at least (51/100)q values of x.

Under these assumptions, there is an efficient algorithm to recover P from F.

The ideas depend on the following elementary but fundamental vanishing lemma for polynomials.

**Lemma 0.2.** If P(x) is a polynomial of degree  $\leq D$ , and P vanishes at D+1 distinct points, then P is the zero polynomial.

We will recall the proof of this lemma later in the lecture.

One application is that a polynomial P of degree D can be recovered if we know its values at any D+1 points. Let S be a set of D+1 points,  $S = \{x_1, ..., x_{D+1}\} \subset \mathbb{F}$ . Let  $V_1(D)$  be the vector space of polynomials in one variable of degree  $\leq D$ . Consider the evaluation map  $E_S$  which evaluates a given polynomial at the points of S:

$$E_S(P) := (P(x_1), ..., P(x_{D+1})).$$

The evaluation map  $E_S: V_1(D) \to \mathbb{F}^{D+1}$  is a linear map. By the vanishing lemma, the kernel of  $E_S$  is zero. Since the domain and range have the same dimension,  $E_S$  is an isomorphism. Therefore, P can be recovered from its values on the set S. Moreover, recovering P amounts to solving a system of linear equations, so it can be done efficiently.

There are at least (51/100)q points x where F(x) = P(x). If we knew which points they were, we could recover P by this interpolation procedure, because the degree of P is < q/100. The whole point is that we don't know where F is still correct and where F has been corrupted.

#### 1. The algorithm

Now we turn to the algorithm. We will consider the graph of F. To set conventions, the graph of F is the set

$$\{(x,y) \in \mathbb{F}^2 | y = F(x) \}.$$

We are hoping to find some nice algebraic structure hidden in the graph of F. To do so, we will find a low degree polynomial R(x,y) which vanishes on the graph of F. It turns out to be a good idea to consider polynomials of the form  $R(x,y) = R_0(x) + R_1(x)y$ . We may/will talk more about this choice later. Let's define W(d) to be the vector space of polynomials of the form  $R_0(x) + R_1(x)y$  where  $R_0$  and  $R_1$  have degree  $\leq d$ . The dimension of W(d) is 2d + 2. The graph of F has q elements. As long as 2d + 2 > q, there is a non-zero polynomial in W(d) which vanishes on the graph of F. In particular, there is such a polynomial of degree  $d \leq q/2$ . Finding such a polynomial just involves linear algebra, so we can find it in polynomial time. In fact, with a little more work we can find a polynomial that vanishes on the graph of F of minimal degree. Let us define R(x,y) to be a lowest-degree polynomial of the form  $R(x,y) = R_0(x) + R_1(x)y$  that vanishes on the graph of F. We know that the degree of  $R_0$  and  $R_1$  is  $\leq q/2$ .

The key observation in the whole argument is that R also vanishes on the graph of P.

**Claim 1.1.** The polynomial R vanishes on the graph of P. In fact, R(x, P(x)) is the zero polynomial.

*Proof.* We know that R vanishes on the graph of F.

Therefore, R(x, F(x)) = 0 for all x.

Since F(x) = P(x) for most x, we see that R(x, P(x)) = 0 for at least (51/100)q values of x.

Now  $R(x, P(x)) = R_0(x) + R_1(x)P(x)$  is a polynomial in x of degree < q/2 + q/100 = (51/100)q. By the vanishing lemma, this polynomial is identically zero.  $\square$ 

We can now describe how to recover the polynomial P. We just proved that  $R_0(x) + R_1(x)P(x)$  is the zero polynomial. In other words,  $R_1(x)P(x) = -R_0(x)$ . So  $R_0$  is divisible by  $R_1$ , and P is equal to  $-R_1/R_0$ .

This finishes the BW algorithm, but it's interesting to explore a little more about the minimal degree polynomial R(x, y).

We let  $E \subset \mathbb{F}$  be the set  $\{e \in \mathbb{F} | F(x) \neq P(x)\}$ . We call E the set of error locations. It turns out that the zero set of E is exactly the graph of E together with a vertical line  $\{x = e\}$  for each error location E. (Picture?)

Claim 1.2. For each  $e \in E$ , R(x,y) vanishes on the line x = e.

Proof. Fix  $e \in E$ . We consider  $R(e,y) = R_0(e) + R_1(e)y$ . We want to prove that R(e,y) is the zero polynomial in y - in other words that  $R_0(e) = R_1(e) = 0$ . We know that R(e,F(e)) = 0 and R(e,P(e)) = 0. Since  $F(e) \neq P(e)$ , we see that the linear polynomial  $R_0(e) + R_1(e)y$  vanishes at two different values of y. So the linear polynomial must vanish.

In fact, we can say exactly what the minimal degree polynomial R(x, y) is.

Claim 1.3. 
$$R(x,y) = c[y - P(x)] \prod_{e \in E} (x - e)$$
, for some non-zero constant  $c \in \mathbb{F}$ .

From this last claim it follows that R vanishes exactly on the graph of P together with the vertical lines at the error locations. From this information, we can easily identify the set E, giving another way to recover the polynomial P.

The proof of this claim involves a fundamental idea/argument. The argument first appears in the proof of the vanishing lemma, so we begin by giving this proof. Then we develop the idea a bit further to prove a divisibility lemma which leads to the claim.

# 2. Vanishing and divisibility Lemmas

Vanishing lemma. If P(x) is a polynomial of degree  $\leq D$ , and P vanishes at D+1 distinct points, then P is the zero polynomial.

*Proof of the vanishing lemma.* We go by induction on D. The case D=0 is trivial. The heart of the matter is in the following divisibility lemma.

**Lemma 2.1.** If P(x) is any polynomial and  $P(x_1) = 0$  for some  $x_1 \in \mathbb{F}$ , then  $P(x) = (x - x_1)P_1(x)$  for some polynomial  $P_1$ .

*Proof.* Suppose  $P(x) = \sum_{j=0}^{D} a_j x^j$ . We can write any degree D polynomial P in the following form:

$$P(x) = (x - x_1)(b_{D-1}x^{D-1} + \dots + b_0) + r.$$

To see this, first we choose the coefficient  $b_{D-1}$  in order to get the  $x^D$  term correct. None of the lower coefficients influence the  $x^D$  term, so we are still free to choose them. Next, we choose  $b_{D-2}$  to get the  $x^{D-1}$  term correct, etc. We choose  $b_0$  to get the x term correct, and we choose x to get the units term correct.

But now, since  $P(x_1) = 0$ , we must have r = 0, and our factoring is done.

We return to the vanishing lemma. Suppose that P vanishes at  $x_1, ..., x_{D+1}$  distinct points. By the divisibility lemma, we see that  $P(x) = (x - x_1)P_1(x)$ , where  $P_1(x)$  has degree  $\leq D - 1$ . But  $P_1$  must vanish at  $x_2, ..., x_{D+1}$ . By induction,  $P_1 = 0$ , and we are done. This finishes the proof of the vanishing lemma.

With the same proof idea, we can prove a simple divisibility lemma for polynomials in two variables.

**Lemma 2.2.** If R(x, y) is a polynomial of two variables, and P(x) is a polynomial in one variable, and R(x, P(x)) is the zero polynomial, then  $R(x, y) = (y-P(x))R_1(x, y)$  for some polynomial  $R_1$ .

*Proof.* Let  $R(x,y) = \sum_{j=0}^{D} a_j(x)y^j$ , where  $a_j(x)$  is a polynomial in x. Now, we can write any polynomial R(x,y) in the following form:

$$R(x,y) = (y - P(x))(b_{D-1}(x)y^{D-1} + \dots + b_0(x)) + r(x),$$

where the  $b_j(x)$  and r(x) are polynomials in x. The proof is basically the same as above. First we choose the polynomial  $b_{D-1}(x)$  in order to get the  $y^D$  term correct. None of the lower coefficients influence the  $y^D$  term, so we are still free to choose them. Next, we choose  $b_{D-2}$  to get the  $y^{D-1}$  term correct, etc. We choose  $b_0$  to get the y term correct, and we choose r to get the units term correct.

But R(x, P(x)) is r(x), so r(x) is the zero polynomial. This gives the required factoring of R(x, y).

As a corollary, we can quickly prove the last claim about the polynomial R(x,y) in the Berlekamp-Welch algorithm. We know that R(x,P(x)) is the zero polynomial, so  $R(x,y)=(y-P(x))R_1(x,y)$ . Because R(x,y) has degree 1 in y, it follows that  $R_1$  must have degree 0 in y: in other words,  $R_1=R_1(x)$  is a polynomial in x only. So  $R(x,y)=(y-P(x))R_1(x)$ . At each  $e\in E$ , R(x,F(x)) vanishes, but F(x)-P(x) doesn't, and so  $R_1(e)=0$ . Using the divisibility lemma in one variable, we see that  $R(x,y)=(y-P(x))\prod_{e\in E}(x-e)R_2(x)$ . Any polynomial of this form vanishes on the graph of F. Since R is a polynomial of minimal degree, it follows that  $R_2(x)$  is just a constant  $c\neq 0$ .

Our last divisibility lemma is closely related to Bezout's theorem. The formulation of the last lemma depended on the special form of the polynomial y - P(x), but Bezout's theorem says something similar about two arbitrary polynomials. Here is one formulation of Bezout's theorem.

**Theorem 2.3.** Suppose that P(x, y) and Q(x, y) are polynomials. Let Z(P, Q) be the set of common zeroes of P and Q. In other words,

$$Z(P,Q) := \{(x,y) \in \mathbb{F}^2 | P(x,y) = Q(x,y) = 0\}.$$

Then either

- (1) Z(P,Q) has at most (degP)(degQ) points, or
- (2) P and Q have a non-trivial common factor. In other words,  $P = R(x, y)P_1(x, y)$  and  $Q = R(x, y)Q_1(x, y)$  for some polynomial R(x, y) with degree  $\geq 1$ .

This is an important theorem that we will prove and discuss more during the course. With a little extra trick, it recovers the last divisibility theorem as a special case. It's an interesting problem to try to prove the Bezout theorem by generalizing the last proof.

The arguments above are also related to the proof that there is unique factorization in the ring of polynomials  $\mathbb{F}[x_1,...,x_n]$  for any number of variables.

## 3. Correcting polynomials from badly corrupted data

In the Berlekamp-Welch algorithm, we considered corrupted data F which was correct a little more than half the time. If F is correct only half the time, then it's impossible to recover the polynomial P even in theory. For example, start with two low degree polynomials  $P_1$  and  $P_2$ , and arrange for F to agree with  $P_1$  half the time and with  $P_2$  half the time. There is no way to tell if the original polynomial was  $P_1$  or  $P_2$ . Following this observation, it may seem that data F which is correct only 1% of the time would not be very useful. Surprisingly, it turns out that a great deal of information can be recovered from such data. In the mid 90's, Sudan generalized the algorithm of Berlekamp-Welch to deal with highly corrupted data. For example, he proved the following result.

**Theorem 3.1.** (Sudan, 1997) Suppose that  $\mathbb{F}$  is a field with q elements, and that F:  $\mathbb{F} \to \mathbb{F}$  is any function. There is an efficient algorithm that lists all the polynomials of degree  $< (1/200)q^{1/2}$  that agree with F at least 1 % of the time.

We have the tools to follow most of the steps of Sudan's argument. We again consider the graph of F in  $\mathbb{F}^2$ . We find a low-degree polynomial Q(x,y) that vanishes on the graph. This time we consider all the polynomials of two variables. If we let V(d) be the space of polynomials in two variables of degree  $\leq d$ , then the dimension of V(d) is  $\binom{d+2}{2}$ . The graph of F has q elements. As long as  $\binom{d+2}{2} > q$ , we can find a polynomial Q(x,y) of degree  $\leq d$  that vanishes on the graph. So we can find a non-zero Q with degree  $d \leq 2q^{1/2}$ .

Suppose that P has degree  $\leq (1/200)q^{1/2}$ , and that P(x) = F(x) for at least q/100 values of x. We claim that Q(x,P(x)) is the zero polynomial. This follows for the same reason as above. We know that Q(x,F(x)) is zero for every x. So Q(x,P(x)) has at least q/100 zeroes. But Q(x,P(x)) is a polynomial of degree at most  $(degQ)(degP) < 2q^{1/2}(1/200)q^{1/2} = q/100$ . Therefore Q(x,P(x)) is identically zero.

By the divisibility lemma in the last section, we see that y - P(x) divides Q(x, y). There is a polynomial time algorithm that factors Q into irreducible factors. This step is not at all obvious, and it requires different ideas. Now we can recover all the good polynomials P by examining the factors of Q for factors of the form (y - P(x)).

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## THE FINITE-FIELD NIKODYM AND KAKEYA PROBLEMS

These notes are rougher than I would like, but they still have some main proofs. Let F be a finite field with q elements. A set  $N \subset F^n$  is called a (generalized) Nikodym set, if for each point  $x \in F^n$ , there is a line L(x) containing x so that  $|L(x) \cap N| \ge q/2$ . A trivial example of a Nikodym set is the entire set  $F^n$ . Can one find a significantly smaller Nikodym set?

**Theorem 0.1.** (Dvir) Any (generalized) Nikodym set in  $F^n$  contains at least  $c_nq^n$  elements.

Proof. Let V(d) be the vector space of degree d polynomials in n variables with coefficients in F. We pick a polynomial P (not identically zero) that vanishes on N with degree  $\leq C_n |N|^{1/n}$ . If this degree is < q/2, then P must vanish at every point  $x \in F^n$ . But a polynomial of degree  $\leq q/2$  cannot vanish at every point of  $F^n$  unless it vanishes identically. We conclude that the degree of P is at least q/2 and so  $|N| \geq C_n^{-1} (q/2)^n$ .

(We used the following lemma. A polynomial P in n variables over F of degree d < q cannot vanish at every point of  $F^n$  unless each coefficient of P is zero. proof by induction on n. The case n = 1 appears in Lecture 2.

Suppose P vanishes at each point of  $F^n$ . Write  $P(x_1, ..., x_n) = \sum_{j=0}^d P_j(x_1, ..., x_{n-1})x_n^d$ . For each particular choice of  $x_1, ..., x_{n-1}$ , we know that  $P(x_1, ..., x_n) = 0$  for all  $x_n \in F$ . Since d < q, we see that the coefficients  $P_j(x_1, ..., x_{n-1})$  must vanish for each j. Therefore  $P_j(x_1, ..., x_{n-1}) = 0$  for each  $(x_1, ..., x_{n-1}) \in F^{n-1}$ . By induction, we see that the coefficients of  $P_j$  all vanish. But then the coefficients of P all vanish.)

Dvir also proved a small variation which is a tiny bit harder than the proof above. A set  $K \subset F^n$  is called a Kakeya set if it contains a line in every direction. In other words, for every vector  $a \in F^n \setminus \{0\}$ , there is a vector b so that the line  $\{at+b|t \in F\}$  is contained in K. A trivial example of a Kakeya set is the entire vector space  $F^n$ . Can one find a Kakeya set significantly smaller than this?

**Theorem 0.2.** A Kakeya set  $K \subset F^n$  has at least  $c_n q^n$  elements.

*Proof.* Let K be a Kakeya set. If K is smaller than the conclusion, let P be a polynomial vanishing on K of degree q. Let d be the degree of P. Write  $P = P_d + Q$ , where  $P_d$  is the sum of monomials of degree d and Q is a polynomial of degree d = d - 1.

Let a be any non-zero vector. Choose b so that the line  $\{at+b|t\in F\}$  is contained in K. Consider the polynomial in one variable R(t):=P(at+b). The polynomial

R vanishes for each  $t \in F$ . It has degree  $\leq d < q$ , and so its coefficients all vanish. In particular, its coefficient of degree d vanishes. But the coefficient of  $t^d$  in R is exactly  $P_d(a)$ . So we see that  $P_d(a)$  vanishes for all  $a \in F^n \setminus \{0\}$ . But since the degree of  $P_d$  is d < q, it easily follows that  $P_d$  vanishes at 0 also. Then we see that  $P_d$  is identically zero, and we reach a contradiction.

The Kakeya and Nikodym problems presented here are the analogues of deep open problems in Euclidean space. A Kakeya set  $K \subset \mathbb{R}^n$  is a set which contains a unit line segment in each direction. For example, the ball of radius 1/2 is a Kakeya set. Besicovitch constructed surprising examples of Kakeya sets with arbitrarily small volume and even with measure 0. Besicovitch's construction works in each dimension  $n \geq 2$ . Although his sets have measure zero, they all have full Hausdorff dimension. The Kakeya conjecture is that every Kakeya set  $K \subset \mathbb{R}^n$  has Hausdorff dimension n.

It can be hard to appreicate the polynomial method proofs without some background trying to prove this type of result without it. We give two simple combinatorial estimates for the size of a finite field Kakeya set  $K \subset \mathbb{F}_q^n$ .

- 1. (Bush method) By pigeonholing, there is a point  $x \in K$  which lies in at least  $q^n/|K|$  lines of the Kakeya set. The union of all the lines of the Kakeya set thru a given point is called a bush. All of these lines are disjoint except at x. Therefore, the bush contains at least  $q^n(q-1)/|K|$  points. Since the bush is contained in K, we see that  $|K| \ge (1/2)q^{\frac{n+1}{2}}$ .
- 2. ( $L^2$ -method, or just counting) Consider the lines of K one at a time. The first contains q points. The second must contain at least q-1 points not in the first. The third must contain at least q-2 points not in the first two, etc. Therefore, the first q lines must contain at least  $(1/2)q^2$  distinct points. So  $|K| \ge (1/2)q^2$ .

Both these methods only use the fact that two distinct lines intersect in  $\leq 1$  point and that a Kakeya set is the union of  $\geq q^{n-1}$  distinct lines. In other words, we have not used the fact that the lines point in different directions! However, there are  $q^2$  lines in a plane. In order to see that a Kakeya set in  $\mathbb{F}^3$  must contain  $q^{2+\epsilon}$  points, we need to use that the lines point in different directions in order to rule out the example that they all lie in a plane.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## THE JOINTS PROBLEM

Suppose that we have a set of lines in  $\mathbb{R}^3$ . A joint of the set of lines is a point which lies in three non-coplanar lines. The joints problem asks what is the maximal number of joints that can be formed from L lines.

Let's look at some examples.

- 1. A grid. An  $S \times S \times S$  grid of lines contains  $3S^2 = L$  lines and contains  $S^3$  joints. So the number of joints is  $\sim L^{3/2}$ .
- 2a. A tetrahedron. Six lines arranged as the edges of a tetrahedron produce four joints. This example generalizes as follows.
- 2b. Take S planes in  $\mathbb{R}^3$  in general position. Any two of the planes intersect in a line, giving  $L = \binom{S}{2}$  lines. Any three of the planes intersect in a point, and each such point is a joint for this set of lines. Therefore, these lines determine  $\binom{S}{3}$  joints. We again have that the number of joints is  $\sim L^{3/2}$ , but the constant is better than in 1. These are the best known arrangements of lines in the joints problem.

Next we look at upper bounds. Since any two lines intersect in  $\leq 1$  point, there are  $\leq {L \choose 2}$  intersection points, and so  $\leq {L \choose 2}$  joints. A joint involves not just two lines, but three lines. We remark that looking at triple intersections (intersections of three lines) is not very different from just intersections. It's possible to arrange L lines in a plane to give  $\sim L^2$  triple intersections. Start with an evenly spaced grid of vertical and horizontal lines, and then add diagonal lines to make the triple intersections. But this example does not give any joints, because all the lines are coplanar.

The joints problem was posed in the early 90's by B Chazelle, H Edelsbrunner, L.J Guibas, R Pollack, R Seidel, M Sharir, and J Snoeyink, in the paper 'Counting and cutting cycles of lines and rods in space' (Comput. Geom. Theory Appls., 1 (1992), pp. 305323). They proved that the number of joints from L lines is  $\lesssim L^{7/4}$ , and the exponent has gradually improved. We will explain some of the ideas from that first paper later. We mention that it's not easy to prove that the number of joints is  $\lesssim L^{1.99}$ .

With the polynomial method, we now have a rather sharp bound for the joints problem.

**Theorem 0.1.** Any L lines in space determine  $\leq 10L^{3/2}$  joints.

**Main Lemma.** If a set of lines has J joints, then one of the lines contains  $\leq 3J^{1/3}$  joints.

The main lemma implies the theorem by removing the lines one at a time. We start with L lines and J joints. By cutting out one line, we reduce the number of joints by  $\leq 3J^{1/3}$ . We look at the remaining lines L-1 lines, which contain  $\leq J$  joints. One of the lines has  $\leq 3J^{1/3}$  joints on it. Removing this line, we reduce the number of joints by  $\leq 3J^{1/3}$ . We remove all L lines, one at a time. Each time the number of joints decreases by  $\leq 3J^{1/3}$ , and we end up with no joints. Therefore,  $J \leq L(3J^{1/3})$ . Rearranging we get  $J^{2/3} \leq 3L$ , which implies the theorem.

Now we turn to the proof of the main lemma.

*Proof.* Let P be a lowest degree non-zero polynomial that vanishes at every joint. The degree of P is  $\leq 3J^{1/3}$  by dimension counting, as in Lecture 1. If every line has  $> 3J^{1/3}$  joints, then P must vanish on every line.

**Lemma 0.2.** If x is a joint lying in three (non-coplanar) lines, and if a smooth function  $F: \mathbb{R}^3 \to \mathbb{R}$  vanishes on the lines, then  $\nabla F$  vanishes at x.

*Proof.* Let  $v_1, v_2, v_3$  be tangent vectors for the three lines. The directional derivative of F in the direction  $v_i$  must vanish at x. So we have  $\nabla F(x) \cdot v_i = 0$  for each i. Since the  $v_i$  are a basis of  $\mathbb{R}^3$ , we have  $\nabla F(x) = 0$ .

So we see that the derivates of P vanish at each joint. The derivates have smaller degree than P. Since P was a minimal degree non-zero polynomial that vanishes at each joint, the derivatives of P are all the zero polynomial! Then P must be constant, and we get a contradiction.

For example, suppose that we start with an  $A \times B \times C$  grid of lines with A < B < C. The number of lines is AB + AC + BC, and the number of joints is ABC. All of the joints are contained in a union of A parallel planes. Therefore, there is a polynomial of degree A which vanishes on all the joints (the polynomial is a product of linear factors). This polynomial actually has minimal degree: it's an exercise to check that a polynomial of degree  $\leq A - 1$  which vanishes on all the joints of this configuration must be the zero polynomial. The minimal polynomial vanishes on all the lines with B joints and all the lines with C joints, but on none of the lines with A joints. So we see that the minimal polynomial identifies the important and less important lines, and locates at least one inessential line with not too many joints on it.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## WHY POLYNOMIALS? PART 1

The proofs of finite field Kakeya and joints and short and clean, but they also seem strange to me. They seem a little like magic tricks. In particular, what is the role of polynomials in these problems? We will consider this question from several points of view all through the course.

It would be interesting to know how hard it is to prove these results without the polynomial method. If there are other short proofs, it would be great to know about them. Perhaps they are less strange or strange in a different way. If it's really hard to prove these results without the polynomial method, then there should be some reason.

We're going to try to ferret out the role of polynomials by thinking about different cousins of these problems. In this section, we'll meet a key example, consider some mostly open problems, and state a result or two that we'll return to later.

## 1. Arrangements of lines with lots of intersection points

Suppose we have L lines in  $\mathbb{R}^3$ . How many intersection points can there be? There are at most  $\binom{L}{2}$  intersection points, and this can be achieved by putting all the lines in a plane.

What if we don't allow ourselves to put all the lines in a plane? Suppose we have L lines in  $\mathbb{R}^3$  with  $\leq 10$  lines in any plane. How many intersection points can there be? Remarkably, there can still be  $\sim L^2$ .

Our example uses a degree 2 algebraic surface defined by the equation z = xy. This surface contains many lines. For each  $y_0$ , there is a 'horizontal line'  $h(y_0)$  in the surface parametrized by  $\gamma(t) = (t, y_0, y_0 t)$ . And for each  $x_0$ , there is a 'vertical line'  $v(x_0)$  in the surface parametrized by  $\gamma(t) = (x_0, t, x_0 t)$ . Any horizontal line intersects any vertical line:  $h(y_0)$  intersects  $v(x_0)$  at  $(x_0, y_0, x_0 y_0)$ . Taking L/2 horizontal lines and L/2 vertical lines gives  $L^2/4$  intersections. Any plane intersects the surface in a degree 2 curve, and so any plane contains at most 2 of our lines. This surface is an example of a regulus, and we will study them more in later sections.

This is a crucial example in combinatorial problems about intersecting lines. Clever examples don't come only from subspaces and objects of linear algebra - they also come from low degree algebraic surfaces. Enlisting the aid of polynomials can help us to either find or rule out such examples.

Continuing our questions, what if we don't allow ourselves to put all the lines in a degree 2 surface either? Suppose that we have L lines in  $\mathbb{R}^3$  with  $\leq 10$  lines in

any plane or degree 2 algebraic surface. How many intersection points can there be? This is an open question, which looks quite important to me. We do know that there are significantly less than  $L^2$  intersections. The best known estimate is that the number of intersections is  $\leq CL^{3/2}$ , and we will prove it later.

The best example that I know has about 4L intersections. The set of lines in  $\mathbb{R}^3$  is a 4-dimensional manifold. So choosing L lines gives us 4L parameters to play with. If we want one particular line to intersect another, that gives us one equation that our parameters have to satisfy. Just counting parameters, one might guess that it's not hard to find examples with 4L intersections, and that examples with more intersections require some type of "coincidence" or "conspiracy". Given four lines in general position, we will see later that there is a line which meets all four. Using this fact, it's straightforward to give examples with nearly 4L intersections.

## 2. Variations of the joints problem

Last lecture, we proved that L lines in  $\mathbb{R}^3$  determine  $\leq 10L^{3/2}$  joints. Now we will consider various special cases and/or generalizations of this problem, trying to see why the problem is hard without polynomials and what the role of polynomials is.

We begin by recapping the proof. The key step was the following lemma.

**Main Lemma.** If a set of lines has J joints, then one of the lines contains  $\leq 3J^{1/3}$  joints.

The main lemma implies the theorem by removing the lines one at a time. We start with L lines and J joints. By cutting out one line, we reduce the number of joints by  $\leq 3J^{1/3}$ . We look at the remaining lines L-1 lines, which contain  $\leq J$  joints. One of the lines has  $\leq 3J^{1/3}$  joints on it. Removing this line, we reduce the number of joints by  $\leq 3J^{1/3}$ . We remove all L lines, one at a time. Each time the number of joints decreases by  $\leq 3J^{1/3}$ , and we end up with no joints. Therefore,  $J \leq L(3J^{1/3})$ . Rearranging we get  $J^{2/3} \leq 3L$ , which implies the theorem.

An important special case of the joints theorem is the axis-parallel case, when each line is parallel to one of the coordinate axes. This case was studied by Loomis and Whitney in the early 50's, and they proved a sharp estimate for the possible number of joints. We now present a proof of the axis-parallel case more or less following their ideas. It suffices to prove a version of the main lemma for axis parallel lines.

**Lemma 2.1.** Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$ , each parallel to one of the coordinate axes. If  $\mathfrak{L}$  determines J joints, then one of the lines contains  $\leq J^{1/3}$  joints.

*Proof.* Suppose that each line contains  $> J^{1/3}$  joints. Let  $\mathfrak{L}_j \subset \mathfrak{L}$  be the set of lines parallel to the  $x_j$  axis. Start with a line in  $\mathfrak{L}_1$ . It contains  $> J^{1/3}$  joints. Each of these joints lies on a line of  $\mathfrak{L}_2$ , giving  $> J^{1/3}$  disjoint lines of  $\mathfrak{L}_2$ . Each of those lines

contains  $> J^{1/3}$  joints, giving  $> J^{2/3}$  joints all together. These joints all lie in a plane parallel to the  $x_1 - x_2$  plane. Therefore, each of these  $> J^{2/3}$  joints lies on a different line of  $\mathfrak{L}_3$ . So we have  $> J^{2/3}$  disjoint lines of  $\mathfrak{L}_3$ . They each contain  $> J^{1/3}$  joints, for a total of > J joints. This gives a contradiction.

It seems to be difficult to generalize this argument to the joints problem. It even seems difficult to adapt it to a small perturbation of the axis parallel case. Suppose that  $\mathcal{L}_j$  is a disjoint set of lines with angle  $< \alpha$  to the  $x_j$  axis, and let  $\mathcal{L}$  be the union of the  $\mathcal{L}_j$ . Even if  $\alpha$  is small, say  $\alpha = 1/1000$ , it seems hard to adapt the above proof to this case. The problem happens at the italicized word 'different'. If the lines are not quite parallel to the axes, then some of the  $> J^{2/3}$  joints may lie on the same line of  $\mathcal{L}_3$ . The strength of this effect seems hard to bound.

If we begin with axis parallel lines, and tilt them just slightly, than the problem gets a lot harder. For another perspective, we can consider bending the parallel lines slightly, leading to nearly axis parallel curves. Suppose that  $\Gamma_j$  is a (possibly disjoint) set of curves with tangent vectors always maintaining an angle  $< \alpha$  to the  $x_j$ -axis. Let  $\Gamma$  be the union of the  $\Gamma_j$ . Define a joint of  $\Gamma$  to be a point that lies in one curve from each  $\Gamma_j$ . If we have L curves, how many joints can we make? A priori, the answer may depend on both  $\alpha$  and L.

This problem is basically open. For a fixed small  $\alpha$ , say  $\alpha = 1/1000$ , do we get  $\leq CL^{3/2}$  joints? I don't know any examples with more joints. The angle condition guarantees that a curve in  $\Gamma_i$  and a curve in  $\Gamma_j$  intersect in at most 1 point for  $i \neq j$ , and so the number of joints is  $\leq {L \choose 2} \sim L^2$ . Even a bound like  $L^{1.99}$  would be interesting. Also, the bound may depend on  $\alpha$ .

For a simple geometric argument, it may be difficult to distinguish the nearly axis-parallel lines from the nearly axis-parallel curves. It may turn out that nearly axis-parallel curves can have significantly more than  $L^{3/2}$  joints. This would offer an explanation of the use of polynomials in the proof of the joints theorem: polynomials treat straight lines and nearly straight curves very differently. On the other hand, it may turn out that the  $L^{3/2}$  estimate extends to nearly axis-parallel curves, which would give a significant new point-of-view about the joints theorem.

#### 3. Examination of the key facts we used

In the polynomial method, we get a lot of mileage out of two rather simple facts about polynomials.

- (1) In *n*-dimensional space  $\mathbb{F}^n$ , the dimension of the space of polynomials of degree  $\leq d$  is  $\sim d^n/n!$ .
- (2) If a polynomial of degree  $\leq d$  vanishes at d+1 points on a line, then it vanishes on the whole line.

The first bullet says that there are lots of polynomials. This gives us a lot of flexibility to find a polynomial with certain properties. There are lot of ways that polynomials can behave on the whole space  $\mathbb{F}^n$ . The second bullet says that the behavior of a polynomial on a line is comparatively limited. If we restrict the polynomials of degree  $\leq d$  to a line, then we get a vector space of dimension d+1 of possible functions on the line. This dimension is much smaller than the dimension of the space of polynomials of degree  $\leq d$  on all of  $\mathbb{F}^n$ . In summary, polynomials can behave in many ways on the whole space, but in comparatively few ways on a line. The gap between  $d^n/n!$  and d+1 gives us a kind of "leverage". In some sense we would like to make this gap as large as possible.

Let W(d) be a vector space of functions from  $\mathbb{F}^n$  to  $\mathbb{F}$ , for some field  $\mathbb{F}$ . We say that W(d) obeys the degree d vanishing lemma if, for any  $f \in W(d)$ , if f = 0 at d+1 points of a line, then f = 0 at every point on the line.

Question: What is the maximum possible dimension of a vector space of functions from  $\mathbb{F}^n$  to  $\mathbb{F}$  which obeys the degree d vanishing lemma?

Exercise. Using a  $(d+1) \times ... \times (d+1)$  grid of points, prove that the dimension is  $< (d+1)^n$ .

I conjecture that the maximum dimension is achieved by the polynomials of degree  $\leq d$ .

Are there examples of W(d) with dimension  $> d^{1+\epsilon}$  which are not polynomials?

Next one may replace lines by some other subsets of  $\mathbb{F}^n$  and ask again about the dimension of space of functions satisfying the vanishing lemma. Little or nothing is known about this...

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 1 Incidence Geometry

Topic: take a bunch of simple shapes like circles or lines, and study how they can intersect each other.

**Definition 1.1.** If L is a set of |L| lines in  $\mathbb{R}^2$ , let  $P_k(L)$  be the set of points lying in at least k lines, called k-fold intersections; then we can ask what the maximum value of  $P_k(L)$  in terms of k and |L| is.

For example, we can get  $P_k(L) = |L|/k$  trivially by dividing the lines into sets of k and intersecting each set.

In an  $N \times N$  grid of points, let L be the set of lines that contain between R and 2R points. Then there are at most  $\theta(\frac{N^2}{R^2})$  lines of those lines through each point: in any such line, the closest point to x must lie in a square of sidelength  $\frac{2N}{R}$  centered at x. We claim that there are at least  $\theta(\frac{N^2}{R^2})$  of those lines through each point, too: each of the points in the quarter of that square of sidelength  $\frac{2N}{R}$  closest to the center of the grid determines a line that contains at least R points, and by the following lemma, a constant fraction of them are distinct and contain not too many points:

Lemma 1. For all B, there are more than  $\frac{1}{100}B^2$  integer pairs  $(x,y) \in \left[\frac{B}{2}, \frac{B^2}{2}\right]$  with gcd 1

*Proof.* Throw out the  $\frac{1}{4}$  pairs where both are divisible by 2, the  $\frac{1}{9}$  divisible by 3, and so on.  $\frac{1}{4} + \frac{1}{9} + \cdots < \frac{99}{100}$ .

If k is the smallest degree of any grid point, then k is about  $\frac{N^2}{R^2}$ ,  $|P_k| \ge N^2$ , and  $|L| = |P_k|k/R = \frac{N^4}{R^3}$ , so  $|P_k| = |L|^2 k^{-3}$ .

**Proposition 1.2.**  $\forall k \in [\sqrt{|L|}]$ , there's a configuration such that  $|P_k| \geq cL^2K^{-3}$ .

In the early 1980s, it was proven that one of the two bounds above is tight up to a constant factor:

**Theorem 1.3** (Szemerédi, Trotter). For some constant c,  $|P_k| \le c \left(\frac{|L|}{k} + \frac{|L|^2}{k^3}\right)$ .

If  $k > \sqrt{|L|}$ , the first term dominates; if  $k \ge \sqrt{L}$ , the second term dominates.

**Proposition 1.4.** 
$$|P_k| \le \frac{\binom{|L|}{2}}{\binom{K}{2}} \le 2L^2k^{-2}$$

*Proof.* There are  $\binom{L}{2}$  pairs of lines, and  $\forall x \in P_k$ , there are at least  $\binom{k}{2}$  pairs of lines that intersect at x.

**Proposition 1.5.** Prop. If  $\frac{k^2}{4} > |L|$ , then  $|P_K| < \frac{k}{2}$ .

*Proof.* Suppose not. Restrict to a subset P of size  $\frac{k}{2}$ . For all  $x \in P$ , there are at least  $\frac{k}{2}$  lines through x that don't contain any other points of P, so  $|L| \ge |P| \frac{k}{2} = \frac{k^2}{4}$ .

**Proposition 1.6.** If  $|L| < \frac{k^2}{4}$ , then  $|P_k| < 2\frac{|L|}{k}$ .

*Proof.* Suppose not. By the last proposition,  $|P_k| < \frac{k}{2}$ . For all  $x \in P$ , there are at least  $\frac{k}{2}$  lines through x that don't contain any other points of P, so  $|L| \ge |P_k| \frac{k}{2}$ , as desired.

So far, we've only used the fact that two lines intersect in at most one point. But that can't be enough to prove the Szemerédi-Trotter Theorem, because in a finite field  $\mathbb{F}_q^2$ , we could take all the lines: that gives  $|L| = q^2 + q$  and k = q + 1, which violates the Szemerédi-Trotter upper bound. (Note that in that case there's a phase transition around  $k = \sqrt{|L|}$ , from  $|P_k| = \sqrt{|L|}$  to  $|P_k| = |L|$ .)

The extra fact we'll use is some topology, specifically the Euler characteristic. Take a large disc containing all the intersections and let  $V_{int}$  and  $E_{int}$  be the interior vertices and edges; there are also 2|L vertices and 2|L| edges along the boundary of the disc. Every edge is in at most two faces (1 if along the boundary) and every face contains at least three edges, so  $3|F| \leq 2|E_{int}| + 2|L|$ , so  $|E_{int}| \leq 3|V_{int}| + 2|L|$ . Hence  $\sum_{v \in V_{int}} (\frac{1}{2} \deg(v) - 3) \leq 2L$  (in fact, it's at most L). If every intersection had multiplicity at least 3, then  $|P_k| \leq \frac{2L}{K-3}$ ; we need to figure out a stronger argument because intersections might have multiplicity 2.

 $K_5$  isn't planar, since  $10 = |E(K_5)| > 3|V(K_5)| - 6 = 9$ 

## 2 Crossing Numbers of Graphs

If G is a graph, a legal map F into the plane takes vertices to distinct points and edges to curves between their endpoints' points.

The crossing number of F is the number of pairs of edges' curves that intersect, and the crossing number of a graph is the minimum crossing number over legal embeddings. For instance,  $CN(K_5) = 1$ .

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## CROSSING NUMBERS AND THE SZEMERÉDI-TROTTER THEOREM

In this lecture we study the crossing numbers of graphs and apply the results to prove the Szemeredi-Trotter theorem. These ideas follow the paper "Crossing numbers and hard Erds problems in discrete geometry" by László A Székely (Combin. Probab. Comput. 6 (1997), no. 3, 353-358).

## 1. Crossing number estimates

**Proposition 1.1.** If G is a planar graph with E edges and V vertices, then  $E-3V \leq 0$ .

*Proof.* We can reduce to the case that G is connected.

Suppose that G is planar and consider an embedding of G into  $S^2$ . This embedding cuts  $S^2$  into faces, and we get a polyhedral structure on  $S^2$  with V vertices, E edges, and some number F of faces. By the Euler formula, V - E + F = 2. The number of faces cannot easily be read from the graph G, but we can estimate it as follows. Each face has at least three edges in its boundary, whereas each edge borders exactly two faces. Therefore  $F \leq (2/3)E$ . Plugging in we get

$$2 = V - E + F < V - (1/3)E$$
.

Rearranging gives  $E - 3V \le -6$ , and we're done.

Technical details: Why did we assume G connected? Consider a graph homeomorphic to two circles, embedded in  $S^2$  as two concentric circles. This gives three "faces" - two disks and an annulus. The Euler formula is false for this configuration because annular faces are not allowed. In class, we discussed some other configurations that require thought, like a single edge, and a tree. There is an interesting book by Lakatos that describes of difficulty of correctly formulating the hypotheses of the Euler formula.

If E-3V is positive, then we see that G is not planar, and if E-3V is large then we may expect that G has a large crossing number. We prove a simple bound for this now.

**Proposition 1.2.** The crossing number of G is at least E-3V.

*Proof.* Let k(G) be the crossing number of G. Embed G in the plane with k(G) crossings. By removing at most k(G) edges, we get a planar graph G' with E' = E - k edges and  $V' \leq V$  vertices. We see  $0 \geq E' - 3V' \geq E - k - 3V$ .

For perspective, consider the complete graph  $K_n$ . It has n vertices and  $\binom{n}{2}$  edges. For large n, this proposition shows that the crossing number of  $K_n$  is  $\gtrsim n^2$ . On the other hand, the only upper bound we have so far is the trivial bound that the crossing number of  $K_n$  is  $\lesssim n^4$ .

What may we hope to improve in this proposition? When we remove an edge of G, it's in our interest to remove the edge with the most crossings, and when we do this, the crossing number of G can decrease by more than 1. For example, for the complete graph  $K_n$ , it looks plausible that there is always an edge with  $\sim n^2$  crossings. How may we estimate this?

This seems to be a tricky problem, and Székely found a very clever solution. Instead of trying to prove that one edge intersects many other edges, he considered a small random subgraph  $G' \subset G$  and proved that two edges of G' must cross. Since G' is only a small piece of G, it follows that many pairs of edges in G must cross.

**Theorem 1.3.** If G is a graph with E edges and V vertices, and  $E \ge 4V$ , then the crossing number of G is at least  $(1/64)E^3V^{-2}$ .

This theorem was proven by several authors before Székely, but we give his proof. It shows that the crossing number of the complete graph  $K_n$  is  $\gtrsim n^4$  as a special case.

*Proof.* Let p be a number between 0 and 1 which we choose below. Let G' be a random subgraph of G formed by including each vertex of G independently with probability p. We include an edge of G in G' if its endpoints are in G'.

We consider the expected values for the number of vertices and edges in G'. The expected value of V' is pV. The expected value of E' is  $p^2E$ . For every subgraph  $G' \subset G$ , the crossing number of G' is at least E' - 3V'. Therefore, the expected value of the crossing number of G' is at least  $p^2E - 3pV$ .

On the other hand, we give an upper bound on the expected crossing number of G' as follows. Let k = k(G) be the crossing number of G. Let  $F : G \to \mathbb{R}^2$  be a legal embedding with k crossings. We claim that each crossing of F involves two disjoint edges. In other words, two edges that share a vertex don't cross. We come back to the claim at the end. By restricting F to G', we get an embedding of G' with  $p^4k$  crossings on average. This is because each crossing involves four vertices, and it appears as a crossing of F(G') only if all four vertices are included in G'. (If F had a crossing involving two edges containing a common vertex, then it would appear with the much higher probability  $p^3$ .) Therefore, the expected value of the crossing number of G' is at most  $p^4k$ .

Comparing our upper and lower bounds, we see that  $p^4k \ge p^2E - 3pV$ , and so we get the following lower bound for k.

$$k > p^{-2}E - 3p^{-3}V$$
.

We can now choose p to optimize the right-hand side. We choose p = 4V/E, and we have  $p \le 1$  since we assumed  $4V \le E$ . Plugging in we get  $k \ge (1/64)E^3V - 2$ .

To finish the proof, we just have to check the claim that F has no crossings of edges that share a vertex. Given any map with such a crossing, we explain how to modify it to reduce the crossing number. Say that  $F(e_1)$  and  $F(e_2)$  each leave F(v) and cross at x. (If they cross several times, then let x be the last crossing.) We modify F as follows. Suppose that  $F(e_1)$  crosses  $k_1$  other edges on the way from F(v) to x and that  $F(e_2)$  crosses  $k_2$  other edges on the way from F(v) to x. We choose the labelling so that  $k_1 \leq k_2$ . Then we modify F on the edge  $e_2$ , making  $F(e_2)$  follow parallel to  $F(e_1)$  until x and then rejoin its original course at x, so that  $F(e_1)$  and  $F(e_2)$  never cross. This operation reduces the crossing number of x, and so a minimal map F has no such crossings.

## 2. The Szemerédi-Trotter theorem

**Theorem 2.1.** Let  $\mathfrak{L}$  be a set of L lines in the plane. Let  $P_k$  be the set of points that lie on at least k lines of  $\mathfrak{L}$ . Then the number of points in  $P_k$  is at most  $\max(2Lk^{-1}, 2^9L^2k^{-3})$ .

*Proof.* Using the lines and points, we make a graph mapped into the plane. The vertices of our graph G are the points of  $P_k$ . We join two vertices with an edge of G if the two points are two consecutive points of  $P_k$  on a line  $l \in \mathcal{L}$ . This graph is not embedded, but the crossing number of our map is at most  $\binom{L}{2} \leq L^2$ , since each crossing of the graph G must correspond to an intersection of two lines of  $\mathcal{L}$ .

We will count the vertices and edges of the graph G and apply the crossing number theorem. The number of vertices of our graph is  $V = |P_k|$ . The number of edges of our graph is kV - L. (At first sight, each vertex should be adjacent to 2k edges which would give kV edges. But on each line  $l \in \mathfrak{L}$ , the first and last vertices are adjacent to one less edge than this initial count.) As long as  $E \geq 4V$ , we can apply the crossing number theorem and it gives

$$L^2 \ge (1/64)(kV - L)^3 V^{-2}.$$

Either  $V \leq 2L/k$ , or else  $kV - L \geq (1/2)kV$ . In the former case, we are done. In the latter case, we have  $L^2 \geq 2^{-9}k^3V$ , which means  $V \leq 2^9L^2k^{-3}$ .

On the other hand, if E < 4V, we have  $kV - L \le 4V$ , and hence  $V \le \frac{L}{k-4}$ . As long as  $k \ge 8$ , this implies  $V \le 2L/k$ , and we are done. Finally, for k < 8, the trivial bound  $|P_k| \le {L \choose 2}/{k \choose 2} \le 2L^2k^{-2} \le 2^9L^2k^{-3}$ .

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# The distinct distance problem and the unit distance problem

During this lecture, we examine the distinct distance problem and the unit distance problem. We would like to apply the following theorem about crossing numbers, proven last time:

**Theorem 1.** If G is a graph with E edges and V vertices, and  $E \ge 4V$ , then the crossing number K(G) of G is at least  $(1/64)E^3V^{-2}$ .

### 1 Distinct distance problem

Suppose we have a set S of N points in the plane, and amongst them we have t distinct distances, t < N. How small can t be?

Let T be the set of distances that arise between two points. We can draw Nt circles: for each point  $p \in S$  and each distance  $d \in T$ , we draw a circle with center p and radius d. We construct a graph G: the vertices will be the points of S, and the edges will be the arcs of circles between consecutive points. What is the crossing number of the graph? We know that any two circles intersect in at most two points. So we have the inequality  $K(G) \leq 2\binom{Nt}{2} \leq (Nt)^2$ . On the other hand, we know that the graph has N points. Each point is contained in N-1 circles, since all distances that arise between points is contained in T, so each point has degree 2(N-1). So, there are N(N-1) edges. So, we have the following inequality:

$$N^2t^2 \ge K(G) \ge 1/64E^3V^{-2} = 1/64N^3(N-1)^3N^{-2} \ge 1/100N^4$$

This gives  $t \geq 1/10N$ .

This proof, however, is incorrect. When we proved the theorem for crossing numbers, we assumed that the graph was simple, however, the graph can have both multiple edges and loops: If a circle has a single point, that point will have a loop around it, and if there are two points P, Q, and many other points on their perpendicular bisector, then P, Q will have many circles going through them, and if there are no interior points on the arcs, there can be many edges between P and Q.

Could the crossing numbers theorem work for graphs that are not simple? In the proof, we used the fact that  $3F \geq 2E$ . However, this is only true because each face has at least three incident edges. If we allow multiple edges, this is not necessarily the case. So our proof from last time does not work.

In fact, if we have a planar graph, we can take an edge, and draw as many parallel edges as we want, without obtaining any new crossing. So the theorem is false for non-simple graphs, and the proof above in this form fails.

Can we try to obtain some sort of theorem on crossing numbers for graphs with multiple edges? Obviously not for general non-simple graphs, but perhaps with some conditions, we can.

**Definition 1.** We will use the term **multigraph** to refer to a graph that can have multiple edges, but no loops. For a multigraph G, define Mult(G) as the highest number of parallel edges between two points, so  $Mult(G) \leq M$  implies that no two points have more than M edges between them.

**Proposition 1.** If  $Mult(G) \leq M$ , and  $E \geq 4MV$ , then  $K(G) \geq 1/64E^3V^{-2}M^{-3}$ .

*Proof.* Take  $G' \subset G$  to be the graph where we replace any parallel edges by one edge. If this graph has E' edges and V' vertices, then V' = V, and  $E' \geq 1/ME$ . Obviously,  $K(G') \geq K(G)$ , so we have

$$K(G') \ge K(G) \ge 1/64E'^3V'^{-2} \ge 1/64E^3V^{-2}M^{-3}$$

From this, we can deduce the following:

**Theorem 2.** If we have N points in the plane, no 100 of which are on a common line, then the number of distinct distances is at least cN, where c is a constant.

Proof. Take the multigraph that is the graph we defined earlier, with the circles that have only one point on them omitted (since these would be loops). By removing these circles, we removed at most Nt edges, so if  $t \leq N/2$ , then there are still at least  $1/2N^2$  edges. (Otherwise we are done.) Since there are less than 100 points on any line, we can have at most 200 edges between any two points. Thus, using the previous proposition, we obtain the desired result.

## 2 Unit distance problem

Last time, we constructed an example by taking a square  $n \times n$  grid of the right size, a set of N points with U(N) unit distances, where  $\omega(N) \leq U(N) \leq O(N^{1+\epsilon})$  for any epsilon. Using Proposition 1, we can deduce the following theorem:

**Theorem 3.** A set S of N points in the plane determine at most  $U < O(N^{4/3})$  unit distances.

Proof. Draw all the unit circles that have centers in S, and contain at least two points of S, and take the multigraph as before: the points are S, and the edges are arcs along circles. Assume  $U \geq 10N$  (otherwise we are done). If we first draw those unit circles that have at least one point on them, not just those with at least two, then we obtain a graph with at least 2U edges: given a pair of points P, Q that are a unit distance apart, look at the circle with center P. This goes through Q, and we can assign to this unit distance the arc of the circle with center P that is to the left of Q (looking at it from P), and vice versa. Thus, we have two edges for each unit distance. Now, if we delete those circles that have one point on them, we delete at most N circles, so we still have at least U edges. This graph has multiplicity at most 4: given any two points, there can be at most two unit circles that go through both of them, and each unit circle gives us at most two edges between them. Since any two circles intersect in at most two points, we can write  $2N^2 \geq K(G) \geq cE^3V^{-2} \geq c'U^3N^{-2}$ , which gives  $U \leq O(N^{4/3})$  as required.

This result is almost 30 years old, published by Spencer, Szemerédi, and Trotter in 1984. This is the best known upper bound, to this day. One reason it is hard to improve is that it is hard to distinguish unit circles from unit parabolas. In that case, however, we have the following example:

Look at parabolas of the form  $y=x^2+ax+b$ , let a run from 1 to s, let b run from 1 to  $s^2$ . Look at the grid of points in the plane  $[1,2,...,s] \times [1,2,...,3s^2]$ , this gives us  $3s^3$  points. Each of the parabolas defined above has s points on it, since plugging in any value of x from 1 to s gives a value of y from 1 to  $3s^2$ . Thus, this example would give us at least  $s^4=cN^{4/3}$  "unit distances", or incidences between unit parabolas and points.

**Definition 2.** Given a set L of curves in the plane and another set S of points, we define the set of incidences  $I(S, L) = \{(x, l) \in S \times L : x \in l.$ 

If we could obtain a similar example for unit circles, then we could add the set of centers of circles, and obtain a counterexample. In fact, for different norms, we can obtain such a set in a similar way.

### 3 Crossing numbers for multigraphs

Let us return to the distinct distance problem, and the problem of crossing numbers for multigraphs.

What is the crossing number of  $K_5^M$ , that is,  $K_5$  with each edge drawn M times?

We can easily embed it into the plain to get  $M^2$  crossings: embed  $K_5$  such that it has one crossing, and draw each edge M times. Can we do better?

Suppose we have an embedding of  $K_5^M$  with  $K(K_5^M)$  crossings. Take a random subgraph G', where we randomly choose each edge from the M parallel edges. In the induced embedding on the subgraph, each crossing occurs with probability  $1/M^2$ , since it occurs if and only if both edges are in G'. Thus, the expected value of the number of crossings is  $1/M^2K(K_5^M)$ , and so

$$1 \le \mathbb{E}(K(G')) \le K(K_5^M)/M^2$$

We can generalize this idea to obtain the following lemma, that gives a better bound than the proposition from earlier:

**Lemma 1.** Let G be a multigraph with multiplicity at most M. Assume  $E \ge 4MV$ , and each edge has multiplicity greater than M/2. Then  $K(G) \ge 1/256E^3V^{-2}M^{-1}$ .

So we can see that although the constant is a bit worse, we have  $M^{-1}$  instead of  $M^{-3}$ .

*Proof.* Take a random  $G' \subset G$  subgraph, where we randomly choose one edge from each set of parallel edges. Since each set has at least M/2 edges, each crossing remains with probability at most  $M^2/4$ . Since the multiplicity is at most M,  $E' \geq 1/ME \geq 4V$ . Thus, we can write

$$4/M^2K(G) \geq \mathbb{E}(K(G')) \geq 1/64(E')^3V^{-2} \geq E^3V^{-2}M^{-3}$$

Using this lemma, we can prove the following proposition (where we get rid of the lower bound on edge multiplicities):

**Proposition 2.** If G is a multigraph with multiplicity at most M, and  $E \ge 100MV$ , then  $K(G) \ge cE^3V^{-2}M^{-1}$  for some c.

*Proof.* Let  $G' \subset G$  consist of all edges that have multiplicity at least M/2. If  $E' \geq 1/10E \geq 10MV$ , then, using the lemma,

$$K(G) \geq K(G') \geq 1/256E'^3V^{-2}M^{-1}) \geq cE^3V^{-2}M^{-1}$$

If E' < 1/10E, then take  $G_1$  to be the edges not in G, and use induction on  $G_1$ , with M/2 (this contains at least 9/10 of the edges, and the multiplicity is halved, so the  $E \ge 100MV$  condition is satisfied). So we have  $E_1 \ge 9/10E$ , and so

$$K(G) \ge K(G_1) \ge cE_1^3 V^{-2} (M/2)^{-1} \ge (9/10)^3 2cE^3 V^{-2} M^{-1} \ge cE^3 V^{-2} M^{-1}$$

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## CROSSING NUMBERS AND DISTINCT DISTANCES

The Szemerédi-Trotter theorem plays a fundamental role in incidence geometry in the plane. It can be rephrased in several equivalent ways, and it helps to know the different ways. We recall three standard phrasings here.

If  $\mathfrak{S}$  is a set of points and  $\mathfrak{L}$  is a set of lines (or curves), recall that the set of incidences  $I(\mathfrak{S},\mathfrak{L}) = \{(p,l) \in \mathfrak{S} \times \mathfrak{L} | p \in l\}$ . We now give three versions of Szemerédi-Trotter.

**Version 1.** If  $\mathfrak{S}$  is a set of S points in the plane, and  $\mathfrak{L}$  is a set of L lines in the plane, then the number of incidences is bounded as follows:

$$|I(\mathfrak{S}, \mathfrak{L})| \le C(S^{2/3}L^{2/3} + S + L).$$

**Version 2.** Suppose that  $\mathfrak{L}$  is a set of L lines in the plane, and let  $P_k$  be the set of points that lie on  $\geq k$  lines of  $\mathfrak{L}$ .

Then 
$$|P_k| \le C(L^2k^{-3} + Lk^{-1}).$$

**Version 3.** Suppose that  $\mathfrak{S}$  is a set of S points in the plane, and let  $\mathfrak{L}_r$  be the set of lines that contain  $\geq r$  points of  $\mathfrak{S}$ . Then  $|\mathfrak{L}_r| \leq C(S^2r^{-3} + Sr^{-1})$ .

Then 
$$|\mathfrak{L}_r| \leq C(S^2r^{-3} + Sr^{-1})$$

In an earlier lecture, we proved Version 2 using the crossing number theorem. With tiny modifications, the same argument proves any version of the theorem. Also, any version above implies any other version by a short counting argument.

## 1. Distinct distances

**Theorem 1.1.** (Székely) If we have N distinct points in the plane, then they determine  $\geq cN^{4/5}$  distinct distances. In fact, there is one point p in the set so that the distance from p takes  $\geq cN^{4/5}$  distinct values.

*Proof.* Suppose that for each point p in our set  $\mathfrak{S}$ , the set of distances  $\{dist(p,q)\}_{q\in\mathfrak{S}}$ takes on  $\leq t$  different values. We assume  $t \leq cN^{4/5}$  and we will get a contradiction. We can choose Nt circles so that each point of the set lies in N-1 circles. We draw all these circles, leaving out circles with  $\leq 4$  points. We make a multigraph G whose vertices are the points of  $\mathfrak{S}$  and whose edges are arcs between consecutive points on one of the circles.

This multigraph has V = N vertices. It has  $E \ge (1/2)N^2$  edges. (Before removing unpopular circles, it would have  $N^2 - N$  edges. We removed edges that were on the unpopular circles, but these circles contribute a total of  $\leq 4Nt \leq (1/200)N^2$  edges.) It has crossing number  $\leq 2(Nt)^2$ , because a pair circles intersects in  $\leq 2$  points.

The multigraph G may have very high multiplicity. Our strategy will be to estimate how many high-multiplicity edges G can have, and trim edges from G to reduce the multiplicity.

**Lemma 1.2.** The number of edges of G with multiplicity  $\geq M$  is at most  $C[N^2M^{-2}t+N\log Nt]$ .

*Proof.* Consider edges from a vertex  $p_1$  to a vertex  $p_2$ . Each edge is the arc of a circle, and the center of the circle must lie on the perpendicular bisector of  $p_1$  and  $p_2$ . If there are many edges from  $p_1$  to  $p_2$ , then there must be many points of our set along the perpendicular bisector.

We define a map from edges of our multigraph to lines, sending an edge to the corresponding perpendicular bisector. A line containing A points of  $\mathfrak{S}$  contributes  $\leq 2At$  edges of the multigraph, each with multiplicity  $\leq A$ .

Let  $\mathfrak{L}_j$  denote the set of lines in the plane which contain  $\sim 2^j$  points of  $\mathfrak{S}$ . (More precisely, the number of points is greater than  $2^{j-1}$  and at least  $2^j$ .) The number of edges with multiplicity at least M is bounded by

$$\sum_{2^{j}>M} |\mathfrak{L}_{j}| 2 \cdot 2^{j} t.$$

The size of  $\mathcal{L}_j$  is bounded by the Szemerédi-Trotter theorem (see Version 3 above). Plugging in, we get:

$$\leq \sum_{2^{j} > M} C(N^{2}2^{-3j} + N2^{-j})2^{j}t.$$

The  $N^2 2^{-3j}$  term decays exponentially in j, and the total is  $\leq CN^2M^{-2}t$ . The second term is independent of j, and we need to sum over  $\sim \log N$  values of j, so the total is  $\leq CN \log Nt$ .

We choose  $M=\alpha t^{1/2}$  for a large constant  $\alpha$ . By choosing  $\alpha$  large enough, we can arrange that the number of edges of multiplicity  $\geq M$  is at most  $(1/10)N^2$ . We let  $G'\subset G$  be the multigraph given by deleting all edges of G with multiplicity  $\geq M$ . The graph G' still has  $\geq (1/3)N^2$  edges, and it now has multiplicity at most  $M \leq t^{1/2}$ .

Now we apply the crossing number theorem for multigraphs. We recall the statement from last lecture.

**Theorem 1.3.** (Crossing number estimate for multigraphs) If G is a multigraph with V vertices and E edges and with multiplicity  $\leq M$ , and if  $E \geq 100MV$ , then the crossing number of G is at least  $cE^3V^{-2}M^{-1}$ .

Our graph G' has crossing number at most  $\sim N^2 t^2$ . But by the theorem above, we have

$$N^2 t^2 \gtrsim k(G') \gtrsim E^3 V^{-2} M^{-1} \sim N^6 N^{-2} t^{-1/2}.$$

Rearranging gives  $t^{5/2} \gtrsim N^2$  and so  $t \gtrsim N^{4/5}$  as desired.

Building on the crossing number approach introduced by Székely, Solymosi-Toth and then Katz-Tardos improved the estimates in the distinct distance problem. Katz-Tardos proved that for any N points in the plane, one of the points determines  $\geq cN^{.864}$  distances with the other points. This approach gave the best estimate in the distinct distance problem before the polynomial method approach.

Using the polynomial method we will prove that the number of distinct distances given by N points is  $\geq cN(\log N)^{-1}$ . However, this approach does not bound the number of distances from a single point. It looks completely plausible that for any N points in the plane, one of the points determines  $\geq cN(\log N)^{-1}$  (or even  $\geq cN(\log N)^{-1/2}$ )) distances with the other points. This would be a better theorem if it's true.

## 2. What about three dimensions?

In the last few sections, we have had a brief but substantial introduction to incidence geometry in two dimensions. What happens in three dimensions? We will brainstorm some questions below. Three dimensions are more complicated, there are more questions, and it's less clear which are the fundamental questions.

**Question 1.** Given S points and L lines in  $\mathbb{R}^3$ , what is the maximum possible number of incidences?

It turns out that this question is equivalent to the corresponding question in  $\mathbb{R}^2$ . Since  $\mathbb{R}^2 \subset \mathbb{R}^3$ , the maximum must be at least as big in two dimensions. But given an arrangement of points and lines in  $\mathbb{R}^3$ , we can project to a generic plane. The projection gives S distinct points and L distinct lines in the plane, and it has at least as many incidences. To try to make the question more interesting, we may bound the number of points or lines in a plane. For example, we may consider the following question.

**Question 2.** Given S points and L lines in  $\mathbb{R}^3$ , with  $\leq B$  lines in any plane, what is the maximum possible number of incidences?

Besides points and lines,  $\mathbb{R}^3$  also contains planes. We can try to make similar incidence questions also using planes.

**Question 3.** Given S points and P planes in  $\mathbb{R}^3$ , what is the maximum possible number of incidences?

This question has a simple answer. Take all P planes containing a line l, and all S points in l. Then the number of incidences is SP, which is the maximum possible. To try to make the question more interesting, we may rule out this example by bounding the number of planes containing any line.

**Question 4.** Given S points and P planes in  $\mathbb{R}^3$ , with the restriction that any line lies in  $\leq B$  of the planes, what is the maximum possible number of incidences?

(I don't know the answer to this question... it may be open.) We can combine lines and planes.

**Question 5.** Given L lines and P planes in  $\mathbb{R}^3$ , what is the maximum possible number of pairs  $(l, \pi)$  where the line l is contained in the plane  $\pi$ ?

By duality, this question is equivalent to question 1, and so it is answered by the Szemerédi-Trotter theorem (up to a constant factor).

We may then combine points, lines, and planes:

**Question 6.** Given S points, L lines, and P planes in  $\mathbb{R}^3$ , what is the maximum possible number of triples  $(p, l, \pi)$  with the point p in the line l in the plane  $\pi$ ?

(I don't know the answer to this question... it may be open.)

We will come back to question 2 later on, using the polynomial method. The Szemerédi-Trotter theorem plays a central and fundamental role in two dimensions. There may not be any one result in three dimensions which is so central. And there are definitely many more questions besides the ones listed here.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## REGULI AND APPLICATIONS, ZARANKIEWICZ PROBLEM

One of our long-term goals is to pursue some questions of incidence geometry in  $\mathbb{R}^3$ . We recall one question to direct our focus during this lecture.

**Question 1.** If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$ , and if at most 10 (or at most B) lines lie in a plane or degree 2 surface, what is the maximum possible number of intersection points of  $\mathfrak{L}$ ?

Now we introduce an important tool for incidence geometry in three dimensions.

## 1. Reguli

It is a classical fact that any three lines in  $\mathbb{R}^3$  lie in the zero set of a degree 2 polynomial. This fact can be used to prove estimates in incidence geometry in three dimensions.

**Proposition 1.1.** For any three lines  $l_1, l_2, l_3$  in  $\mathbb{R}^3$ , there is a non-zero degree 2 polynomial Q that vanishes on all three lines.

*Proof.* We will prove this result by counting dimensions. We can think of the argument as an example of the polynomial method.

Let V(2) be the space of polynomials of degree  $\leq 2$  in three variables. The space V(2) is a vector space of dimension 10. (A basis is given by  $x^2, xy, xz, y^2, yz, z^2, x, y, z, 1$ .)

Choose three points on each line. Let  $p_{i,j}$  be three distinct points on  $l_i$ . By linear algebra, we can find a non-zero degree 2 polynomial Q that vanishes at all the points  $p_{i,j}$ . Since Q has degree 2 and vanishes at three distinct points of  $l_i$ , it must vanish on all of  $l_i$ . So Q vanishes on all three lines as desired.

This proposition allows us get good information about the lines that intersect all three lines  $l_1, l_2$ , and  $l_3$ . Exactly what happens depends a little on the properties of  $l_1, l_2$ , and  $l_3$ . Recall that two lines in  $\mathbb{R}^3$  are skew if they don't intersect and they're not parallel. The most important case concerns three skew lines.

**Proposition 1.2.** If  $l_1$ ,  $l_2$ , and  $l_3$  are pairwise skew, then there is an irreducible degree 2 algebraic surface  $R(l_1, l_2, l_3)$  which contains every line that intersects  $l_1$ ,  $l_2$ , and  $l_3$ .

*Proof.* By the last proposition, there is a non-zero degree 2 polynomial Q that vanishes on  $l_1$ ,  $l_2$ , and  $l_3$ . Let  $R(l_1, l_2, l_3)$  be the zero set of Q. Suppose that l intersects  $l_1$ ,  $l_2$ , and  $l_3$ . Since  $l_1$ ,  $l_2$ , and  $l_3$  are disjoint, the line l must intersect R in three distinct points. But then Q vanishes identically on l, and l is contained in R.

Finally, if Q was reducible, then it would be a product of linear factors, and R would be a union of two planes. But since the lines  $l_1, l_2$ , and  $l_3$  are skew, no two of them lie in a plane, and so R cannot be a union of two planes. Also, if Q had degree 1, then R would be a plane, and this cannot happen either.

The surface  $R(l_1, l_2, l_3)$  is called a regulus. Reguli have played an important role in incidence geometry for a long time... including the first work on the joints problem in the paper "Counting and cutting cycles of lines and rods in space", by Chazelle, Edelsbrunner, Guibas, Pollack, Seidel, Sharir, and Snoeyink (Computational Geometry, Theory and Applications 1 (1992) 305-323).

To complement this proposition, we record a couple of trivial lemmas which deal with the case when two lines are not skew.

**Lemma 1.3.** Suppose that  $l_1$  and  $l_2$  are lines in  $\mathbb{R}^3$  that intersect at a point p. Suppose that P is the plane that contains  $l_1$  and  $l_2$ . Then any line which intersects both  $l_1$  and  $l_2$  either contains p or lies in P.

**Lemma 1.4.** Suppose that  $l_1$  and  $l_2$  are parallel. Let P be the plane that contains them. Then any line which intersects both  $l_1$  and  $l_2$  lies in P.

Chazelle et al applied these results to 3d incidence geometry. For example, they proved that the number of joints determined by L lines is  $\lesssim L^{7/4}$ . We will use their method to work on Question 1.

**Theorem 1.5.** Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq 10$  lines in any plane or degree 2 surface. Then the number of intersection points of  $\mathfrak{L}$  is  $\lesssim L^{5/3}$ .

*Proof.* We will work with the intersection matrix of a set of lines  $\mathfrak{L}$ . Let us record which pairs of lines intersect. We make an  $L \times L$  matrix A whose entries are 0 or 1, where the entry  $a_{ij}$  is 1 if and only if  $l_i$  and  $l_j$  intersect. (Convention for the diagonal: all zeroes.)

We write |A| to mean the number of 1's in the matrix A. If every intersection point was a simple intersection of two lines, then the number of intersection points would be (1/2)|A|. Some intersection points have multiplicity 2, others may have very high multiplicity, and we want to keep track of them separately. We let  $A_t$  be the matrix with a 1 in the (i,j)-entry if  $l_i$  and  $l_j$  intersect at a point lying in  $\sim 2^t$  lines of  $\mathfrak{L}$ . (More precisely,  $\sim 2^t$  means more than  $2^{t-1}$  but at most  $2^t$ .) The number of points with intersection multiplicity  $\sim 2^t$  is  $\sim |A_t|2^{-2t}$ . Therefore, the number of intersection points is

$$\sim \sum_{t} |A_t| 2^{-2t}.$$

Our next goal is to estimate  $|A_t|$ .

**Lemma 1.6.** Suppose that  $\mathfrak{L}$  has  $\leq 10$  lines in any plane or degree 2 surface. Then  $A_t$  has no  $3 \times 20 \cdot 2^t$  minor of all 1's.

Proof. Suppose that  $A_t$  has a  $3 \times 20 \cdot 2^t$  minor of all 1's. Let the three rows by labelled by  $l_1, l_2, l_3$ . If  $l_1, l_2, l_3$  are all skew, then the  $\geq 20$  column lines all lie in the degree 2 surface  $R(l_1, l_2, l_3)$ , which is impossible. Suppose that  $l_1, l_2, l_3$  are not all skew. After relabelling, we can assume that  $l_1$  and  $l_2$  are not skew. If  $l_1$  and  $l_2$  interesect in a point p and lie in a plane P, then we either get  $5 \cdot 2^t$  column lines containing p or  $5 \cdot 2^t$  column lines lying in P. There can't be that many lines in a plane. Also, by the definition of  $A_t$ , there should only be  $\leq 2^t$  lines of  $\mathfrak{L}$  containing p. Finally, if  $l_1$  and  $l_2$  are parallel lines in the plane P, then we get  $10 \cdot 2^t$  column lines in the plane

Knowing that the matrix  $A_t$  does not have any  $3 \times 20 \cdot 2^t$  minors of all 1's controls the number of 1's in the matrix by the following classical theorem. It touches on an important area of combinatorics with many open questions.

**Theorem 1.7.** (Kővári-Sós-Turán, 1954) Suppose that A is an  $L \times L$  matrix whose entries are 0 or 1. Suppose that A has no  $V \times W$  minor of all 1's, for some integers  $V \leq W$ . Then the number of 1's in A is at most  $C(V)W^{1/V}L^{\frac{2V-1}{V}}$ .

We give the proof and discuss the problem more generally below. So we see  $|A_t| \lesssim 2^{t/3} L^{5/3}$ .

$$\sum_{t} |A_{t}| 2^{-2t} \lesssim L^{5/3} \sum_{t} 2^{-(5/3)t} \lesssim L^{5/3}.$$

Using the polynomial method, we will eventually improve this bound to  $L^{3/2}$ .

## 2. The Zarankiewicz problem

In the early 1950's, Zarankiewicz posed the following problem. Suppose that A is an  $M \times N$  matrix with entries 0 or 1, and suppose that A has no  $V \times W$  minor of all 1's. What is the maximum possible number of 1's that we can have in A? We considered the problem above for square matrices M = N = L.

**Theorem 2.1.** (Kővári-Sós-Turán, 1954) Suppose that A is an  $M \times N$  matrix whose entries are 0 or 1. Suppose that A has no  $V \times W$  minor of all 1's, for some integers  $V \leq W$ . Then the number of 1's in A is at most  $C(V)W^{1/V}MN^{\frac{V-1}{V}}$ .

*Proof.* Let  $C_1, ..., C_N$  denote the columns of A. We can think of each column as a subset of the numbers [1, ..., M]. We let  $\binom{M}{V}$  denote all of the sets of V distinct elements of the numbers 1, ..., M. We let  $\binom{C_j}{V}$  denote all of the sets of V distinct

elements of  $C_j$ . Clearly  $\binom{C_j}{V} \subset \binom{M}{V}$ . We let  $|C_j|$  be the number of elements in  $C_j$ , so that the number of elements in  $\binom{C_j}{V}$  is  $\binom{|C_j|}{V}$ .

The condition that A has no  $V \times W$  minor of all 1's implies that each element of  $\binom{M}{V}$  occurs in  $\langle W \rangle$  of the sets  $\binom{C_j}{V}$ . So we get the following inequality:

$$\sum_{j=1}^{N} \binom{|C_j|}{V} < W \binom{M}{V}.$$

We write  $A \lesssim B$  for  $A \leq C(V)B$ . Up to constant C(V), the left-hand side is roughly  $\sum |C_j|^V$ , and so

$$\sum_{j=1}^{N} |C_j|^V \lesssim WM^v.$$

The total number of 1's in A is  $\sum_{j} |C_{j}|$ . Now by Holder's inequality,

$$\sum_{j=1}^{N} |C_j| \le (\sum_{j=1}^{N} |C_j|^V)^{1/V} N^{\frac{V-1}{V}} \lesssim (WM^V)^{1/V} N^{\frac{V-1}{V}} = W^{1/V} M N^{\frac{V-1}{V}}.$$

The Zarankiewicz problem has been in the background of many questions in incidence geometry. For example, suppose that we have S points and L lines in the plane. We can form the incidence matrix, an  $S \times L$  matrix. Each row corresponds to a point, each column corresponds to a line, and there is a 1 if the point lies on the line. This matrix has no  $2 \times 2$  submatrix of all 1's, because two lines intersect in only one point. Therefore, the number of incidences is  $\lesssim SL^{1/2}$ . (The situation is symmetric, so the number of incidences is also  $\lesssim S^{1/2}L$ .) These bounds are equivalent to the first bounds we proved about incidence geometry of points and lines in the plane.

We can do other examples with unit circles and/or circles. For instance, consider the unit distance problem. We have N points in the plane. Form an  $N \times N$  0/1 matrix with a 1 whenever the distance between the corresponding points is 1. We can think of this as an incidence matrix. The rows correspond to points, and the columns correspond to unit circles centered at the points, and an entry is 1 if the point corresponding to the row lies on the unit circle corresponding to the column. Two unit circles intersect in at most 2 points, and so this matrix has no  $3 \times 2$  minor of all 1's. Therefore, the number of unit distances is  $\lesssim N^{3/2}$ .

It's a very interesting question how sharp the Kővári-Sós-Turán theorem is. After a couple of examples, we come to deep open problems.

Example 1. Consider an  $N \times N$  0-1 matrix with no  $2 \times 2$  submatrix. The KST theorem says that the matrix has  $\lesssim N^{3/2}$  1's. This estimate is sharp. The example was discovered by Reiman in 1958 ("Uber ein Problem von K. Zarankiewicz", Acta Mathematica Hungarica 9 (34): 269-273.) We have essentially already seen the example: it is the incidence matrix of lines over a finite field. We pick  $N=q^2$  lines in the plane  $\mathbb{F}_q^2$ . We let the rows of our matrix correspond to the points of  $\mathbb{F}_q^2$  and the columns correspond to the  $q^2$  chosen lines. We put a 1 in the matrix if the point corresponding to the row lies in the line corresponding to the column. Since two lines intersect in at most 1 point, there are no  $2 \times 2$  submatrices. Since each line contains q points, our matrix has  $q^3 = N^{3/2}$  1's. Working with the projective plane over  $\mathbb{F}_q$  is even slightly better.

Example 2. Next consider an  $N \times N$  0-1 matrix with no  $3 \times 3$  submatrix. The KST theorem says that the matrix has  $\lesssim N^{5/3}$  1's. This example was found by Brown in the early 60's. It involves a clever construction with some low-degree polynomials over finite fields. We will do it on the homework.

This example is clever and special, and it seems very hard to generalize it to  $4 \times 4$  minors. Consider an  $N \times N$  0-1 matrix with no  $4 \times 4$  submatrix. The KST theorem says that the matrix has  $\lesssim N^{7/4}$  1's. But the best examples have only  $\sim N^{5/3}$  1's and these are basically Brown's examples which have no  $3 \times 3$  minor of all 1's! It's a longstanding open problem in combinatorics where the truth lies between Brown's example and the KST upper bound.

Example 3. Finally, consider an  $N \times N$  0-1 matrix with no  $V \times V$  submatrix. The KST theorem says that the number of 1's is  $\leq C(V)N^{2-(1/V)}$ . For large V, the best examples come from a random construction. On the homework, you will use the technique to prove that there are examples with  $\sim N^{2-\frac{2}{V+1}}$  1's. For  $V \geq 5$ , I believe these are the largest known examples.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.S997 Notes

## The Elekes-Sharir Approach to the Distinct Distance Problem

Today's the last background lecture in incidence geometry. We'll discuss one of the latest methods to approaching the distinct distance problem, which has a cool connection to incidence geometry.

Before going into that, let's review how we were thinking about the distinct distance problem. Suppose we have N points and  $t \ll N$  distances. Draw tN circles around each point, and consider the circles as arcs. We tried this approach before, but never used the fact that the radii at each of the points must be the same.

We make some new definitions to take advantage of that. Let  $P \subset \mathbb{R}^2$  be the set of points and d(P) the set of nonzero distances. Let  $Q(P) = \{(p_1, q_1, p_2, q_2) \in P^4 : |p_1 - q_1| = |p_2 - q_2| \neq 0\}$ . We'd expect |Q(P)| to be large.

**Lemma 1.** 
$$|d(P)| |Q(P)| \ge (N^2 - N)^2 \ge N^4$$
.

Proof. Let  $d(P) = \{d_1, \ldots, d_s\}$  where s = |d(P)|. We can just count  $n_j = \{(p,q) \in p^2 : |p-q| = d_j\}$  and  $\sum_j n_j = N^2 - N$ . If we pick the distance first and then choose two pairs equalling that distance, we get  $|Q(P)| = \sum_j n_j^2$ . Then we just use Cauchy-Schwarz:  $N^2 - N = \sum_{j=1}^s n_j \cdot 1 \le \left(\sum n_j^2\right)^{1/2} s^{1/2} = |Q(P)|^{1/2} |d(P)|^{1/2}$ , as desired.

This is not at all surprising: If there are few distances, then there should be a lot of quadruples. So we'd also like to count these quadruples in another way, and figuring out a way to do this was their key insight. Let G be the group of orientation-preserving rigid motions of the plane.

**Lemma 2.** 
$$|p_1 - q_1| = |p_2 - q_2| \neq 0$$
 iff  $\exists ! g \in G$  with  $g(p_1) = p_2$  and  $g(q_1) = q_2$ .

That got people thinking about which rigid motions take  $p_1$  to  $p_2$ . Let  $S_{p_1,p_2} = \{g \in G : g(p_1) = p_2\}$ . This is a 1-dimensional curve in G, which is a 3-dimensional Lie group.

**Lemma 3.** Assume 
$$p_1 \neq q_1$$
. Then  $|p_1 - q_1| = |p_2 - q_2|$  iff  $|S_{p_1,p_2} \cap S_{q_1,q_2}| = 1$ , and  $|p_1 - q_1| \neq |p_2 - q_2|$  iff  $|S_{p_1,p_2} \cap S_{q_1,q_2}| = 0$ .

So we can look at the incidence geometry of these curves in G. If a point lies on two curves, it corresponds to two quadruples, and if a point lies on three curves, it corresponds to six quadruples. Let  $G_{=k} := \{g \in G : g \text{ lies in exactly } k \text{ curves of } S\}$ .

Let  $E: Q(P) \to g$  be given by Lemma 3. Then the image of E is contained in  $\bigcup_{k\geq 2} G_{=k}$ . We have  $E^{-1}(g) = 2\binom{k}{2}$ , since we can take the quadruples in either order. Therefore, we have

**Lemma 4.** 
$$|Q(P)| = \sum_{k=2}^{N} |G_{=k}| \, 2\binom{k}{2}$$
.

We usually calculated things with  $G_k = \{g \in G : g \text{ lies in } \geq k \text{ curves}\}$ . So writing in terms of these, we have

**Lemma 5.** 
$$Q(P) \sim \sum_{k=2}^{N} |G_k| k$$
.

*Proof.* We have

$$|Q(P)| = |G_{=k}| 2 \binom{k}{2}$$

$$= \sum_{k=2}^{N} [|G_k| - |G_{k+1}|](k^2 - k)$$

$$= \sum_{l} |G_l| [(l^2 - l) - ((l - 1)^2 - (l - 1))]$$

$$\sim \sum_{l} l |G_l|.$$

We also have this other characterization of  $G_k$ :

**Lemma 6.**  $G_k = \{g \in G : |gP \cap P| \ge k\}.$ 

This is sort of a generalization of symmetries, where we'd require qP = P. So we can think of these as partial symmetries.

Example. Suppose our set of points is an  $s \times s$  square grid with  $N = s^2$ . Then  $|G_{s^2}| = 4$ . What about things like  $\left|G_{\frac{1}{10}s^2}\right|$ ? Well, it takes a while to explain, but  $\left|G_k\right| \sim N^3 k^{-2}$  for all  $2 \le k \le \frac{1}{10}N$ .

That this is the best you can do was a conjecture:

Conjecture (ES1). If  $P \subset \mathbb{R}^2$  with |P| = N and 2 < k < n, then  $|G_k| \leq N^3 k^{-2}$ .

This has since been proven, and we'll prove it in this class using the polynomial method. Let's see the consequences.  $|Q(P)| \leq \frac{N}{k=2} |G_k| k \lesssim \frac{N}{k=2} N^3 k^{-1} \lesssim N^3 \log N$ . Then  $|d(P)| \gtrsim N^3/|Q(P)| \gtrsim N/\log N$ . We'll prove this whole chain of implications using the polynomial method. We see that we've claimed that the conjecture itself is sharp for the square grid, so we know that the square grid indeed does have that many quadruples. But we could have lost some at the last step because we used Cauchy-Schwarz, and indeed, we checked earlier that there are  $N/\sqrt{\log N}$  distinct distances in the large square grid.

Let's get a better feel for these rigid motions. We first have the translations T, which are congruent to the plane  $\mathbb{R}^2$ .

**Lemma 7.**  $|T \cap G_k| \lesssim N^3 k^{-2}$ .

Proof. Consider the number of translation quadruples  $Q_T \subset Q(P) = \{(p_1,q_1,p_2,q_2) \in P^4 \text{ such that } p_1 - q_1 = p_2 - q_2 = 0\}$ . Then  $\#Q_T \leq N^3$  because  $\forall p_1,q_1,p_2$ , there is at most one choice of  $p_2$ . Then define  $E:Q_T \to T$  similar to before, and if  $g \in G_k$ ,  $\left|E^{-1}(g)\right| \sim k^2$ . So  $|Q_T| \geq |G_k \cap T| \cdot 2^{-k}_2$ , and we're done.

Now we'd like to "straighten" G' := G/T. There's a way to do this to make it correspond to the incidence geometry of points and lines. G' is a rotation around a fixed point  $(x,y) \in \mathbb{R}^2$  by angle  $\theta \in (0,2\pi)$ . Then we define  $\rho: G \to \mathbb{R}^3$  by  $\rho(x, y, \theta) = (x, y, \cot \theta/2)$ .

**Proposition.**  $\rho(S_{pq} \cap G')$  is a line  $\ell_{pq}$ .

*Proof.* Indeed, if we rotate from p to q, the point of rotation must be on the perpendicular bisector of p and q. It's just trigonometry from here. 

In fact, we have the following:

**Proposition.** Let  $v = \frac{p_2 - q_2}{2}, \frac{q_1 - p_1}{2}$  be a vector perpendicular to p - q with length  $\frac{1}{2} |p - q|$  and  $a = \frac{p + q}{2}$ . Then  $\rho(S_{pq} \cap G')$  is a line parameterized by  $\ell_{pq} : t \mapsto (a + tv, t)$ .

Let  $\mathcal{L} = \{\ell_{pq}\}_{p,q \in P}$ ,  $N^2$  lines. Then  $|G'_k|$  is the number of points in  $\geq k$  lines of  $\mathcal{L}$ . Remember that the incidence geometry depended on whether they were all in the plane.

**Lemma 8.** If q = r then  $\ell_{pq}$  and  $\ell_{qr}$  are skew.

*Proof.*  $S_{pq} = \{g \in G : g(p) = q\}$ , so  $S_{pq} \cap S_{pr} = \emptyset$ . This shows that  $\ell_{pq} \cap \ell_{pr} = \emptyset$ , so we also have to show they aren't parallel. The "slope" ((dx/dz, dy/dz)) of  $\ell_{pq}$  is v(p,q) and these slopes are different.  $\square$ 

We also realized that there was a problem if too many lines lay in some regulus. We won't prove this in class today but defer this proof to a while later, but there are  $\leq N$  lines of  $\mathcal{L}$  in any degree 2 surface.

Conjecture (ES2A). If  $\mathcal{L}$  is a set of L lines with at most  $L^{1/2}$  in any plane or degree 2 surface, then  $|P_2| \lesssim L^{3/2}$ .

Conjecture (ES2B). If  $\mathcal{L}$  is a set of L lines with at most  $L^{1/2}$  in any plane and  $3 \leq k \leq L^{1/2}$ , then  $|P_k| \lesssim L^{3/2}k^{-2}$ .

Finally, we saw another log-log graph of the bounds we had. We had the S-T bound for any L lines that was piecewise linear with two regions, from 2 to  $L^{1/2}$  and  $L^{1/2}$  to L. Then if we assume the number of lines in any plane or degree 2 surface is small, then we lower the first line.

This finishes our background on incidence geometry. In the next session, we'll pick up with the polynomial method.

---

#### ALGEBRAIC STRUCTURE AND DEGREE REDUCTION

Let  $S \subset \mathbb{F}^n$ . We define deg(S) to be the minimal degree of a non-zero polynomial that vanishes on S. We have seen that for a finite set S,  $deg(S) \leq n|S|^{1/n}$ . In fact, we can say something a little sharper. Let V(d) be the vector space of polynomials of degree  $\leq d$  in n variables. It has dimension  $\binom{d+n}{n}$ . If N < dim V(d), then  $deg(S) \leq d$ . This bound is sharp for generic sets S. (should we prove it?...) If deg(S) is significantly smaller than  $|S|^{1/n}$ , then it means that S has more algebraic structure than a generic set.

We are going to explore the connection between combinatorial properties of a set S and its algebraic structure. We will see that interesting examples in the kind of incidence geometry questions we have been studying need to have algebraic structure. Once we prove that a set has some algebraic structure, it makes sense to try to use that structure to study the set.

As a warmup, we consider a set of L lines in  $\mathbb{F}^3$ . It's easy to find a degree L polynomial that vanishes on the L lines, but in fact we can do better.

**Proposition 0.1.** For any L lines in  $\mathbb{F}^3$ , there is a polynomial of degree  $\leq 3L^{1/2}$  that vanishes on each line.

Proof. Let V(d) be the space of polynomials in three variables of degree  $\leq d$ . The dimension of V(d) is  $\binom{d+3}{3} \geq (1/6)d^3$ . We will choose the degree d later. We pick d+1 points on each of the L lines. If dimV(d) > (d+1)L, we can find a non-zero polynomial of degree  $\leq d$  that vanishes on all the points. Since it vanishes on d+1 points on each line, it will also vanish on all the lines. Therefore, we can find such a polynomial as long as  $(1/6)d^3 > (d+1)L$ .

## 1. Degree reduction

We have seen that the union of any L lines in  $\mathbb{F}^3$  has degree  $\lesssim L^{1/2}$ . Now we consider arrangements of lines with lots of incidences and prove that the union has much lower degree. This process is called degree reduction.

**Proposition 1.1.** Let X be a union of L lines in  $\mathbb{F}^3$ . Suppose that each line contains > A intersection points with other lines. Then the degree of X is  $\leq L/A$ .

This proposition holds automatically if  $A \leq L^{1/2}$ , and it becomes interesting when A is significantly larger than  $L^{1/2}$ . For example, suppose that we have L lines in  $\mathbb{R}^3$  with much more than  $L^{3/2}$  intersection points. If there are approximately the same number of intersection points on each line, then each line would contain much more

than  $L^{1/2}$  intersection points. Then the proposition would imply that the union of the lines has degree much smaller than  $L^{1/2}$ . The union has some special polynomial structure, and it's reasonable to try to use the polynomial structure to study the lines.

The first proof of the joints theorem used degree reduction. I think of it as one of the main steps/ideas in the polynomial method. This proposition is the first step in the proof of the Elekes-Sharir conjecture on the number of intersection points of a set of lines in  $\mathbb{R}^3$ . I also think of it as philosophically important in explaining why polynomials are relevant. The combinatorial structure of the problem forces the set of points or lines to have a special algebraic structure - and then it makes sense to use this structure to study the problem. The proof of degree reduction is similar to the proof of finite field Nikodym or other fundamental results. By counting dimensions, we find a low degree polynomial that vanishes on some points of X. Then by using the vanishing lemma, we see that it also has to vanish at other points of X, and eventually we prove that it vanishes on all of X.

We begin with heuristics - with an informal argument that describes the main idea of the proof. Let  $\mathcal{L}$  be our set of lines. Let d be a degree that we will choose later. We randomly choose a subset  $\mathcal{L}_0 \subset \mathcal{L}$  of size  $(1/10)d^2$ . By the last proposition, we can find a non-zero degree d polynomial P that vanishes on every line of  $\mathcal{L}_0$ .

Now the key point is that there are many incidences between the lines of  $\mathfrak{L}_0$  and the other lines of  $\mathfrak{L}$ . Therefore, our polynomial vanishes at many points on other lines of  $\mathfrak{L}$ . If we can check that our polynomial vanishes at d+1 points on each line of  $\mathfrak{L}$ , then it vanishes on all the lines of  $\mathfrak{L}$ . So let's pick a line  $l \in \mathfrak{L}$  and try to estimate how many points of l intersect a line of  $\mathfrak{L}_0$ .

Pick a line  $l \in \mathfrak{L}$ . It has A intersection points with other lines of  $\mathfrak{L}$ . Fix one of the intersection points. The probability that this intersection point lies in one of the lines of  $\mathfrak{L}_0$  is  $\geq (1/10)d^2/L$ . Therefore, the expected number of intersection points between l and lines of  $\mathfrak{L}_0$  is  $E \geq (1/10)Ad^2/L$ . We are going to choose d so that E > 100d. It suffices to choose d so that

$$(1/10)Ad^2/L \ge 100d.$$

Rearranging, it suffices to choose d so that  $d \ge 1000LA^{-1}$ . We now choose d to be an integer which is  $\le 1001L/A$  and so that  $E \ge 100d$ . On average, the polynomial P vanishes on  $\ge 100d$  points of l. This suggests that it vanishes on > d points of l with high probability. Since l was an arbitrary line of  $\mathfrak{L}$ , this suggests that P usually vanishes on most of the lines of  $\mathfrak{L}$ .

To get rigorous estimates, we need a little bit of probability. In particular, we will use the following lemma.

**Lemma 1.2.** (Probability lemma) Let S be a set of N elements. Let  $X \subset S$  be a random subset where each element of S is included in X independently with probability p. The expected size of X is pN.

- (1)  $\mathbb{P}[|X| > 2pN] \le exp(-\frac{1}{100}pN).$ (2)  $\mathbb{P}[|X| < (1/2)pN] \le exp(-\frac{1}{100}pN).$

We will prove the probability lemma at the end. The lemma says that the size of |X| is close to the expected value pN almost all the time. Now we can begin the formal proof of Proposition 1.1. We will use large constants that hopefully make the argument more transparent.

*Proof.* Let d be a degree which we will choose later. Let p be the number  $(1/20)d^2/L$ . We form a subset  $\mathfrak{L}_0 \subset \mathfrak{L}$  by including each line independently with probability p. With high probability, the size of  $\mathcal{L}_0$  is at most  $(1/10)d^2$ , and therefore we can find a non-zero polynomial P of degree  $\leq d$  that vanishes on the lines of  $\mathfrak{L}_0$ . (The probability of this step going wrong is at most  $exp(-\frac{1}{2000}d^2)$ , which we can arrange is always < 1/100.)

Fix a line l. It contains  $\geq A$  intersection points with other lines of  $\mathfrak{L}$ . Each of these intersection points has a probability  $\geq p$  of lying in a line of  $\mathfrak{L}_0 \setminus \{l\}$ . These events are independent. The expected number of points of l lying in lines of  $\mathfrak{L}_0$  is  $E \ge Ap = (1/20)d^2A/L$ .

We now choose d in the range  $(10^6 - 1)L/A \le d \le 10^6 L/A$ . An easy calculation shows that  $E > 10^4 d$ .

If l intersects  $\mathfrak{L}_0$  in  $\geq d+1$  points, then P=0 on l. But by the probability lemma, the probability that l intersects  $\mathfrak{L}_0$  in  $\leq d$  points is  $\leq exp(-\frac{1}{100}E) \leq exp(-100d) \leq$  $exp(-10^{7}L/A)$ .

If  $L/A > 1000 \log L$  then the probability that l contains  $\leq d$  intersection points with  $\mathfrak{L}_0$  is  $< L^{-10}$ . In this case, with high probability, P = 0 on every line of  $\mathfrak{L}$ , and we are done. This is the main case.

In the case that L/A is quite small, the proposition is still true but the proof is trickier. We sketch what to do in this minor case. We can arrange that P vanishes on 99% of the lines of  $\mathfrak{L}$ . Let  $\mathfrak{L}' \subset \mathfrak{L}$  be the lines where P doesn't vanish. We have  $|\mathfrak{L}'| < (1/100)|\mathfrak{L}|$ . Each line of  $\mathfrak{L}'$  has < d intersection points with lines of  $\mathfrak{L} \setminus \mathfrak{L}_0$ . But it has  $\geq A$  intersection points with lines of  $\mathfrak{L}$ . Now in this case, A is close to L and d is extremely small, so we can assume that each line of  $\mathfrak{L}'$  has > (99/100)Aintersection points with other lines of  $\mathcal{L}'$ . Now we can iterate or induct to find a polynomial P' that vanishes on  $\mathfrak{L}'$  with degree  $d' \leq (1/10)d$ , and we're done.

Here is a related result which is special to finite fields.

**Proposition 1.3.** Suppose that  $X = \bigcup_{l \in \mathcal{L}} l \subset \mathbb{F}_q^3$ . If each point of X lies in at least 2 lines of  $\mathfrak{L}$ , then  $deg X \lesssim \log q |X| q^{-2}$ .

Before we prove the result, let's discuss the bound. We saw in an early lecture that a non-zero polynomial of degree d vanishes at  $\leq dq^2$  points of  $\mathbb{F}_q^3$ . Therefore, for any set  $X \subset \mathbb{F}_q^3$ , we have  $|X|q^{-2} \leq degX \lesssim |X|^{1/3}$ . Sets with degree near the upper bound have no particular algebraic structure. Sets with degree near the lower bound have the most algebraic structure. So this proposition says that unions of lines with  $\geq 2$  lines through every point are almost as algebraically structured as possible. In fact, we will see that the  $\log q$  factor can be removed as long as  $|X|q^{-2} \geq \log q$ .

As a heuristic, imagine that we also knew that each point of X lies in  $\leq 10$  lines of  $\mathfrak{L}$ . Then  $|\mathfrak{L}| = L \leq 10|X|/q$ . Each line of  $\mathfrak{L}$  contains q points of intersection with other lines of  $\mathfrak{L}$ . In this case, the last proposition implies that  $deg(X) \lesssim L/A \sim |X|q^{-2}$ . The full proof is a modification of the proof of the last proposition, and the annoying special case at the end seems harder to deal with.

Proof. We form a subset  $\mathfrak{L}_1 \subset \mathfrak{L}$  as follows. Suppose that the lines of  $\mathfrak{L}$  are put in order,  $l_1, l_2, ...$  We go through the list of lines one at a time and decide whether to add each line to  $\mathfrak{L}_1$ . If a given line contains  $\geq q/2$  points which are not in any line already in  $\mathfrak{L}_1$ , then we add the line to  $\mathfrak{L}_1$ . Otherwise we don't. Since each line of  $\mathfrak{L}_1$  brings  $\geq q/2$  new points of X,  $|\mathfrak{L}_1| \leq 2|X|q^{-1}$ . Every line in  $\mathfrak{L} \setminus \mathfrak{L}_1$  intersects lines of  $\mathfrak{L}_1$  at  $\geq q/2$  distinct points. (Otherwise, we would have added it to  $\mathfrak{L}_1$ .) We let  $L = |\mathfrak{L}_1| \sim |X|/q$ .

We let d be a degree to be chosen later, and as above we let  $\mathfrak{L}_0 \subset \mathfrak{L}_1$  be a random subset where each line of  $\mathfrak{L}_1$  is included independently with probability  $p = (1/20)d^2/L$ . With high probability,  $|\mathfrak{L}_0| \leq (1/10)d^2$ , and we can choose a non-zero polynomial P of degree  $\leq d$  so that P = 0 on each line of  $\mathfrak{L}_0$ .

Let's assume for now that  $|X|q^{-2} \ge \log q$ . Let l be a line of  $\mathfrak{L}$  that intersects lines of  $\mathfrak{L}_1$  at  $\ge A = q/2$  points. Note that every line of  $\mathfrak{L} \setminus \mathfrak{L}_1$  has this property. The expected number of intersections between l and lines of  $\mathfrak{L}_0$  is  $\ge E = Ap = (1/20)d^2A/L$ . As in the last proof, we choose E so that  $E \ge 10^4d$ . We can do this with a degree  $d \sim L/A \sim |X|q^{-2}$ . More precisely, we can arrange that d is between  $10^5|X|q^{-2}$  and  $10^6|X|q^{-2}$ , and that  $E \ge 10^4d$ . Now the probability that l intersects lines of  $\mathfrak{L}_0$  in  $\le d$  places is  $\le exp(-\frac{1}{100}E) \le exp(-10^7|X|q^{-2}) \le exp(-10^7\log q) = q^{-10^7}$ . The total number of lines in  $\mathbb{F}_q^3$  is  $\le 10q^4$ , which is much smaller. So we can arrange that P vanishes on every line l with  $\ge q/2$  intersections with lines of  $\mathfrak{L}_1$ . In particular P vanishes on all the lines of  $\mathfrak{L} \setminus \mathfrak{L}_1$ . Finally, a line of  $\mathfrak{L}_1$  either intersects lines of  $\mathfrak{L}_1$  in  $\ge q/2$  points, or else it intersects lines of  $\mathfrak{L} \setminus \mathfrak{L}_1$  in  $\ge q/2$  points. Either way, we conclude that P vanishes on l. To summarize, assuming that  $|X|q^{-2} \ge \log q$ , we have proven that  $deg(X) \le 10^6|X|q^{-2}$ .

Next we turn to the small case,  $|X|q^{-2} < \log q$ . The argument goes basically the same, but now we need to choose E so that  $E \ge 10^4 d$  and  $E \ge 10^4 \log q$ . The second criterion may be harder in the small case. To arrange it, we need to know that

 $(1/20)d^2A/L \ge 10^4 \log q$ , and so  $d^2 \ge CLA^{-1} \log q = |X|q^{-2} \log q \le C(\log q)^2$ . In this case we can arrange that  $d \le \log q$ . The rest of the argument goes the same.  $\square$ 

Remark: It would be nice to remove this suspicious  $\log q$  factor, and it would also be nice to clean up the proof.

Let's try to list examples of such sets. A plane has this property. A regulus (like z=xy) has this property. If  $X_i$  are sets with this property then the union of  $X_i$  has this property. In particular, unions of planes and reguli have this property. Very large sets also have this property - say the complement of a few points. Of course, the complement of a few points is a union of planes, but I wouldn't be surprised to find sets with  $\sim q^3$  points with this property which aren't unions of planes and reguli. Later we will meet a strange example: the Heisenberg group. The Heisenberg group has this property, it has  $\sim q^{5/2}$  points, and it is not a union of planes and reguli. I conjecture that a set X with this property and  $< (1/100)q^{5/2}$  points is a union of planes and reguli.

### 2. An Application

**Proposition 2.1.** Let  $\mathfrak{L} = \{l_i\}i \in I$  be a set of lines in  $\mathbb{F}_q^3$ . Let  $S_i \subset l_i$  be a subset of size  $\geq q/2$ . Let  $X = \cup_i S_i \subset \cup_i l_i = Y$ . Then  $|Y| \leq C(\log q)|X|$ .

Remark: As above, the  $\log q$  factor appears only if  $|X| < (\log q)q^2$ . Perhaps it can be removed entirely.

We start with a naive application of the polynomial method. We can find a non-zero polynomial P that vanishes on X with degree  $d \lesssim |X|^{1/3}$ . If |X| is close to  $q^3$ , there is nothing to prove, and so we can assume that d < q/2. Now P vanishes on  $\geq q/2 > d$  points on each line  $l_i$ , so P vanishes on Y. However, this does not give such a good bound for |Y|. It only implies that  $|Y| \leq C|X|^{1/3}q^2$ . For example, if  $|X| = q^{5/2}$ , we get  $|Y| \lesssim q^{17/6}$ .

We can do better by a degree reduction argument. We sketch the argument here. It is similar to the last proposition. We make a subset  $I_1 \subset I$  as follows. We consider the lines  $l_i$  one at a time and decide whether to add  $itoI_1$ . We add i to  $I_1$  if  $S_i$  contains  $\geq q/4$  points that aren't already in the union of  $\{S_i\}_{i\in I_1}$ . At the end  $|I_1|=L\leq 4|X|q^{-1}$ . Also for each  $i\in I\setminus I_1$ ,  $S_i$  intersects the sets in  $I_1$  in  $\geq A=q/4$  points.

By the same argument as above, we can find a non-zero polynomial P of degree  $d \leq 10^6 \log q |X| q^{-2}$  so that that P vanishes on  $l_i$  for each  $i \in I \setminus I_1$ , and vanishes on  $l_i$  for  $i \in I_1$  as long as  $S_i$  intersects other sets  $\{S_i\}_{i \in I}$  for  $\geq q/4$  points.

Define  $I_{meager} \subset I$  to be the set of i so that  $S_i$  intersects other  $S_i$ 's in  $\leq q/4$  points. The polynomial P vanishes on  $l_i$  for each  $i \in I \setminus I_{meager}$ . The union of lines  $l_i$  with

 $i \in I \setminus I_{meager}$  has size  $\leq dq^2 \lesssim \log q|X|$ . The size of  $I_{meager}$  is  $\leq 4|X|q^{-1}$ . So the union of the lines in  $I_{meager}$  has size  $\leq 4|X|$ .

#### 3. A Probability Lemma

We recall and prove the probability lemma that we used above.

**Lemma 3.1.** (Probability lemma) Let S be a set of N elements. Let  $X \subset S$  be a random subset where each element of S is included in X independently with probability p. The expected size of X is pN.

- (1)  $\mathbb{P}[|X| > 2pN] \le exp(-\frac{1}{100}pN).$ (2)  $\mathbb{P}[|X| < (1/2)pN] \le exp(-\frac{1}{100}pN).$

*Proof.* We let  $a_j$  be 1 if the  $j^{th}$  element of S is included in X and 0 otherwise. The functions  $a_j$  are independent, and the probability that  $a_j = 1$  is p. Also  $|X| = \sum_i a_j$ .

Using independence we get the following equation, which holds for any number  $\beta \in \mathbb{R}$ :

$$\mathbb{E}e^{\beta|X|} = \mathbb{E}\prod_{i} e^{\beta a_{i}} = \prod_{i} \mathbb{E}e^{\beta a_{i}} = (pe^{\beta} + 1 - p)^{N}.$$

On the other hand,  $\mathbb{P}[|X| > 2pN] e^{2\beta pN} \leq \mathbb{E}e^{\beta|X|}$ . Combining these equations, we get the following upper bound for the probability that |X| is > 2pN:

$$\mathbb{P}\left[|X|>2pN\right] \leq \left\lceil \frac{pe^{\beta}+1-p}{e^{2\beta p}}\right\rceil^{N}.$$

This bound holds for any  $\beta$ . If  $\beta > 0$ , then the fraction in brackets is < 1. Taking  $\beta = 1$ , the fraction in brackets is  $\leq (1 + p(e-1))/(1 + 2p) \leq exp(-p/100)$ . Therefore, inequality 1 holds.

To prove inequality 2, we use a similar argument. We observe that  $\mathbb{P}[|X| < (1/2)pN]e^{(1/2)\beta pN} \le$  $\mathbb{E}e^{\beta|X|}$ . Thus we get the following upper bound for the probability that |X| is < (1/2)pN:

$$\mathbb{P}\left[|X| < (1/2)pN\right] \le \left\lceil \frac{pe^{\beta} + 1 - p}{e^{(1/2)\beta p}} \right\rceil^{N}.$$

This bound again holds for any  $\beta$ . If  $\beta$  is negative and close to zero, then the expression in brackets is < 1. In particular, if  $\beta = -1/10$  then the expression in brackets is at most

$$\frac{1 - (1/10)p + (2/100)p}{1 - (1/20)p} \le exp(-p/100).$$

Therefore, inequality 2 holds.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### BEZOUT THEOREM

One of the most fundamental results about the degrees of polynomial surfaces is the Bezout theorem, which bounds the size of the intersection of polynomial surfaces. The simplest version is the following:

**Theorem 0.1.** (Bezout in the plane) Suppose  $\mathbb{F}$  is a field and P,Q are polynomials in  $\mathbb{F}[x,y]$  with no common factor (of degree  $\geq 1$ ). Let  $Z(P,Q):=\{(x,y)\in\mathbb{F}^2|P(x,y)=Q(x,y)=0\}$ . Then the number of points in Z(P,Q) is  $\leq (degP)(degQ)$ .

There are several approaches to proving the Bezout theorem. I found one approach that feels closely related to the methods we've been studying. (It appears in Joe Harris's book *Algebraic Geometry*, a First Course, exercise 13.17.)

The proof uses the unique factorization of polynomials. We recall exactly what this means.

For any field  $\mathbb{F}$ , the ring of polynomials over  $\mathbb{F}$  in n variables,  $\mathbb{F}[x_1,...,x_n]$  obeys unique factorization. The units in this ring are exactly the non-zero elements of  $\mathbb{F}$ . A non-zero polynomial P is called irreducible if whenever  $P = P_1 \cdot P_2$ , one of  $P_1, P_2$  is a unit. Unique factorization says that if P can be written as a product of irreducibles in two different ways, say  $P = \prod_i P_i = \prod_j Q_j$ , then there are the same number of factors in each product, and we can reorder the indices so that  $Q_i = c_i P_i$  where  $c_i \in \mathbb{F} \setminus \{0\}$ .

There are a number of variations on the statement of the Bezout theorem, and we mention them later.

### 1. A PROOF OF BEZOUT IN THE PLANE

Let  $\bar{I}$  be the ideal generated by P,Q, and let  $S = \mathbb{F}[x,y]/\bar{I}$ . We can roughly think of S as the ring of polynomial functions on Z(P,Q), and it follows from this that  $|Z(P,Q)| \leq dimS$ . (We think of S as a vector space over  $\mathbb{F}$  in order to define its dimension.)

Lemma 1.1.  $|Z(P,Q)| \leq dim S$ .

*Proof.* For any set  $X \subset \mathbb{F}_2$  let  $E_X$  be the evaluation (or restriction) map from  $\mathbb{F}[x,y]$  to  $Fcn(X,\mathbb{F})$ . If X is a finite set, then  $E_X$  is surjective. We state this as a lemma, and we'll prove it later.

**Lemma 1.2.** If  $X \subset \mathbb{F}^n$  is any finite set, and  $f: X \to \mathbb{F}$  is any function, then there is a polynomial which agrees with f on X.

If  $X \subset Z(P,Q)$ , then  $\bar{I}$  is in the kernel of  $E_X$ , and so we can think of  $E_X$  as a map from S to  $Fcn(X,\mathbb{F})$ . If  $X \subset Z(P,Q)$  is finite, then  $E_X$  is surjective, and so  $dimS \geq |X|$ .

Our goal is to bound the dimension of S by (degP)(degQ). In order to do this, we will mod out by P and then by Q, and keep track of dimensions of the objects at each step.

Let I be the ideal of  $\mathbb{F}[x,y]$  generated by P. Let  $R = \mathbb{F}[x,y]/I$ . The dimensions of R and I are both infinite, but we can get valuable information by considering polynomials of degree  $\leq d$ . Let  $V_d \subset \mathbb{F}[x,y]$  be the polynomials of degree  $\leq d$ . Let  $I_d = I \cap V_d$ , and let  $R_d = V_d/I_d \subset R$ . We will consider the dimensions of these spaces as functions of d.

The dimension of  $V_d$  is  $\binom{d+2}{2}$ , as we have seen.

**Lemma 1.3.** The dimension of 
$$I_d$$
 is  $dimV_{d-D} = {d-D+2 \choose 2}$  for all  $d \ge D$ .

*Proof.* Multiplication by P gives a linear map from  $V_{d-D}$  to  $I_d$ . We claim this linear map is an isomorphism. The kernel of the map is zero. Any element in  $I_d$  can be written as PQ for some Q, and we must have  $degQ \leq d - D$ , so that the map is surjective.

The dimension of  $R_d$  is  $dimV_d - dimI_d = {d+2 \choose 2} - {d-D+2 \choose 2} = Dd + (3/2D - D^2)$ , for  $d \ge D$ .

Now let J be the ideal of R generated by Q. Let S = R/J, and note that this is the same ring S defined above. Let  $J_d = J \cap R_d$  and  $S_d = R_d/J_d$ .

## **Lemma 1.4.** The dimension of $J_d$ is $\geq dim R_{d-E}$ .

Proof. Multiplication by Q gives a map from  $R_{d-E}$  to  $J_d$ . We claim that this map is injective. Suppose  $r_1 \in R_{d-E}$  is in the kernel of the map. Let  $P_1 \in V_{d-E}$  be a polynomial representing  $r_1$ . We see that  $QP_1$  is in I, so  $QP_1 = PP_2$  for some polynomial  $P_2$ . By unique factorization, we see that P divides  $P_1$ . But then  $P_1 \in I$  and  $P_1 = 0$ .

(Exercise: Do we get equality in this lemma?) The dimension of  $S_d$  is  $dim R_d - dim I_d \leq dim R_d - dim I_{d-E}$ . If  $d \geq D + E$ , then

$$dimR_d - dimR_{d-E} = [Dd + (3/2D - D^2)] - [D(d - E) + (3/2D - D^2)] = DE.$$

Since this holds for every d, we conclude that  $dimS \leq DE$  and so  $|Z(P,Q)| \leq DE$ .

1.1. **Polynomials with prescribed values.** Now we return to Lemma 1.2 at the beginning of the last section:

**Lemma 1.5.** If  $X \subset \mathbb{F}^n$  is any finite set, and  $f: X \to \mathbb{F}$  is any function, then there is a polynomial P of degree  $\leq |X| - 1$  which agrees with f on X.

Proof. For each  $p \in X$ , we will construct a polynomial  $P_p$  with  $P_p(p) = 1$  and  $P_p = 0$  on  $X \setminus p$ . Fix p. For each  $q \in X \setminus p$ , let  $L_q$  be a polynomial that vanishes at q but not at p. Then define  $P_p = c \prod_{q \in X \setminus p} L_q$ . We see that  $P_p(q) = 0$  for each  $q \in X \setminus p$ , and that  $P_p(p) \neq 0$ . By choosing the constant c, we can arrange that  $P_p(p) = 1$ . The degree of  $P_p$  is |X| - 1.

Finally, for an arbitrary function f, we define  $P = \sum_{p \in X} f(p) P_p$ .

### 2. Statements of the Bezout Theorem

The Bezout theorem is usually stated as an equality (by algebraic geometers). It roughly says that if P and Q have no common factor, then the "number" of points in Z(P,Q) is equal to (degP)(degQ). To make this work we need to work over an algebraically closed field and we need to work over projective space, and we need to count intersections with multiplicity.

For example, let's try to consider two circles  $x^2 + y^2 = 100$  and  $(x-5)^2 + y^2 = 100$ . Initially, we consider x, y in  $\mathbb{R}$ , where we can easily visualize the circles. They appear to intersect in two points. Where are the other two points? What if we allow x, y to be complex numbers? In fact this doesn't lead to any more intersection points. But if we work over complex projective space, we get two more intersection points at infinity. Now what if we slide the circles apart so that they become tangent and then disjoint. In  $\mathbb{R}^2$ , the number of intersection points goes from 2 to 1 to 0. When the circles become disjoint over  $\mathbb{R}^2$  they develop two points of intersection in  $\mathbb{C}^2 \setminus \mathbb{R}^2$ . At the moment of tangency, there is only one intersection point in  $\mathbb{C}^2$ , plus two intersection points at infinity. But this one intersection point at the tangency has "multiplicity 2". Counting with multiplicity, there are still exactly four intersection points.

The full statement of the equality Bezout theorem requires some work to define the multiplicities of the intersections. Because the statement is more complicated the full proof is rather longer than this. But the inequality version is what we will need in our applications. In my opinion, the inequality version of the Bezout theorem is somewhat underrated. It takes only a fraction of the effort to state and prove it, and it still has many applications.

#### 3. The Hilbert Polynomial

To give context, we mention without proof some important related concepts. (I don't really know this area myself. I hope there are not errors. Anyway, we won't use any of these statements later.)

Let's look back at the proof of the Bezout theorem in the plane. Recall that I is the ideal generated by P and  $R = \mathbb{F}[x,y]/I$ . A key observation was the formula for the dimension of  $R_d$ :

$$dim R_d = Dd + (3/2D - D^2)$$
, for  $d \ge D$ .

In general, for any ideal I in  $\mathbb{F}[x_1,...,x_n]$ , we can define  $R = \mathbb{F}[x_1,...,x_n]/I$  and  $R_d = V_d/I_d$ , and we can study the dimension of  $R_d$ . Another basic example is given by the ideal I = 0. In this case,  $R = \mathbb{F}[x_1,...,x_n]$ , and so we have seen that

$$dim R_d = {d+n \choose n} = (1/n!)d^n + \text{ lower order terms.}$$

In general, the dimension of  $R_d$  is always given by a polynomial, called the Hilbert polynomial, for all d sufficiently large.

$$dim R_d = h_I(d) = \sum_{j=0}^m a_j d^j$$
, for  $d \ge d_0$ .

The leading term of the Hilbert polynomial,  $a_m d^m$  is particularly interesting. In the first example above, the leading term was Dd. In the second example, the leading term was  $(1/n!)d^n$ . In general, m will be the dimension of Z(I) and  $m!a_m$  will be the degree of Z(I). (We have not defined dimension and degree anywhere else. These can be taken as definitions, and they are equivalent to other definitions in algebraic geometry...)

In the polynomial method, it was very important to observe that in n dimensions, the space of polynomials of degree  $\leq d$  has dimension growing like  $d^n$ . In the Hilbert polynomial perspective, this feature can be taken as the definition of the dimension of a variety Z(I).

#### 4. The Bezout theorem in higher dimensions

The Bezout theorem can be generalized to higher dimensions. The full statement gets harder to prove. In our applications, we will need the following minor generalization. Let  $\mathbb{F}$  be an infinite field.

**Theorem 4.1.** If  $P, Q \in \mathbb{F}[x, y, z]$  have no common factor (of degree  $\geq 1$ ), then the number of lines in Z(P,Q) is  $\leq (degP)(degQ)$ .

*Proof.* We define  $\bar{I}$  to be the ideal generated by P and Q, and we define S to be the ring  $\mathbb{F}[x,y,z]/\bar{I}$ . If the ring S contains many lines, then it must be large in some sense. But if the degrees of P and Q are small, then S must be small in some sense. Let us make this precise. Let  $V_d \subset \mathbb{F}[x,y,z]$  be the polynomials of degree  $\leq d$ . Let

 $\bar{I}_d = \bar{I} \cap V_d$ , and  $S_d = V_d/\bar{I}_d$ . On the one hand, we will bound the dimension of  $S_d$ from above using the degrees of P and Q:

$$dim S_d \leq (deg P)(deg Q)d + c(P, Q).$$

On the other hand, if Z(P,Q) contains L lines, then we will bound the dimension of  $S_d$  from below as follows:

$$dim S_d \ge Ld - c(L)$$
.

Given these two bounds, taking  $d \to \infty$ , we see that  $L \leq (deg P)(deg Q)$ .

Now we turn to the upper bounds on  $S_d$ .

We closely follow the argument in the planar case. Let D = degP and E = degQ. I is the ideal generated by P, and R is  $\mathbb{F}[x,y,z]/I$ . J is the ideal of R generated by Q. S = R/J.

The dimension of  $I_d$  is equal to  $dimV_{d-D} = \binom{d-D+3}{3}$  for  $d \ge D$ . The dimension of  $R_d$  is  $dimV_d - dimI_d = \binom{d+3}{3} - \binom{d-D+3}{3} = (1/2)Dd^2 + \text{lower order terms.}$ 

The dimension of  $J_d$  is  $\geq dim R_{d-E} = (1/2)D(d-E)^2 + \text{lower order terms}$ .

The dimension of  $S_d$  is  $dim R_d - dim J_d \leq dim R_d - dim R_{d-E} = DEd +$ lower order terms.

In other words,  $dimS_d = DEd + c$ , where c is a constant that depends on P, Q but not on d.

Now we turn to the lower bounds on the size of  $S_d$  related to the lines in Z(P,Q). For any set  $X \subset \mathbb{F}^3$ , let  $E_X$  be the restriction map from  $V_d$  to  $Fcn(X, \mathbb{F})$ .

**Lemma 4.2.** If X is a union of L lines in  $\mathbb{F}^n$ , then the rank of  $E_X: V_d \to Fcn(X, \mathbb{F})$ is  $\geq Ld - c(L)$ . (Recall that  $\mathbb{F}$  is an infinite field.)

We will come back to the proof of this lemma. For now, we use this lemma. If  $X \subset$ Z(P,Q), then I is in the kernel of  $E_X$ , and so  $E_X$  is a map from  $S_d$  to  $Fcn(X,\mathbb{F})$ . In particular, the dimension of  $S_d$  is at least the rank of the map  $E_X: V_d \to Fcn(X, \mathbb{F})$ . If Z(P,Q) contains L lines, then Lemma 4.2 implies that the dimension of  $S_d$  is at least Ld - c(L).

Now we turn to the proof of Lemma 4.2

*Proof.* Fix d. After a linear change of variables, we can assume that each line is transverse to planes of the form  $x_n = h$ . Choose d - L values  $h_1, ..., h_{d-L}$  so that each plane  $x_n = h_j$  intersects the L lines in L distinct points. Let  $X_0 \subset X$  be these L(d-L) points.

We claim that for any function  $f: X_0 \to \mathbb{F}$ , there is a degree d polynomial that agrees with f on  $X_0$ . This will imply that  $rankE_X: V_d \to Fcn(X, \mathbb{F})$  is at least  $|X_0| = Ld - L^2$ .

Fix a value  $h_j$ . The set  $X_0$  intersects the plane  $x_n = h_j$  at L points,  $(y_{1,j}, h_j), ..., (y_{L,j}, h_j)$  with  $y_{k,j} \in \mathbb{F}^{n-1}$ . By Lemma 1.5, we can find a degree L polynomial  $P_j$  in n-1 variables so that  $P_j(y_{k,j}) = f(y_{k,j})$  for each  $y_{k,j}$ .

Now we want to find a polynomial P in n variables with degree  $\leq d$  so that  $P(y,h_j)=P_j(y)$  for all y and all j from 1 to d-L. Let's expand out  $P_j$  and P:

$$P_j(y) = \sum_I c_I(j) y^I$$
, where I is an exponent in (n-1) variables of degree at most L.

Now we will choose P to have the following form:

$$P(y, x_n) = \sum_{I} P_I(x_n) y^I$$
, where  $|I| \le L$  and  $deg P_I \le d - L$ .

It suffices to choose  $P_I$  so that  $P_I(h_j) = c_I(j)$  for each j = 1, ..., d - L. We can do this by applying Lemma 1.5 again.

This finishes the proof of Theorem 4.1.

Exercise: Figure out what happens in finite fields. Check that the result is still true if degP,  $degQ < |\mathbb{F}|$  or if the theorem is phrased carefully.

Finally, we discuss/explore what might be true more generally in higher dimensions. Suppose that we have some ideals  $I_j$  in  $\mathbb{F}[x_1,...,x_n]$ . Suppose that  $I_j$  has dimension  $m_j$  and degree  $D_j$ . In other words, if  $R_{j,d} = V_d/I_{j,d}$ , then

$$dim R_{j,d} = D_j(m_j!)^{-1} d^{m_j} + \text{ lower order terms, for all } d \text{ sufficiently large.}$$

Let I be the ideal generated by  $I_j$ . Suppose that it has dimension m and degree D. Now we may pose the following question:

Question 1. If 
$$(n-m) = \sum_{j} (n-m_j)$$
, then is  $D \leq \prod_{j} D_j$ ?

The condition on the dimensions is similar to asking that P and Q have no common factor in the planar version of Bezout.

It would be cool to know whether this is true, and also to see if there is a proof in the spirit of the arguments above.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## SPECIAL POINTS AND LINES OF ALGEBRAIC SURFACES

## 1. Introduction

As we have seen many times in this class we can encode combinatorial information about points and lines in terms of algebraic surfaces. Looking at these surfaces can in turn show us things about the underlying combinatorics that are not obvious at first glance.

One theme that comes up often when looking at these surfaces is that they contain special points— such as critical points, etc- whose presence or absence tells us something about our underlying combinatorial problem. Todays lecture focuses on this theme.

## 2. Critical points

Consider a polynomial  $P \in \mathbb{R}[x_1, \dots, x_n]$ . Let Z(P) be its zero set, aka

$$Z(P) = \{x \in \mathbb{R}^n | P(x) = 0\}$$

Recall that a point x is called a critical point if and only if  $\nabla P(x) = 0$ . Recalling the implicit function theorem:

**Theorem 2.1.** If a point  $x \in Z(P)$  is not a critical point of P then Z(P) is a smooth manifold in some open neighborhood centered at x.

We might hope that, in general, there are very few critical points. This is not always the case. Consider

$$P(x_1,\ldots,x_n)=x_1^2$$

Then every point on the plane  $\{x_1 = 0\}$  is a critical point of P. Unfortunate as this may be it turns out that, in some sense, this is the only case we have to worry about.

**Definition 2.2.** A polynomial P is square free if, whenever a polynomial  $Q^2$  divides P, we have that Q is constant.

Our pathological example is not square free—if, however, we only consider square free polynomial then everything works out:

**Lemma 2.3.** If P is square free then  $P, \partial_1 P, \dots, \partial_n P$  have no common nonconstant factors.

*Proof.* Assume that P is square free, and that  $P, \partial_1 P, \ldots, \partial_n P$  have a common non-constant factor Q. Without loss of generality we can assume that this factor is irreducible. We say that  $R \sim Q$  if R = cQ for some  $c \neq 0$ . Then note that we can write

$$P = \Pi P_i$$

where each of the  $P_j$  is irreducible. Since Q is irreducible and divides P it must be the case that  $Q \sim P_j$  for some j. This implies  $P_j$  divides  $\partial_i P$  for all i. Using the product rule note that

$$\partial_i P = \sum_{j_0} \partial_i P_{j_0} \prod_{j \neq j_0} P_j$$

Therefore, since  $P_j$  divide  $\partial_i P$  for all i, the fact that  $P_j$  divides  $\prod_{k \neq j_0} P_k$  for all  $j_0 \neq j$  tells us that  $P_j$  divides  $\partial_i P_j \prod_{j \neq k} P_k$ . Since P is square free we know that  $P_j$  can not divide  $\prod_{j \neq k} P_k$ . This implie  $P_j$  must divide  $\partial_i P_j$ . However, since  $\partial_i P_j$  has smaller degree than  $P_j$  it must be that  $\partial_i P_j = 0$  for all i. This implies  $P_j$ , and thus Q, is constant. Therefore we have a contradiction.

This can be used to prove the following result.

**Proposition 2.4.** If n = 2 and P is a square free polynomial of degree d then the number of critical points in Z(P) is at most  $2d^2$ .

*Proof.* Assume  $x \in Z(P)$  is a critical point, then P(x) = 0 and  $\partial_i P(x) = 0$  for all i. We can write  $P = \prod P_j$ , where  $P_j$  is irreducible. The product formula then implies that either  $x \in Z(P_j)$  for at least two j, or else x is a critical point of  $Z(P_j)$  for some j. We call these points type a and type b respectively.

First let us count the number of type a points. Since each pair  $P_i$ ,  $P_j$  is relatively prime (assuming  $i \neq j$ ) the number of x that are zeros of of both  $P_i$  and  $P_j$  is, according to Bezouts theorem, bounded above by  $deg(P_i)deg(P_j)$ . Therefore the total number of type a points is bounded above by

$$\sum_{i \neq j} deg(P_i) deg(P_j) \le d^2$$

Next we want to bound the number of type b points. We know that  $P_j$  is irreducible, and that there exists i so that  $\partial_i P_j$  is not identically 0. Since  $P_j$  is irreducible we know that  $P_j$  and  $\partial_i P_j$  can have no common factor, so by Bezouts they share at most

$$deg(P_j)deg(\partial_i P_j) \le deg(P_j)^2$$

zero points, so the number of critical points in  $Z(P_j)$  is at most  $deg(P_j)^2$ , so the total number of type b points is at most

$$\sum_{j} deg(P_j)^2 \le d^2$$

Adding these bounds together gives us our result.

The above theorem relied heavily on Bezouts theorem. In some cases we need a slightly different version of Bezouts, one that works for lines instead of points.

**Theorem 2.5.** If  $P, Q \in \mathbb{R}[x_1, x_2, x_3]$  have no common factor then the set  $Z(P) \cap Z(Q)$  contains at most deg(P)deg(Q) lines

A proof of the above is given in the notes from last time. To gain some intuition of why it is true assume we pick some random plane  $\Pi$  in  $\mathbb{R}^3$ . We can then restrict P and Q to  $\Pi$ , giving us  $\tilde{P}$  and  $\tilde{Q}$ . In general we expect each line in  $Z(P,Q) = Z(P) \cap Z(Q)$  to intersect  $\Pi$  exactly once, so if Z(P,Q) contains L lines then

$$L \le |Z(P,Q) \cap \Pi| = |Z(\tilde{P},\tilde{Q})|$$

we expect that  $\tilde{P}$  and  $\tilde{Q}$  won't have any factors in common (though we will not prove this here), so Bezout tells us that

$$L \leq |Z(\tilde{P}, \tilde{Q})| \leq deg(\tilde{P})deg(\tilde{Q}) \leq deg(P)deg(Q)$$

which is what we wanted.

Now that we have a version of Bezout for lines we can use an almost identical argument to the one in Proposition 2.4 to give us

**Proposition 2.6.** If  $P \in \mathbb{R}[x_1, x_2, x_3]$  has degree d and is square free then Z(P) contains at most  $2d^2$  critical lines (aka lines all of whose points are critical).

#### 3. Joints and Critical Points

We saw a connection between combinatorics and critical points in the joints problem. Below is a sketch of an alternative proof of the joints problem (the original one) that makes this even more explicit. The bound for the joints problem follows easily from the below lemma by induction:

**Lemma 3.1.** If we have L lines in  $\mathbb{R}^3$  one of these lines has at most  $1000L^{\frac{1}{2}}$  joints on it.

*Proof.* This is only a sketch.

We will proceed in a proof by contradiction.

The first step is degree reduction: create a polynomial P, P = 0 on all the lines. We can easily choose P to be square free, with  $deg(P) \leq \frac{1}{10}L^{\frac{1}{2}}$ 

Step 2 is to note that  $\nabla P = 0$  on all the joints. Step 3 is to note, since we are assuming each of the lines has a lot of joints on it that  $\nabla P = 0$  identically on all lines.

This implies that Z(P) has L critical lines in it, were  $L > 2deg(P)^2$ . This, however, is a contradiction.

#### 4. Flat Points

In the below assume that n = 3.

**Definition 4.1.** Assume that  $x \in Z(P)$  is not a critical point. We can rotate and translate Z(P) so that x = 0 and

$$T_x Z(P) = \{x_3 = 0\}$$

(where  $T_xM$  is the tangent plane of M at x for a given x and M). Then around x the surface Z(P) is given by the equation

$$x_3 = Q(x_1, x_2) + O(x_1, x_2)^3$$

where Q is homogeneous of degree 2. We say that x is flat iff Q = 0.

There are numerous equivalent ways to state this condition. Let N be the normal to Z(P). Then x is flat iff  $\partial_v N(x) = 0$  for all  $v \in T_x Z(P)$ .

Note that  $N = \frac{\nabla P}{|\nabla P|}$ . More than that  $v \in T_x Z(P)$  iff  $v \cdot \nabla P = 0$ . Therefore we can use this to try to give an alternative characterization of flat. Before doing so, however, we want to introduce some tricks.

The first trick is to see that  $\partial_v N = 0$  iff  $\partial_v \nabla P$  is parallel to  $\nabla P$ , which happens iff

$$\partial_v \nabla P \times \nabla P = 0$$

The second trick is to note that  $\{e_j \times \nabla P\}_{j=1,2,3}$  is a spanning subset of  $T_x Z(P)$ . The above inspires us to define

$$SP(x) = \{(\partial_{e_j \times \nabla P} \nabla P(x)) \times \nabla P(x)\}_{j=1,2,3}$$

Note that SP(x) is a collection of 3 vectors, and is polynomial in x. We can then put the above together in a proposition:

**Proposition 4.2.** If  $x \in Z(P)$  then SP(x) = 0 iff  $\nabla P(x) = 0$  or x is flat.

*Proof.* This just follows by stringing all the above results together.

Clearly if  $\nabla P(x) = 0$  then  $(\partial_{e_j \times \nabla P} \nabla P(x)) \times \nabla P(x) = 0$  so SP(x) = 0. Similarly if x is flat then

$$(\partial_{e_j \times \nabla P} \nabla P(x)) \times \nabla P(x) = 0$$

so SP(x) = 0.

On the other hand assume that SP(x) = 0 and that  $\nabla P(x) \neq 0$  then since

$$(\partial_{e_i \times \nabla P} \nabla P(x)) \times \nabla P(x) = 0$$

for all j = 1, 2, 3, and since  $\{e_j \times \nabla P\}_{j=1,2,3}$  spans  $T_x Z(P)$  it must be that

$$(\partial_v \nabla P(x)) \times \nabla P(x) = 0$$

for all  $v \in T_x Z(P)$ , which implies

$$(\partial_v \nabla P(x)) \times N = 0$$

which implies x is flat.

We can see that, if every point of Z(P) is flat then Z(P) is a plane. This, however, is the only case when we can have a lot of flat lines. To see this, define a special line be one where every point on the line satisfies SP(x) = 0 (note that ever flat line is special).

**Proposition 4.3.** If P is an irreducible degree d polynomial and P is not linear then Z(P) contains at most  $3d^2$  special lines.

*Proof.* First consider the case that P does not divide every component of SP(x), which is to say that there is some j so that P does not divide some component of  $(\partial_{e_j \times \nabla P} \nabla P) \times \nabla P$ . The claim then follows by Bezout.

Therefore assume P divides every component of SP(x). This implies SP(x) = 0 on all of Z(P).

First consider the case that there exists a noncritical point  $x \in Z(P)$ . This implies Z(P) is smooth in a neighborhood of x. More than that it is flat in that neighborhood, so it must locally be a plane. Therefore Z(P) must contain that entire plane. This implies that the linear polynomial whose zero set equals this plane must divide P. Putting this together with the fact that P is irreducible implies that Z(P) must be linear. This is a contradiction.

Therefore all points in Z(P) are critical. Therefore every line is critical, but we know there are at most  $2d^2$  critical lines, so we are done.

We will apply the above to prove some combinatorial results next week. In particular we will prove a special case of the ES conjecture, namely that:

**Theorem 4.4.** Assume we have L lines in  $\mathbb{R}^3$ , with at most B lines on any plane. Then if  $P_3$  is the set of points lying on 3 lines we have that  $|P_3| \leq cBL$  for some constant c

If we define  $P_k$  in the analogous way then  $|P_k| \leq cL^{\frac{3}{2}}k^{-2}$ .

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## APPLICATION TO INCIDENCE THEORY OF LINES IN SPACE

In connection with the distinct distance problem, we encountered the following question about lines in  $\mathbb{R}^3$ . Given L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane, how many points can there be in  $P_k(\mathfrak{L})$ ? Elekes and Sharir conjectured the answer to this question, and we will eventually prove their conjecture.

**Theorem 0.1.** If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane, and  $3 \leq k \leq L^{1/2}$ , then  $|P_k(\mathfrak{L})| \lesssim L^{3/2}k^{-2}$ .

Recall that  $P_k(\mathfrak{L})$  is the set of points lying in  $\geq k$  lines of  $\mathfrak{L}$ .

Today, we will prove this result for k = 3. The proof is based on the new techniques we have developed: degree reduction and special points (critical points and flat points).

**Theorem 0.2.** (Elekes-Kaplan-Sharir) Suppose  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane. If  $B \geq L^{1/2}$ , then  $|P_3(\mathfrak{L})| \leq CBL$ .

Taking  $B = L^{1/2}$ , we get the case k = 3 of the conjecture.

As in the proof of the joints theorem, we will try to prove that there is always one line with not too many points of  $P_3$  on it.

**Lemma 0.3.** Suppose  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane, with  $B \geq L^{1/2}$ . Then one of the lines contains  $\leq CB$  points of  $P_3(\mathfrak{L})$ .

Given this lemma, the theorem follows by induction on the number of lines.

#### 1. The proof of the main Lemma

We will do a proof by contradiction. We let  $C_0$  be a large constant that we can choose later. We assume that each line of  $\mathfrak{L}$  contains  $> C_0 B$  points of  $P_3$ .

#### Step 1. Degree reduction

By the degree reduction theorem, there is a non-zero polynomial P that vanishes on all the lines of  $\mathfrak{L}$  with degree  $\lesssim L(C_0B)^{-1}$ . By choosing  $C_0$  sufficiently large, we can assume that

$$d := degP \le (1/100)LB^{-1} \le (1/100)L^{1/2}$$
.

We can also assume that P is square free.

# Step 2. The points of $P_3$ are special points for P

Recall that a point  $x \in Z(P)$  is called special if it is either critical or flat. Special points can be detected by polynomials. Last lecture, we defined a vector of polynomials SP(x) so that x is special if and only if P(x) = 0 and SP(x) = 0. Each component of SP(x) has degree  $\leq 3d - 4$ , and there are nine components.

We claim that each point of  $P_3$  is either critical or flat. Let  $x \in P_3$ . By definition, x lies in (at least) three lines of  $\mathfrak{L}$ . Pick three lines  $l_1, l_2, l_3$  containing x. We know that P = 0 on these three lines. If the three lines are not coplanar, then we saw in our study of joints that x is a critical point of P. The reason is that  $\partial_{v_i} P(x) = 0$  where  $v_i$  are the tangent directions to the three lines. Since these directions form a basis of  $\mathbb{R}^3$ ,  $\nabla P(x) = 0$ . Suppose now that x is not a critical point of P. In this case, we will prove that x is a flat point of Z(P).

We see that the lines  $l_1, l_2, l_3$  must lie in a plane. We still have  $\partial_{v_i} P(x) = 0$  for each i, and so the lines  $l_i$  must all lie in the tangent plane to Z(P) at x. Next we perform a translation and rotation so that x is moved to 0 and Z(P) is locally described as a graph

$$x_3 = f(x_1, x_2) = Q(x_1, x_2) + O(|x_1| + |x_2|)^3$$
, Q homogeneous of degree 2.

The translation and rotation moves the lines  $l_i$  to lines  $\tilde{l}_i$  which contain 0 and lie in the plane  $x_3 = 0$ . Since these lines lie in the image of Z(P), we see that f vanishes on them. Therefore, Q must vanish on them. So we see that the quadratic form Q vanishes on three lines through 0 in  $\mathbb{R}^2$ . Now by the vanishing lemma, Q must also vanish on any line that passes through the three lines at distinct points, and it quickly follows that Q = 0. This means that the point x is flat.

Each point of  $P_3$  is either critical or flat, and so SP(x) = 0 for each  $x \in P_3$ .

#### Step 3. The lines of $\mathfrak L$ are special lines for P

Each line of  $\mathfrak{L}$  contains  $\geq C_0B \geq L^{1/2}$  points of  $P_3$ . On the other hand, the polynomial P has degree  $\leq (1/100)L^{1/2}$ . The polynomials in SP have degree  $\leq 3d-4 \leq (3/100)L^{1/2}$ . Each polynomial SP vanishes at  $\geq L^{1/2}$  points on each line of  $\mathfrak{L}$ . Therefore, SP=0 on each line of  $\mathfrak{L}$ .

## Step 4. Almost all the lines of $\mathcal{L}$ must lie in planes of Z(P)

Suppose that  $P = \prod_j P_j$  with  $P_j$  irreducible. Some of the  $P_j$  may be linear, and each linear factor corresponds to a plane in Z(P). Let  $\pi_1, ..., \pi_T$  be all the planes in Z(P), with  $T \leq d \leq (1/100)L^{1/2}$ . Next we consider how special lines of Z(P) relate to special lines of the  $Z(P_j)$ .

**Lemma 1.1.** Suppose that  $l \subset Z(P)$  is a special line, i.e. SP = 0 on l. Then either l lies in  $Z(P_i)$  for two different j, or else l is a special line of  $Z(P_i)$  for some j.

(We note that if l lies in  $Z(P_j)$  for two different j, then  $\nabla P = 0$  on l, so l is a special line.)

*Proof.* Let l be a special line of Z(P). Suppose that l lies in  $Z(P_{j_1})$  but l does not lie in any other  $Z(P_j)$ . We have to show that l is a special line of  $Z(P_{j_1})$ . First, suppose that l is a critical line of Z(P) - in other words,  $\nabla P = 0$  on l. We expand  $\nabla P$  using the Liebniz formula:

$$\nabla P = \sum_{j_0} (\nabla P_{j_0}) \prod_{j \neq j_0} P_j.$$

Along the line l,  $P_{j_1} = 0$ , and so the sum simplifies to  $(\nabla P_{j_1}) \prod_{j \neq j_1} P_j$ . At all but finitely many points of l, the product does not vanish, and so  $\nabla P_{j_1}$  must vanish. By the vanishing lemma,  $\nabla P_{j_1} = 0$  on l.

Next, suppose that l is not a critical line and is a flat line. For almost every point  $x \in L$ , Z(P) is a smooth manifold near x and Z(P) is flat at x. But for almost every point x in l,  $Z(P) = Z(P_{j_1})$  in a small neighborhood of x. So  $Z(P_{j_1})$  is flat at almost every point  $x \in l$ . Therefore,  $SP_{j_1}(x) = 0$  for almost every  $x \in l$ . By the vanishing lemma,  $SP_{j_1} = 0$  on l.

Now we count the number of special lines of various types, using the Bezout theorem. The number of lines that lie in at least two  $Z(P_j)$  is  $\leq \sum_{j_1,j_2} (deg P_{j_1}) (deg P_{j_2}) \leq d^2 < 10^{-4} L$ .

If  $P_j$  is not a linear polynomial, then we proved last time that the number of special lines in  $Z(P_j)$  is  $\leq 3(degP_j)^2$ . Therefore, the number of special lines in  $Z(P_j)$  for all the  $P_j$  with  $degP_j \geq 2$  is  $\leq 3\sum_j (degP_j)^2 \leq 3d^2 \leq 3 \cdot 10^{-4}L$ .

Therefore, at least (99/100)L lines of  $\mathfrak{L}$  must lie in the planes  $\pi_1, ..., \pi_T$ , with  $T \leq d \leq (1/100)L/B$ . By the pigeon hole principle, one of the planes contains at least 99B lines of  $\mathfrak{L}$ . But we assumed that each plane contains  $\leq B$  lines of  $\mathfrak{L}$ . This contradiction proves the lemma.

#### 2. What happens for large k?

We will eventually prove the following theorem.

If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane and if  $3 \leq k \leq L^{1/2}$ , then  $|P_k(\mathfrak{L})| \lesssim L^{3/2}k^{-2}$ .

Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane. We would like to show that one of the lines contains  $\leq L^{1/2}k^{-1}$  points of  $P_k(\mathfrak{L})$ . (For heuristic purposes, suppose that each line had  $L^{1/2}k^{-1}$  points of  $P_k$ . Then we would have

 $L^{3/2}k^{-1}$  incidences between  $\mathfrak{L}$  and  $P_k$ . But each point of  $P_k$  lies on  $\geq k$  lines, so we would have  $\leq L^{3/2}k^{-2}$  points of  $P_k$ .)

Let us suppose that each line contains  $\geq A$  points of  $P_k$ . For which values of A can we hope to run the argument above? In order for the argument to work, it's crucial to be able to do degree reduction. Let us do a heuristic calculation of how big A needs to be to do degree reduction.

Let d be a degree that we can pick later. We find a non-zero polynomial P of degree  $\leq d$  that vanishes on  $(1/10)d^2$  random lines of  $\mathfrak{L}$ . Let l be another line of  $\mathfrak{L}$ . We want to estimate the number of points where this line intersects the random lines above. The line l contains A points of  $P_k$ . Each of these points lies in  $\geq k$  lines of  $\mathfrak{L}$ , and so l intersects  $\geq Ak$  lines of  $\mathfrak{L}$ . Each line of  $\mathfrak{L}$  has a probability  $\sim d^2/L$  of being chosen in the list of random lines. Therefore, the number of lines of  $\mathfrak{L}$  which intersect l is typically  $Akd^2/L$ . If this number is l then the number of distinct intersection points is typically of the same order of magnitude. The number of intersection points is capped at l so we have

$$\mathbb{E}|\{x \in l | x \in \text{ the } d^2 \text{ random lines }\}| \gtrsim \min(Akd^2L^{-1}, A).$$

We can do degree reduction only if this expected number is >d. So to do degree reduction we need  $Akd^2L^{-1}>d$  and A>d. The first inequality is equivalent to  $d>LA^{-1}k^{-1}$ . So to do degree reduction, we need  $A>d>LA^{-1}k^{-1}$  and hence  $A>L^{1/2}k^{-1/2}$ . If A is, say,  $\geq 10^5L^{1/2}k^{-1/2}$ , then we can do degree reduction down to degree  $d\sim LA^{-1}k^{-1}$ . The rest of the argument above works. Filling in the details, it is possible to prove the following fairly weak estimate:

**Proposition 2.1.** Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane. Suppose  $3 \leq k \leq L^{1/2}$ . Then one of the lines contains  $\lesssim L^{1/2}k^{-1/2}$  points of  $P_k$ .

Then, by a somewhat tricky induction argument we get

**Corollary 2.2.** Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane. Suppose  $3 \leq k \leq L^{1/2}$ . Then  $|P_k| \lesssim L^{3/2}k^{-3/2}$ .

This estimate is significantly weaker than the theorem we will eventually prove. What is the source of our difficulties, and why are we getting stuck at this point?

It's interesting to consider the example of lines in finite fields. Let  $\mathfrak L$  be the set of all the lines in  $\mathbb F_q^3$ . The total number of lines is  $L \sim q^4$ . The number of lines in any plane is  $\sim q^2 \leq L^{1/2}$ . Each point of  $\mathbb F^q$  lies in  $k \sim q^2$  lines. Therefore  $|P_k(\mathfrak L)| = q^3 \sim L^{3/2} k^{-3/2}$ .

This situation is similar to the Szemerédi-Trotter theorem. The Szemerédi-Trotter theorem is true for lines in  $\mathbb{R}^2$ . But it's false over finite fields, in particular if we

consider the set of all lines in  $\mathbb{F}_q^2$ . The known proofs all somehow use the topology of  $\mathbb{R}^2$ . Theorem 0.1 has very similar difficulties.

On the other hand, the case k=3 of Theorem 0.1 has a nice proof with the polynomial method. This case seems at least as hard as the joints problem, and no one knows how to approach it (so far) without the polynomial method.

So the problem combines the difficulties of the Szemerédi-Trotter theorem and the joints theorem. To prove it, we will need to combine some type of topological argument as in the ST theorem with some type of polynomial argument as in the joints theorem. Our next main goal in the course is to see how to get these two methods to cooperate.

2.1. On the tricky induction. Here we describe, for reference, the slightly tricky inductive argument to get the corollary from the proposition. Actually, to do the induction we need a slightly more general proposition.

**Proposition 2.3.** Suppose that  $3 \le k \le 10L^{1/2}$ . Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane, with  $B \geq L^{1/2}$ . Then one of the lines of  $\mathfrak{L}$  contains  $\lesssim Bk^{-1/2}$  points of  $P_k$ .

Proof sketch. Suppose that each line contains  $\geq A$  points of  $P_k$ . If  $A \geq 10^5 L^{1/2} k^{-1/2}$ . then we can do degree reduction to fit all the lines in Z(P) for P of degree  $\leq$  $CLA^{-1}k^{-1}$ . This degree is  $\leq (1/100)A$  and  $\leq (1/100)L^{1/2}$ . All the points of  $P_k$ are special points of Z(P). Since A > 3degP, all the lines are special lines. Since  $degP \leq (1/100)L^{1/2}$ , Z(P) only has room for < (1/100)L special lines except in the planes of Z(P). So almost all the lines actually lie in  $\leq d$  planes. One plane must contain at least  $(1/2)L/d \gtrsim Ak$  lines. Therefore,

$$A \leq \min(L^{1/2}k^{-1/2}, Bk^{-1}) \leq Bk^{-1/2}.$$

Using this proposition and induction, we get the following corollary.

Corollary 2.4. Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane, where  $B > L^{1/2}$ . Suppose that  $3 < k < L^{1/2}$ . Then  $|P_k| \le LBk^{-3/2}$ .

Proof sketch. Remove the lines one at a time using the last lemma, until we get down to  $(1/100)k^2$  lines. At this point, we know that  $|P_{k/2}| \lesssim k$  by the counting bound. At each step, we remove a line that intersects  $\lesssim LBk^{-1/2}$  points of  $P_{k/2}$ . By the end, all but k point of  $P_k$  must have had k/2 lines removed. So we see

$$(|P_k(\mathfrak{L})| - Ck)k \lesssim L(Bk^{-1/2}).$$
 Hence  $|P_k(\mathfrak{L})| \lesssim LBk^{-3/2}$ .

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## TAKING STOCK

In today's lecture, we are going to take stock of where we've come from and discuss where we're going. What were the difficulties in the problems? What were the main things we learned? What is the next challenge?

In the last lecture, we proved the following theorem about 3-rich points for sets of lines in  $\mathbb{R}^3$ :

**Theorem 0.1.** Let  $\mathfrak{L}$  be a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane. If  $B \geq L^{1/2}$ , then  $|P_3(\mathfrak{L})| \lesssim BL$ .

The proof involved three tools that we developed ahead of time: flat points and lines, degree reduction, and Bezout's theorem. Putting it all together, it is the longest proof we have studied so far in this course. I want to take a little time to put it in context more. We'll look at some examples. Also, we'll try to describe the nature of the difficulty in proving the theorem. Why does it take this much work to prove the theorem?

We begin with a simple example. A collection of B lines in a plane can have  $\sim B^2$  3-rich points. For example, we can take a grid with B/3 evenly spaced vertical lines, B/3 evenly spaced horizontal lines, and B/3 evenly spaced diagonal lines. In this grid, we get  $\geq B^2/20$  3-rich points. Next, if we choose L/B generic planes, and put B lines in each plane, we get an arrangement of lines with  $\sim BL$  3-rich points. We can arrange that there will be  $\leq B$  lines in any plane by taking each configuration of B lines and rotating and translating it generically.

### 1. What makes the theorem hard?

To get a feel for the difficulty, let's consider the following much weaker corollary.

**Proposition 1.1.** Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\geq L^{1.99}$  3-rich points. Then, there is a plane that contains  $\geq 3$  lines of  $\mathfrak{L}$ .

To prove the proposition, the key question is "how can we find this plane"? Let's mention one possible way of finding a plane with three lines in it. Let us look at the incidence matrix of  $P_3(\mathfrak{L})$  with  $\mathfrak{L}$ . If we find a "triangle" in the incidence matrix, then we automatically get three lines in a plane. A triangle is a set of three lines  $l_1, l_2, l_3 \in \mathfrak{L}$ , and three points  $x_1, x_2, x_3 \in P_3$  so that each line contains exactly two of the three points. In this case, the points  $x_1, x_2, x_3$  lie in a unique plane  $\pi$  which contains all three lines.

We can try to find a triangle in the incidence matrix. What do we know about the incidence matrix. By hypothesis, it has dimensions  $L \times P$  with  $P \ge L^{1.99}$ , and each point lies in at least three lines. Also, any two lines intersect in at most one point. Just based on this information, does the matrix need to have a triangle? The answer to this question is no. It comes from an interesting example that was explained to me by Andrew Suk.

**Proposition 1.2.** Fix any  $\epsilon > 0$ . For all sufficiently large L, we can find a set  $\mathfrak{L}$  of L lines in  $\mathbb{R}^2 \subset \mathbb{R}^3$  and a set of 3-rich points  $P \subset P_3(\mathfrak{L})$  so that  $|P| \geq L^{2-\epsilon}$  and yet the incidence matrix of P and  $\mathfrak{L}$  contains no triangle.

The construction is based on an important example of Behrend about 3-term arithmetic progressions. Recall that an arithmetric progression of length r is a sequence of numbers a, a+d, a+2d, ..., a+(r-1)d. Behrend's example is concerned with the question, "how large is the largest subset of the integers from 1 to N with no 3-term arithmetric progression?"

**Theorem 1.3.** (Behrend, 1946) Fix any  $\epsilon > 0$ . For any N sufficiently large, there is a subset of [1...N] with  $\geq N^{1-\epsilon}$  elements and with no 3-term arithmetic progression.

We'll discuss Behrend's construction some time later... Using it, we now give the proof of Proposition 1.2.

Proof. We describe the lines and the points. The lines are vertical, horizontal, and diagonal lines in a grid. We take vertical lines x=a for a=1...S. We take horizontal lines y=b for b=1...S. And we take diagonal lines x-y=c for c=-S,...,S. We have a total of L=4S+1 lines. We let X denote the  $S\times S$  grid of lattice points  $\{(a,b)\in\mathbb{Z}^2|1\leq a,b\leq S\}$ . Each point of X lies in exactly three lines of  $\mathfrak{L}$ . The set X is the set of all 3-rich points of  $\mathfrak{L}$ . It has size  $S^2\sim L^2$ , but the incidence matrix of X with  $\mathfrak{L}$  contains many triangles. We will pare down X slightly to a subset  $P\subset X$  so that the incidence matrix of P with  $\mathfrak{L}$  contains no triangles. The key idea of the proof is that Behrend's construction lets us do this paring.

By Behrend's construction, we can find a subset  $P_0 \subset [S/2,...,3S/2]$  so that  $|P_0| \ge S^{1-\epsilon}$  and yet  $P_0$  contains no 3-term arithmetic progression. We define the set  $P := \{(a,b) \in X | a+b \in P_0\}$ . For each  $d \in [S/2,...,3S/2]$ , the set of  $(a,b) \in X$  so that a+b=d has  $\ge S/2$  elements, and so  $|P| \ge (1/2)S^{2-\epsilon} \ge cL^{2-\epsilon}$ .

Consider a triangle in the incidence matrix of X and  $\mathfrak{L}$ . The horizontal lines are pairwise disjoint, as are the vertical lines and the diagonal lines. Therefore, the triangle must consist of one horizontal line, one vertical line, and one diagonal line. Let  $x_i = (a_i, b_i) \in X$  be the vertices of the triangle. We have to show that the three vertices are not all in P. It suffices to show that  $d_i = a_i + b_i$  form a 3-term arithmetic progression. This follows by the geometry of the triangle.

It's probably best at this moment to draw your own picture. But for completeness, we write down the details. Suppose that  $x_1$  is the lower-left vertex,  $x_2$  is the right angle, and  $x_3$  is the upper-right vertex. We have  $(a_2, b_2) = (a_1, b_1 + d)$ . And  $(a_3, b_3) = (a_2 + e, b_2)$ . But because the diagonal line is at a 45 degree angle, we see that the triangle is isosceles and so e = d. A short computation shows that  $a_1 + b_1, a_2 + b_2, a_3 + b_3$  make a 3-term arithmetic progression.

Therefore, we probably need a different idea to locate a plane with three lines in it. We can formulate this issue more precisely using the axioms of incidence theory (for points, lines, planes in three dimensions). In these axioms, we have a set of points, and each line or plane is a subset of the points, and the whole structure obeys a list of axioms. We don't give the whole list of axioms here, but we give the flavor by mentioning two examples. 1. For any two points, there is a unique line containing the two points. 2. If three points don't all lie on a line, then there is a unique plane containing the three points. Etc. Now we may ask whether Theorem 0.1 or Proposition 1.1 hold more generally in the axioms of incidence theory. I believe that the answer is 'no' and that Suk's construction can be modified to prove the following

**Conjecture 1.4.** Fix any  $\epsilon > 0$ . Then for arbitrarily large numbers L, the following holds: there is a set of points, lines, and planes obeying the incidence axioms, and a subset  $\mathfrak{L}$  of the lines, so that  $|\mathfrak{L}| = L$ ,  $|P_3(\mathfrak{L})| \geq L^{2-\epsilon}$  and yet each plane contains  $\leq 2$  lines of  $\mathfrak{L}$ .

Theorem 0.1 depends on some other structure about lines in  $\mathbb{R}^3$  which is not captured in the incidence axioms. What structure is it? Our proof is based on algebraic structure.

There's a fairly short proof of Proposition 1.1 using reguli. If  $\mathfrak{L}$  has  $L^{1.99}$  3-rich points, then it follows from Problem Set 2 that there is a regulus or plane containing  $\gtrsim L^{.99}$  lines of  $\mathfrak{L}$ . Since the lines inside a regulus cannot make any 3-rich points, it's not too hard to push a bit farther and prove that there is a plane containing  $\gtrsim L^{.99}$  lines of  $\mathfrak{L}$ . Reguli provide an additional structure which is not included in the incidence axioms. Basically this structure amounts to including degree 2 surfaces as well as planes.

The technique of reguli cannot easily push all the way down to  $L^{3/2}$  3-rich points. To try to find a regulus with many lines, we can look at the intersection matrix of the lines of  $\mathfrak{L}$ . If this matrix has a  $3 \times A$  minor of all 1's, then we can find  $\sim A$  lines which lie in a common plane, lie in a common regulus, or pass through a common point. But by Brown's construction, the intersection matrix may have no  $3 \times 3$  minor of all 1's and still have  $L^{5/3}$  1's. It's hard to rule out that we may have  $\sim L^{5/3}$  3-rich points points but the intersection matrix may have no  $3 \times 3$  minor of all 1's.

In our proof with the polynomial method, we include in the story not just surfaces of degree 2 but surfaces of all degrees. With this algebraic structure, we are able to

prove Theorem 0.1, which holds as long as the number of 3-rich points is at least a large constant times  $L^{3/2}$ . It's actually not clear what happens below this threshold (i.e. for  $B < L^{1/2}$  in the statement of the theorem). The polynomial method (as we've been using it) stops working, but I don't know any examples with  $P_3$  significantly larger than BL.

### 2. The big picture

We have mostly been talking about estimates for the incidences of lines in  $\mathbb{R}^2$  or  $\mathbb{R}^3$ . We can usually begin on any given problem by thinking about basic facts about incidences, such as "two points lie on a unique line". These facts lead to some basic estimates, but in many cases the basic estimates are far from sharp. To improve them, we need some subtler facts about lines. We have followed two main approaches.

- (1) Use the topological structure of Euclidean space. This approach leads to the crossing number lemma, the Szemerédi-Trotter theorem, and other applications.
- (2) Use the algebraic structure of Euclidean space. This approach leads to the joints theorem and Theorem 0.1 above.

How can we recongnize/guess which tool is good for which problem? In the case of the Szemerédi-Trotter theorem, the need for topological considerations is motivated by the example of lines in finite fields. The Szemerédi-Trotter theorem fails badly if we let  $\mathcal{L}$  be the set of all lines in  $\mathbb{F}_q^2$ . Finite fields have most of the algebraic structure that we see in  $\mathbb{R}^2$ , but they're very different topologically.

It's less clear to me how to recognize the need for algebraic structure. For example, I still find it kind of surprising that there is not a very different proof of the joints theorem - and such a proof may indeed exist. I think one can probably demonstrate that these theorems don't follow just from 'incidence axioms'. (Of course Szemerédi-Trotter also does not follow just from incidence axioms.) In practice, if a certain question seems similar to the joints theorem or finite field Kakeya..., then it's a candidate for the polynomial method. Also, if it's possible to do some degree reduction, then the problem is a good candidate for the polynomial method.

So far, these two techniques have been complementary. We can't prove the Szemerédi-Trotter theorem with just the polynomial method. If we try to find a low-degree polynomial on the points, then we get a degree which is larger than the number of points on each line, and then we can't do anything with it. If we try to find a low degree polynomial that vanishes on the lines, since we are in the plane, we just get a degree L polynomial and it doesn't lead to any interesting information about the points. There is no possibility of doing degree reduction – any set of L lines in

the plane has degree exactly L. This may suggest that the polynomial method is not well suited to study questions about lines in the plane.

On the other hand, the topological methods have had only limited success in proving estimates for the joints problem. The basic issue is that curves in  $\mathbb{R}^3$  do not divide space into components, and so the whole set up is totally different. There are papers using the topological approach to prove interesting estimates about the joints problem – the best estimate proven this way is something like  $J \leq L^{1.62\cdots}$ . The method involves taking lines or curves in space and projecting them onto planes, and then using the crossing number lemma to study the projections. It seems difficult to capture all the 3-dimensional structure that we're interested in with these two-dimensional projections...

So we have studied two methods. They are useful in different situations – in some sense they deal with different difficulties. However, there are problems that involve both types of difficulties.

## 3. The next goal

Our next goal is the following theorem. It was conjectured by Elekes and Sharir and proven by Katz and G.

**Theorem 3.1.** Suppose that  $\mathfrak{L}$  is a set of lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane. Suppose that  $3 \leq k \leq L^{1/2}$ . Then  $|P_k| \lesssim L^{3/2}k^{-2}$ .

This theorem involves both types of difficulties. For large values of k, it is false over finite fields. In particular, let us consider the set of all lines in  $\mathbb{F}_q^3$ . We have  $|\mathfrak{L}| \sim q^4$ . The number of lines in each plane is  $\sim q^2 \leq L^{1/2}$ . Each point lies in  $\geq q^2$  lines. Therefore, taking  $k = q^2 \leq L^{1/2}$ , we have  $|P_k| = q^3 \sim L^{3/2}k^{-3/2}$ . We see indeed that our theorem is false over finite fields. The example is reminiscent of the Szemerédi-Trotter theorem, and it suggests we need to use the topological structure of  $\mathbb{R}^3$ . If we try to adapt the algebraic proof of Theorem 0.1 to large k, then the method gives the upper bound  $|P_k| \lesssim L^{3/2}k^{-3/2}$ , matching the example in finite fields. Moreover it looks plausible that the proof of Theorem 0.1 can be extended to finite fields, and that the same results hold there.

On the other hand, if we look for a purely topological proof, it seems hard to prove the case k = 3 that we already proved with the polynomial method.

Our next goal is to prove this theorem by combining the polynomial method and the topological method.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## THE CELLULAR METHOD

In this lecture, we introduce the cellular method as an approach to incidence geometry theorems like the Szemerédi-Trotter theorem. The method was introduced in the paper "Combinatorial complexity bounds for the arrangements of curves and spheres" by Clarskon, Edelsbrunner, Guibas, Sharir, and Welzl (Discrete Comput. Geom. (1990) 5, 99-160). In the next lectures, we will combine ideas from the cellular method with polynomial method.

Our goal here is to describe some of the main ideas of the cellular method as context. We will not give complete proofs but instead sketch the proofs and do heuristic calculations. As a model problem, we consider using the cellular method to prove the Szemerédi-Trotter theorem. (It has many other applications, and we will mention some of them later.)

Suppose that we have a set  $\mathfrak{L}$  of L lines in  $\mathbb{R}^2$  and we fix a number k in the range  $2 \leq k \leq L^{1/2}$ . We wish to bound the number of k-rich points  $|P_k|$ .

The cellular method is a divide-and-conquer strategy. We cut the plane into cells. We use elementary estimates to control the number of k-rich points in each cell, and if the points and/or lines are well-divided among the cells, then we get a stronger estimate by dividing into pieces in this way.

## 1. Good cell decompositions

Suppose we take d lines in  $\mathbb{R}^2$  (not necessarily in  $\mathfrak{L}$ ). The complement of the d lines has  $\lesssim d^2$  connected components, which we call cells. If the lines are in general position, the number of cells is  $\sim d^2$ . Each line enters  $\leq d+1$  cells. So each line of  $\mathfrak{L}$  enters only a small fraction of all the cells (at most  $\lesssim 1/d$ ).

In each cell, we will employ a simple counting estimate for k-rich points, which we proved in the first lecture on incidence geometry.

**Lemma 1.1.** (Counting bound) If  $\mathfrak{L}$  is a set of L lines, and if  $L \leq k^2/4$ , then  $|P_k| \leq 2L/k$ .

Our strategy is to emply the counting bound in each cell and add up the results. If all the lines go through a single cell and all the k-rich points lie in that cell, then we haven't gained anything by our cell division. The divide-and-conquer algorithm works well if each cell is roughly equal. We consider two precise conditions.

A Even distribution of points. We suppose that all the k-rich points are in the open cells, and the number of k-rich points in each open cell is  $\leq 10|P_k|/d^2$ .

B Even distribution of lines. We suppose that all the k-rich points are in the open cells, and the number of lines of  $\mathfrak{L}$  that enter each cell is  $\leq 10L/d$ .

In each case, if we are able to choose d, we will be able to prove the Szemerédi-Trotter bound  $|P_k| \lesssim L^2 k^{-3}$ . Let us examine how the argument would go in each case. We let  $O_i$  denote the open cells. We let  $L_i$  denote the number of lines of  $\mathfrak{L}$  which intersect  $O_i$ . We let  $N_i$  be the number of k-rich points in  $O_i$ .

# Case A.

**Lemma 1.2.** If  $d \ge 160Lk^{-2}$ , and if condition A. holds, then  $|P_k| \le 8Ldk^{-1}$ .

*Proof.* We have the following bounds for  $N_i$ . By the counting bound, if  $L_i \leq (1/4)k^2$ , then  $N_i \leq 2L_ik^{-1}$ . Also, by assumption,  $N_i \leq 10|P_k|d^{-2}$  for all i. We call a cell 'big' if  $L_i \geq (1/4)k^2$ . We can bound  $|P_k| = \sum N_i$  in terms of the number of big cells as follows:

$$|P_k| = \sum_i N_i \le (\sum_i 2L_i k^{-1}) + (\text{\# big cells}) \cdot 10d^{-2}|P_k|.$$

We also know that  $\sum_i L_i \leq L(d+1)$  because each line enters  $\leq d+1$  open cells. We can plug this in to the first term of the right-hand side. Also, we see that the number of big cells is at most  $\sum L_i/(k^2/4) \leq 8dLk^{-2}$ . Therefore we get the following inequality:

$$|P_k| \le 4Ldk^{-1} + 80Ld^{-1}k^{-2}|P_k|.$$

If the coefficient  $80Ld^{-1}k^{-2}$  is  $\geq 1$ , this inequality is vacuous. But as long as  $80Ld^{-1}k^{-2} \leq 1/2$ , we can shift the term  $80Ld^{-1}k^{-2}|P_k|$  to the other side. Let us assume that  $80Ld^{-1}k^{-2} \leq 1/2$ . This is equivalent to  $d \geq 160Lk^{-2}$ . Under this assumption, we see that  $|P_k| \leq 8Ldk^{-1}$ .

Now suppose we were able to arrange d lines in the plane obeying condition A. for any d. We could choose  $d = 160Lk^{-2}$ , and we would see that  $|P_k| \leq 2000L^2k^{-3}$ , the Szemerédi-Trotter bound.

# Case B.

This case is similar and even a little easier.

**Lemma 1.3.** If  $d \ge 40Lk^{-2}$ , and if condition B. holds, then  $|P_k| \le 4dLk^{-1}$ .

Proof. Since we have assumed condition B,  $L_i \leq 10L/d$ . If  $10L/d \leq (1/4)k^2$ , then we can apply the counting bound to deduce that  $N_i \leq 2L_i/k$ . Then we see that  $|P_k| = \sum_i N_i \leq 2k^{-1} \sum_i L_i \leq 2L(d+1)/k \leq 4dLk^{-1}$ .

Now suppose we were able to arrange d lines in the plane obeying condition B. for any d. We could choose  $d = 40Lk^{-2}$ , and we would see that  $|P_k| \leq 200L^2k^{-3}$ , the Szemerédi-Trotter bound.

This raises the question, "can we actually find d lines in the plane obeying condition A or B?" We explore this in the next section.

#### 2. Are there good cell decompositions?

Can we find d lines obeying condition A? Morally the answer is no. Here is a more precise related question.

**Question 2.1.** Given a set of N points in the plane, and an integer  $d \leq N^{1/2}$ , can we find d lines which cut the plane into cells so that each open cell contains  $\leq 1000N/d^2$  points?

The answer to this question is definitely no. Let  $\gamma$  be a closed strictly convex curve, such as a circle. Pick N points on this curve. Pick  $d \sim N^{1/2}$ . Consider d lines in the plane. Each line contains  $\leq 2$  of our points, so only a small fraction of the points are in the lines. More importantly, each line intersects  $\gamma$  in at most 2 points. Therefore, the lines cut  $\gamma$  into  $\leq 2d$  pieces. One of those pieces must contain  $\geq (N-2d)/(2d) \gtrsim N^{1/2}$  points of our set. This badly violates our goal. We wanted to find  $\sim N^{1/2}$  lines that cut  $\mathbb{R}^2$  into cells with  $\lesssim 1$  point in each cell – but in fact one of the cells must have  $\gtrsim N^{1/2}$  points in it.

Next we ask: Can we find d lines obeying condition B? Morally the answer is yes (although I'm not sure if the answer is literally yes). The main idea is to choose a subset of d random lines from  $\mathfrak{L}$ . If we do this, a typical edge of the cell decomposition will intersect  $\lesssim L/d$  lines. To get a rough idea of what's happening, consider a line  $l \in \mathfrak{L}$ . For simplicity, let's suppose that it intersects all the other lines of  $\mathfrak{L}$  at different points. The intersection points are L-1 points along  $\mathfrak{l}$ . Now we randomly pick d of the L lines - so essentially we randomly pick d of the intersection points. Now the line l is cut into the segments betweent the selected points. The average number of points in each segment is L/d, and the probability that a given segment has  $\geq KL/d$  points falls off exponentially in K. So very few edges intersect more than 1000L/d lines of  $\mathfrak{L}$ . Next we consider the cells of our decomposition. If a cell has  $\leq 1000$  edges, and each edge intersects  $\leq 1000L/d$  lines of  $\mathfrak{L}$ , then the number of lines of  $\mathfrak{L}$  which intersect the cell is  $\leq 10^6L/d$ . The cell decomposition may have a few cells with > 1000 edges, but these are also pretty rare.

Here's another perspective. Suppose we first choose d/2 random lines of  $\mathfrak{L}$  and look at the resulting cells. Suppose that one of the cells intersects > KL/d lines of  $\mathfrak{L}$  for a very large K. When we choose d/2 more random lines of  $\mathfrak{L}$ , we are very likely to choose one of the lines intersecting this popular cell. The probability that we will not choose any of these lines is < exp(-cK). As we keep adding random lines,

popular cells are likely to be cut down to size. If we make this analysis quantitative, I believe we find that the fraction of cells  $O_i$  where  $L_i \geq KL/d$  is  $\lesssim exp(-cK)$ . So this random decomposition nearly obeys condition B.

If the heuristics above are correct, we can arrange that every cell obeys  $L_i \leq C(\log L)L/d$ , and this implies the S-T estimate up to logarithmic losses. In order to prove the real Szemerédi-Trotter theorem with the cellular method, one has to subdivide the popular cells by adding some line segments. This requires some care, and we don't discuss the details here.

## 3. Good cell decompositions in three dimensions

Having warmed up in two dimensions, now we consider a set  $\mathfrak{L}$  of L lines in  $\mathbb{R}^3$ . We consider d planes in  $\mathbb{R}^3$  which typically divide  $\mathbb{R}^3$  into  $\sim d^3$  cells. Each line can only enter  $\leq d+1$  open cells, so each line enters only a small fraction of the cells. If the lines and/or points are evenly distributed among the cells, then we get a good bound for the number of k-rich points. We again consider two precise conditions.

- A Even distribution of points. We suppose that all the k-rich points are in the open cells, and the number of k-rich points in each open cell is  $\leq 10|P_k|/d^3$ .
- B Even distribution of lines. We suppose that all the k-rich points are in the open cells, and the number of lines of  $\mathfrak{L}$  that enter each cell is  $\leq 10L/d^2$ .

In either case, we get good bounds for  $P_k$  especially if we can choose d.

**Lemma 3.1.** If  $d \ge 13L^{1/2}k^{-1}$ , and if condition A. holds, then  $|P_k| \le 8Ldk^{-1}$ .

*Proof.* We have the following bounds for  $N_i$ . By the counting bound, if  $L_i \leq (1/4)k^2$ , then  $N_i \leq 2L_ik^{-1}$ . Also, by assumption,  $N_i \leq 10|P_k|d^{-3}$  for all i. We call a cell 'big' if  $L_i \geq (1/4)k^2$ . We can bound  $|P_k| = \sum N_i$  in terms of the number of big cells as follows:

$$|P_k| = \sum_i N_i \le (\sum_i 2L_i k^{-1}) + (\# \text{ big cells}) \cdot 10d^{-3}|P_k|.$$

We also know that  $\sum_i L_i \leq L(d+1)$  because each line enters  $\leq d+1$  open cells. We can plug this in to the first term of the right-hand side. Also, we see that the number of big cells is at most  $\sum L_i/(k^2/4) \leq 8dLk^{-2}$ . Therefore we get the following inequality:

$$|P_k| \le 4Ldk^{-1} + 80Ld^{-2}k^{-2}|P_k|.$$

If the coefficient  $80Ld^{-2}k^{-2}$  is  $\geq 1$ , this inequality is vacuous. But as long as  $80Ld^{-2}k^{-2} \leq 1/2$ , we can shift the term  $80Ld^{-2}k^{-2}|P_k|$  to the other side. Let us assume that  $80Ld^{-2}k^{-2} \leq 1/2$ . This is implied by  $d \geq 13L^{1/2}k^{-1}$ . Under this assumption, we see that  $|P_k| \leq 8Ldk^{-1}$ .

Now suppose that for any  $d \ge 1$  we could choose d hyperplanes so that A holds. We would choose  $d \sim L^{1/2}k^{-1}$ , and then we would get the bound  $|P_k| \lesssim L^{3/2}k^{-2}$ .

Condition B is similar. If we could find  $d = 20L^{1/2}k^{-1}$  planes obeying condition B, then it would again follow that  $|P_k| \lesssim L^{3/2}k^{-2}$ .

This looks like a promising route towards our target theorem:

**Theorem 3.2.** If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane and  $3 \leq k \leq L^{1/2}$ , then  $|P_k| \lesssim L^{3/2}k^{-2}$ .

4. Are there good cell decompositions in three dimensions?

So we are led to the following question.

**Question 4.1.** If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in a plane, and if  $d \leq L^{1/2}$ , can we find d planes obeying condition A or condition B?

We haven't used or mentioned the restriction  $\leq L^{1/2}$  lines in any plane so far. We take a moment to see how it may be relevant. Suppose we consider L lines which all lie in a plane  $\pi$ . If we include the plane  $\pi$  among the d planes, then the planes will include all the k-rich points which completely violates condition A or B. Each other plane intersects  $\pi$  in a line (or not at all). So we are now effectively partitioning the point of  $P_k \subset \pi$  with d lines. But these d lines only cut  $\pi$  into  $d^2$  pieces, and so an average piece must have  $\gtrsim |P_k|d^{-2}$  k-rich points and must meet  $\gtrsim Ld^{-1}$  lines, violating either condition.

Now we return to our set of lines  $\mathfrak L$  with  $\leq L^{1/2}$  lines in any plane. Is it possible that with this restriction, we can find a good cell decomposition obeying one of the conditions. The answer is still no. We have the same problems as before with condition A. If P is a set of points on a convex surface like a sphere, then for any cell decomposition with d planes, one of the cells will have  $\gtrsim |P|d^{-2}$  points. Also, P could be a set of points on a curve  $\gamma$ . There are many curves  $\gamma$  that intersect every plane in  $\leq 10$  points - say a typical trefoil knot. If P is a set of points on such a curve, then any cell decomposition with d planes has a cell with  $\gtrsim |P|d^{-1}$  points on it.

We also have a problem with condition B. Suppose that P is a set of points on a convex curve  $\gamma$  in  $\mathbb{R}^2$ , and  $\mathfrak{L}$  is  $P \times \mathbb{R} \subset \mathbb{R}^3$ . Suppose that one plane is transverse to the  $x_3$ -axis. This plane intersects the lines in |P| points lying on a convex curve. Each other plane intersects the first plane in a line. All together, the other planes cut the first plane into  $\lesssim d^2$  faces. But they cut the convex curve into  $\lesssim d$  segments. Therefore, we get a 2-dimensional face of our decomposition which transversely intersects  $\gtrsim Ld^{-1}$  lines. Any open cell bordering this face must intersect  $\gtrsim Ld^{-1}$  lines of  $\mathfrak{L}$ . We could also try using planes that are all parallel to the  $x_3$  axis, but there are similar problems, and one of the cells still contains  $\gtrsim Ld^{-1}$  lines.

The cellular method works well for incidences of codimension 1 objects, such as planes or spheres in  $\mathbb{R}^3$ . In this case, we can build an interesting cell decomposition by taking a random subset of the planes or spheres. For objects of codimension > 1, such as lines in  $\mathbb{R}^3$ , it has been difficult to apply the cellular method (at least directly).

Returning to our question, there are many examples where we cannot cut space into evenly matched cells. It's not clear if these examples share a useful structure or property that we could take advantage of. In our counterexamples, it seems that the points or lines fit onto a nice 2-dimensional surface or 1-dimensional curve. Does that always happen, or is it just wishful thinking?

#### 5. Polynomial cell decompositions

A union of d planes is a special case of an algebraic surface of degree d. The main idea in this chapter is to cut space into pieces with a degree d algebraic surface. Allowing an arbitrary degree d surface instead of just d planes greatly increases our flexibility. (When we pick d planes, we have 3d parameters to play with, but when we pick a degree d surface we have  $\sim (1/6)d^3$  parameters to play with!) With all this extra flexibility, we can do a much better job of decomposing space into evenly matched cells. On the other hand, if Z is a degree d surface, then a line either lies in Z or intersects Z in  $\leq d$  points. Therefore, each line intersects  $\leq d+1$  components of the complement of Z – exactly the same bound as if Z was a union of d planes.

**Theorem 5.1.** If X is any finite subset of  $\mathbb{R}^n$  and d is any degree, then there is a non-zero degree d polynomial P so that each component of  $\mathbb{R}^n \setminus Z(P)$  contains  $\leq C(n)|X|d^{-n}$  points of X.

We will prove this theorem next time. The proof is a cousin of finding a degree d polynomial that vanishes at  $\sim d^n$  prescribed points, but it uses topology instead of linear algebra.

We should also give a caveat. The theorem does NOT guarantee that the points of X lie in the complement of Z(P). In fact it is possible that  $X \subset Z(P)$ . There are two extreme cases. If all the points of X lie in the complement of Z(P), then we get optimal equidistribution, and we have a good tool to do a divide-and-conquer argument. If all the points of X lie in Z(P), then we see that  $deg(X) \leq d$ , and we get a good degree bound on X. Generally, X will have some points in Z(P) and some points in the complement. On one part of X we get a degree bound and on the other part of X we get good equidistribution.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# POLYNOMIAL CELL DECOMPOSITIONS

#### 1. Polynomial cell decompositions

A union of d planes is a special case of an algebraic surface of degree d. The main idea in this chapter is to cut space into pieces with a degree d algebraic surface. Allowing an arbitrary degree d surface instead of just d planes greatly increases our flexibility. (In  $\mathbb{R}^3$ , when we pick d planes, we have 3d parameters to play with, but when we pick a degree d surface we have  $\sim (1/6)d^3$  parameters to play with!) With all this extra flexibility, we can do a much better job of decomposing space into evenly matched cells. On the other hand, if Z is a degree d surface, then a line either lies in Z or intersects Z in S d points. Therefore, each line intersects S d + 1 components of the complement of S – exactly the same bound as if S was a union of S planes.

**Theorem 1.1.** If S is any finite subset of  $\mathbb{R}^n$  and d is any degree, then there is a non-zero degree d polynomial P so that each component of  $\mathbb{R}^n \setminus Z(P)$  contains  $\leq C(n)|S|d^{-n}$  points of S.

We will prove this theorem today. The proof is a cousin of finding a degree d polynomial that vanishes at  $\sim d^n$  prescribed points, but it uses topology instead of linear algebra.

# 2. Ham sandwich theorems

We will build our polynomial cell decomposition using a tool from topology, the ham sandwich theorem. In this section, we develop the tools that we will use.

**Theorem 2.1.** (Ham sandwich theorem) If  $U_1, ..., U_n$  are finite volume open sets in  $\mathbb{R}^n$ , then there is a hyperplane that bisects each set  $U_i$ .

This theorem was first proven by Banach in the late 30's (in the case n=3). Then Stone and Tukey generalized the argument to higher dimensions, and they gave a much more general theorem (see below). We can get a heuristic sense of the situation by counting parameters. The set of hyperplanes in  $\mathbb{R}^n$  is given by n parameters. Heuristically, we might expect that the subset of hyperplanes that bisect  $U_1$  is given by n-1 parameters; that the subset of hyperplanes that bisect  $U_1$  and  $U_2$  is given by n-2 parameters etc. Another special case happens when each  $U_i$  is a round ball. In that case, the solution is a plane that goes through the center of each ball. If the centers are in general position, there will be exactly one solution.

The planes are exactly the zero sets of degree 1 polynomials (polynomials of the form  $a_1x_1 + ... + a_nx_n + b$ ). We can generalize this setup by allowing other functions, such as higher degree polynomials. Suppose that V is a vector space of functions from  $\mathbb{R}^n$  to  $\mathbb{R}$ . Multiplication by a scalar doesn't change the zero set of a function f, so might say heuristically that the family of zero sets is given by dimV - 1 parameters. For example, if V is the polynomials of degree  $\leq 1$ , then dimV = n + 1, and the dimension of the set of hyperplanes is n. Since we have dimV - 1 parameters to play with, we might hope to bisect dimV - 1 sets  $U_i \subset \mathbb{R}^n$ . This heuristic turns out to be correct under very mild conditions on the space V.

To state our theorem, we make a little basic notation. For any function  $f : \mathbb{R}^n \to \mathbb{R}$ , we let  $Z(f) := \{x \in \mathbb{R}^n | f(x) = 0\}$ . We say that f bisects a finite volume open set U if

$$Vol_n\{x \in U | f(x) > 0\} = Vol_n\{x \in U | f(x) < 0\} = (1/2)Vol_nU.$$

**Theorem 2.2.** (General ham sandwich theorem, Stone and Tukey, 1942) Let V be a vector space of continuous functions on  $\mathbb{R}^n$ . Let  $U_1, ..., U_N \subset \mathbb{R}^n$  be finite volume open sets with  $N < \dim V$ . For any function  $f \in V \setminus \{0\}$ , suppose that Z(f) has Lebesgue measure 0. Then there exists a function  $f \in V \setminus \{0\}$  which bisects each set  $U_i$ .

The ham sandwich theorem is one corollary, given by taking V to be the degree 1 polynomials. If we consider the space of polynomials with degree  $\leq d$ , we get the following corollary.

Corollary 2.3. (Polynomial ham sandwich theorem)

*Proof.* We let V(d) be the space of polynomials of degree  $\leq d$ . We saw in the very beginning of the course that  $dimV(d) = \binom{d+n}{n}$ . It's also easy to check that for a non-zero polynomial P, Z(P) has measure 0. We leave this as an exercise.

The polynomial ham sandwich theorem is analogous to the more basic polynomial existence lemma which we have been using throughout the course. We rewrite the lemma here to make the analogy clear.

**Lemma 2.4.** (Polynomial existence lemma) If  $p_1, ..., p_N \in \mathbb{R}^n$  are points and  $N < \binom{d+n}{n}$ , then there is a non-zero polynomial of degree  $\leq d$  that vanishes at each  $x_i$ .

The polynomial existence lemma is analogous to the polynomial ham sandwich theorem. The first is based on linear algebra, and the second is based on topology. The polynomial existence lemma was a basic step in all of our arguments. Using the polynomial ham sandwich theorem instead gives a new direction to the polynomial method.

### 3. On the proof of the ham sandwich theorem

The heuristic argument above using parameter counting is definitely not a proof. The proof of the ham sandwich theorem is based on the Borsuk-Ulam theorem.

**Theorem 3.1.** (Borsuk-Ulam) Suppose that  $\phi: S^N \to \mathbb{R}^N$  is a continuous map that obeys the antipodal condition  $\phi(-x) = -\phi(x)$  for all  $x \in S^N$ . Then the image of  $\phi$  contains  $\theta$ .

For a proof of the Borsuk-Ulam theorem, the reader can look at Matousek's book *Using the Borsuk-Ulam theorem* or in the book *Differential Topology* by Guillemin and Pollack, Chapter 2.6. The book *Using the Borsuk-Ulam theorem* discusses some surprising applications of Borsuk-Ulam to combinatorics.

Proof of the general ham sandwich theorem. For each i from 1 to N, we define  $\phi_i$ :  $V \setminus \{0\} \to \mathbb{R}$  by

$$\phi_i(F) := Vol(\{x \in U_i | F(x) > 0\}) - Vol(\{x \in U_i | F(x) < 0\}).$$

So  $\phi_i(F) = 0$  if and only if f bisects  $U_i$ . Also,  $\phi_i$  is antipodal,  $\phi_i(-F) = -\phi_i(F)$ . We will check below that  $\phi_i$  is a continuous function from  $V \setminus \{0\}$  to  $\mathbb{R}$ . We assemble the  $\phi_i$  into one function  $\phi: V \setminus \{0\} \to \mathbb{R}^N$ .

We know that dimV > N, and without loss of generality we can assume that dimV = N + 1. Now we choose an isomorphism of V with  $\mathbb{R}^{N+1}$ , and we think of  $S^N$  as a subset of V. The map  $\phi: S^N \to \mathbb{R}^N$  is antipodal and continuous. By the Borsuk-Ulam theorem, there is a function  $f \in S^N \subset V \setminus \{0\}$  so that  $\phi(f) = 0$ . This function f bisects each  $U_i$ .

It only remains to check the technical point that  $\phi_i$  is continuous. This follows from the next lemma. It's basically an exercise in measure theory.

**Continuity Lemma.** Let V be a finite-dimensional vector space of continuous functions on  $\mathbb{R}^n$ . Suppose that for each  $f \in V \setminus \{0\}$ , the set Z(f) has measure 0.

If U is a finite volume open set, then the measure of the set  $\{x \in U | f(x) > 0\}$  depends continuously on  $f \in V \setminus \{0\}$ .

*Proof.* Suppose that f is a function in  $V \setminus \{0\}$  and  $f_n \in V \setminus \{0\}$  with  $f_n \to F$  in V. A priori,  $f_n$  converges to f in the topology of V. But then it follows that  $f_n \to f$  pointwise. Pick any  $\epsilon > 0$ . We can find a subset  $E \subset U$  so that  $f_n \to f$  uniformly pointwise on  $U \setminus E$ , and  $m(E) < \epsilon$ .

The set  $\{x \in U | f(x) = 0\}$  has measure zero. Therefore, we can choose  $\delta$  so that the set  $\{x \in U \text{ such that } |f(x)| < \delta\}$  has measure less than  $\epsilon$ .

Next we choose n large enough so that  $|f_n(x) - f(x)| < \delta$  on U - E. Then the measures of  $\{x \in U | f_n(x) > 0\}$  and  $\{x \in U | f(x) > 0\}$  differ by at most  $2\epsilon$ . But  $\epsilon$  was arbitrary.

#### 4. Ham sandwich for finite sets

We now adapt the ham sandwich theorem to finite sets of points. Instead of open sets  $U_i$ , we will have finite sets  $S_i$ . We say that a polynomial P bisects a finite set  $S_i$  if at most half the points in  $S_i$  are in  $\{P > 0\}$  and at most half the points in  $S_i$  are in  $\{P < 0\}$ . Note that  $P_i$  may vanish on some or all of the points of  $S_i$ . We will give an example below to illustrate why we want this definition.

**Corollary 4.1.** Let  $S_1, \ldots, S_N$  be finite sets of points in  $\mathbb{R}^n$  with  $N < \binom{n+d}{n}$ . Then there is a non-zero polynomial of degree  $\leq d$  that bisects each set  $S_i$ .

Let us give an example now. Suppose that we take two sets  $S_1$  and  $S_2$  in the plane, both lying on the x-axis, with  $S_1 \subset [0,1] \times \{0\}$  and  $S_2 \subset [2,3] \times \{0\}$ . Since  $2 < {2+1 \choose 2} = 3$ , we should be able to choose a degree 1 polynomial to bisect both  $S_1$  and  $S_2$ . The only option is to choose the  $x_1$ -axis: any transverse line will fail to bisect one of the two sets. Because of this situation, we have to allow p to "bisect" a finite set S in the case that p vanishes on S.

The proof of the theorem is to replace the finite sets by finite unions of  $\delta$ -balls, apply the polynomial ham sandwich theorem, and then take  $\delta \to 0$ . We include the details here, but this is again just an analysis exercise.

*Proof.* For each  $\delta > 0$ , define  $U_{i,\delta}$  to be the union of  $\delta$ -balls centered at the points of  $S_i$ . By the polynomial ham sandwich theorem we can find a non-zero polynomial  $P_{\delta}$  of degree  $\leq d$  that bisects each set  $U_{i,\delta}$ . In fact, the proof of the ham sandwich theorem tells us that  $P_{\delta} \in S^N \subset V(d) \setminus \{0\}$ .

Now we can find a sequence  $\delta_m \to 0$  so that  $p_{\delta_m}$  converges to a polynomial  $PinS^N \subset V(d) \setminus \{0\}$ . Since the coefficients of  $P_{\delta_m}$  converge to the coefficients of P, it's easy to check that  $P_{\delta_m}$  converges to P uniformly on compact sets.

We claim that P bisects each set  $S_i$ . We prove the claim by contradiction. Suppose instead that P>0 on more than half of the points of  $S_i$ . (The case P<0 is similar.) Let  $S_i^+ \subset S_i$  denote the set of points of  $S_i$  where P>0. By choosing  $\epsilon$  sufficiently small, we can assume that  $P>\epsilon$  on the  $\epsilon$ -ball around each point of  $S_i^+$ . Also, we can choose  $\epsilon$  small enough that the  $\epsilon$ -balls around the points of  $S_i$  are disjoint. Since  $P_{\delta_m}$  converges to p uniformly on compact sets, we can find m large enough that  $P_{\delta_m}>0$  on the  $\epsilon$ -ball around each point of  $S_i^+$ . By making m large, we can also arrange that  $\delta_m<\epsilon$ . Therefore,  $P_{\delta_m}>0$  on more than half of  $U_{i,\delta_m}$ . This contradiction proves that P bisects  $S_i$ .

### 5. Cell decompositions

**Theorem 5.1.** If S is any finite subset of  $\mathbb{R}^n$  and d is any degree, then there is a non-zero degree d polynomial P so that each component of  $\mathbb{R}^n \setminus Z(P)$  contains  $\leq C(n)|S|d^{-n}$  points of S.

Proof. Find a polynomial  $P_0$  of degree 1 that bisects S. Some points of S lie in  $Z(P_0)$ . The rest lie in  $S_+$  and  $S_-$ , which each have  $\leq |S|/2$  points. The sets  $S_+$  and  $S_-$  are in different components of the complement of  $Z(P_0)$ . Next we find a low degree polynomial  $P_1$  that bisects  $S_+$  and  $S_-$ . Neglecting the points in  $Z(P_1)$  we have four subsets of S left each with  $\leq |S|/4$  points. These four subsets lie in different components of the complement of  $Z(P_0P_1)$ . We continue in this way to define polynomials  $P_2$ ,  $P_3$ , etc. The polynomial  $P_j$  bisects  $2^j$  sets. By the polynomial ham sandwich theorem, we can find  $P_j$  with degree  $\leq C(n)2^{j/n}$ . Each component of the complement of  $Z(P_0 \cdot \ldots \cdot P_j)$  has  $\leq |S|2^{-j}$  points.

We repeat J times, and we let  $P = P_0 \cdot ... \cdot P_J$ . Each component of the complement of Z(P) has  $\leq |S|2^{-J}$  points of S. We need to choose d so that  $deg(P) \leq d$ , which means that  $C(n) \sum_{j=0}^{J} 2^{j/n} \leq d$ . The sum is a geometric sum, and the last term is comparable to the whole. Therefore, we can arrange that  $degP \leq d$  and also  $2^{J/n} \gtrsim d$ . Therefore,  $2^{J} \gtrsim d^{n}$ , and each component of the complement of Z(P) has  $\leq |S|d^{-n}$  points of S.

We should also give a caveat. The theorem does NOT guarantee that the points of S lie in the complement of Z(P). In fact it is possible that  $S \subset Z(P)$ . There are two extreme cases. If all the points of S lie in the complement of Z(P), then we get optimal equidistribution, and we have a good tool to do a divide-and-conquer argument. If all the points of S lie in Z(P), then we see that  $deg(S) \leq d$ , and we get a good degree bound on S. Generally, S will have some points in Z(P) and some points in the complement. One part of S has a low degree and the other part of S is spread out well among the cells.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## USING (POLYNOMIAL) CELL DECOMPOSITIONS

## 1. Szemerédi-Trotter

We will recall the standard form of the theorem.

**Theorem 1.1.** If  $\mathfrak{S}$  is a set of S points and  $\mathfrak{L}$  is a set of L lines (all in  $\mathbb{R}^2$ ), then the number of incidences obeys the following bound:

$$I(\mathfrak{S}, \mathfrak{L}) \le C_0[S^{2/3}L^{2/3} + S + L].$$

We will prove the result by using a polynomial cell decomposition together with elementary counting bounds in each cell. We first recall the counting bounds.

**Lemma 1.2.** If  $\mathfrak{S}$  and  $\mathfrak{L}$  are as above, then

- $I(\mathfrak{S}, \mathfrak{L}) \leq L + S^2$ .  $I(\mathfrak{S}, \mathfrak{L}) \leq L^2 + S$ .

*Proof.* Fix  $x \in \mathfrak{S}$ . Let  $L_x$  be the number of lines of  $\mathfrak{L}$  that contain x and no other point of  $\mathfrak{S}$ . For each other point  $y \in S$ , there is at most one line of  $\mathfrak{L}$  containing x and y. Therefore,  $I(x,\mathfrak{L}) \leq S + L_x$ . So  $I(\mathfrak{S},\mathfrak{L}) \leq S^2 + \sum_{x \in S} L_x \leq S^2 + L$ .

Now we turn to the proof of the theorem.

*Proof.* If  $L > S^2/10$  or  $S > L^2/10$ , then the conclusion follows from the counting lemma. Therefore, we can now restrict to the case that

$$10^{1/2}S^{1/2} \le L \le S^2/10. \tag{1}$$

We will also use induction on L, and so we can assume the theorem holds for smaller sets of lines.

Now we come to the heart of the proof. We use the polynomial cell decomposition to cut  $\mathbb{R}^2$  into cells, and then we use the counting lemma in each cell.

Let d be a degree to choose later. By the polynomial cell decomposition lemma, we can find a non-zero polynomial P of degree  $\leq d$  so that each component of the complement of Z(P) contains  $\lesssim Sd^{-2}$  points of  $\mathfrak{S}$ . Let  $O_i$  be the components,  $S_i$ the number of points of  $\mathfrak{S}$  in  $O_i$ , and  $L_i$  the number of lines of  $\mathfrak{L}$  that intersect  $O_i$ . Since each line intersects  $\leq d+1$  cells, we know that  $\sum L_i \leq L(d+1)$ .

Applying the counting lemma in each cell, we get

$$I(\mathfrak{S}_i, \mathfrak{L}_i) \le L_i + S_i^2$$
.

We let  $\mathfrak{S}_{cell}$  be the union of  $\mathfrak{S}_i$  - all the points of  $\mathfrak{S}$  that lie in the interiors of the cells.

$$I(\mathfrak{S}_{cell}, \mathfrak{L}) = \sum_{i} I(\mathfrak{S}_{i}, \mathfrak{L}_{i}) \leq \sum_{i} L_{i} + \sum_{i} S_{i}^{2} \lesssim Ld + Sd^{-2} \sum_{i} S_{i} = Ld + S^{2}d^{-2}.$$

We let  $\mathfrak{S} = \mathfrak{S}_{cell} \cup \mathfrak{S}_{alg}$ , where  $\mathfrak{S}_{alg}$  is the set of points in Z(P). It remains to bound  $I(\mathfrak{S}_{alg}, \mathfrak{L})$ . We divide  $\mathfrak{L}$  as  $\mathfrak{L}_{cell} \cup \mathfrak{L}_{alg}$ , where  $\mathfrak{L}_{cell}$  are the lines that intersect some open cells, and  $\mathfrak{L}_{alg}$  are the lines contained in Z(P).

Each line of  $\mathfrak{L}_{cell}$  has  $\leq d$  intersection points with Z(P), hence  $\leq d$  incidences with  $\mathfrak{S}_{alg}$ . Hence  $I(\mathfrak{S}_{alg}, \mathfrak{L}_{cell}) \leq Ld$ . Summarizing everything so far, we have the following:

$$I(\mathfrak{S}, \mathfrak{L}) \leq C(Ld + S^2d^{-2}) + I(\mathfrak{S}_{alg}, \mathfrak{L}_{alg})$$

We will deal with the last term by induction. We will choose  $d \leq L/2$ . So  $\mathfrak{L}_{alg}$  contains  $\leq L/2$  lines. By induction,

$$I(\mathfrak{S}_{alq}, \mathfrak{L}_{alq}) \le C_0[S^{2/3}(L/2)^{2/3} + S + L/2].$$

Now we are ready to optimize over d. We need to choose d to be an integer between 1 and L/2. We choose  $d \sim S^{2/3}L^{-1/3}$ . Because of the bounds in equation (1), we can find d this size in the range  $1 \le d \le L/2$ . Plugging in, we get

$$I(\mathfrak{S}, \mathfrak{L}) \le CL^{2/3}S^{2/3} + C_0[S^{2/3}(L/2)^{2/3} + S + L/2].$$

Finally, we choose  $C_0$  large enough compared to C, and the whole right hand side is bounded by  $C_0[S^{2/3}L^{2/3} + S + L]$ .

## 2. The 3-dimensional version - outline of the ideas

We will prove (today and next lecture) the following 3-dimensional result, which we can think of as a possible analogue of the ST theorem for lines in  $\mathbb{R}^3$ .

**Theorem 2.1.** If  $\mathfrak{S}$  is a set of S points in  $\mathbb{R}^3$  and  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with at most B lines in any plane, then

$$I(\mathfrak{S}, \mathfrak{L}) \le C_0[S^{1/2}L^{3/4} + L^{1/3}B^{1/3}S^{2/3} + S + L].$$

In particular, if k is sufficiently large and we take  $\mathfrak{S}$  to be the set of points in  $\geq k$  lines of  $\mathfrak{L}$ , then plugging in we get  $|\mathfrak{S}_k| \lesssim L^{3/2}k^{-2} + LBk^{-3} + Lk^{-1}$ . Taking  $B = L^{1/2}$  and combining with our earlier bound for 3-rich points, we get

**Corollary 2.2.** If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq L^{1/2}$  lines in any plane and  $k \geq 3$ , then the number of k-rich points is  $\lesssim L^{3/2}k^{-2}$ .

Now we discuss some examples. The S term and the L term are easy. If we choose L/B planes, and use a grid configuration in each plane, we get  $\sim L^{1/3}B^{1/3}S^{2/3}$  incidences. Finally, if we choose points and lines coming from a 3-dimensional grid, we can get  $S^{1/2}L^{3/4}$  incidences. In particular, the theorem is sharp up to constant factors.

The main ideas are similar to the ideas in the proof of ST above, but there are one or two extra twists and the computations are longer. In this outline, we want to explain the main steps/ideas, especially the new twists, but postpone the calculations.

We let d be a degree we can choose later, and we build a degree d polynomial cell decomposition. In each cell we apply an incidence bound that we already know. We could apply the counting lemma as above. We can also apply the Szemerédi-Trotter theorem in each cell. Recall that the Szemerédi-Trotter theorem holds for points and lines in  $\mathbb{R}^n$  for any n by a random projection argument. Since it is stronger than the counting lemma bounds, we may as well use ST in each cell. Then adding up the contributions from the cells, we get

$$I(\mathfrak{S}_{cell}, \mathfrak{L}) \lesssim S^{2/3} L^{2/3} d^{-1/3} + S + L.$$

As d increases, we get stronger and stronger bounds on the incidences in the cells. On the other hand, as d increases, we get more points in Z(P) and weaker information about Z(P).

We can again divide the lines as  $\mathfrak{L}_{cell}$  and  $\mathfrak{L}_{alg}$ . Each line of  $\mathfrak{L}_{cell}$  has  $\leq d$  incidences with  $\mathfrak{S}_{alg}$ . Therefore, we get

$$I(\mathfrak{S},\mathfrak{L}) \lesssim dL + d^{-1/3}S^{2/3}L^{2/3} + S + L + I(\mathfrak{S}_{alg},\mathfrak{L}_{alg}).$$

In the proof of ST, we chose  $d \leq L/2$ , which forced  $L_{alg} \leq L/2$  and allowed us to use induction. We cannot quite do that here. A surface of low degree may contain arbitrarily many lines. This is true for planes and reguli, and also for many other examples. We cannot yet use induction. Also, we need to use the bound on the number of lines in a plane, which we haven't used yet.

The surface Z(P) contains  $\leq d$  planes. Each of these planes contains  $\leq B$  lines of  $\mathfrak{L}$ . Let  $\mathfrak{L}_{planar}$  be the subset of lines of  $\mathfrak{L}$  which lie in one of the planes of Z(P). Using this information and applying Szemerédi-Trotter in each plane, it's not hard to bound  $I(\mathfrak{S}, \mathfrak{L}_{planar})$ . In particular, we'll get the following bound:

$$I(\mathfrak{S}, \mathfrak{L}_{planar}) \lesssim B^{1/3} L^{1/3} S^{2/3} + dL + S + L.$$

This estimate is fine, and it remains to bound  $I(\mathfrak{S}_{alg}, \mathfrak{L}_{alg} \setminus \mathfrak{L}_{planar})$ . We will do this using our tools about special points and lines in an algebraic surface – as in the proof of the esimate on the number of 3-rich points. As in that lecture, we call a point special if it is critical or flat, and we call a line special if each point on the line is special. A point  $x \in Z(P)$  is special if and only if a set of polynomials called SP vanishes at x, and the polynomials in SP have degree  $\leq 3d$ .

One of the main tools in the special lines discussion is that there aren't that many special lines. The number of special lines in Z(P) which aren't in any of the planes is  $\leq 10d^2$ . We will choose d so that  $10d^2 \leq L/2$ , and then we can control this term by induction. We write  $\mathfrak{L}_{alg} = \mathfrak{L}_{spec} \cup \mathfrak{L}_{nonspec}$  where  $\mathfrak{L}_{spec}$  are the special lines of  $\mathfrak{L}_{alg}$ . Note that  $\mathfrak{L}_{planar} \subset \mathfrak{L}_{spec}$ . We just recalled that  $|\mathfrak{L}_{spec} \setminus \mathfrak{L}_{planar}| \leq 10d^2$ .

We have

$$I(\mathfrak{S}_{alg}, \mathfrak{L}_{alg} \setminus \mathfrak{L}_{planar}) \leq I(\mathfrak{S}_{alg}, \mathfrak{L}_{spec} \setminus \mathfrak{L}_{planar}) + I(\mathfrak{S}_{alg}, \mathfrak{L}_{nonspec}).$$

We can control the first term by induction as long as we choose  $10d^2 \leq L/2$ . And we will see that the second term is minor.

We write  $\mathfrak{S}_{alg} = \mathfrak{S}_{spec} \cup \mathfrak{S}_{nonspec}$ . Each non-special line contains at most 3d special points, so

$$I(\mathfrak{S}_{spec}, \mathfrak{L}_{nonspec}) \leq 3dL.$$

On the other hand, if a point  $x \in Z(P)$  lies in three lines in Z(P), then we saw that x is a special point of Z(P). Therefore, each point of  $\mathfrak{S}_{nonspec}$  is incident to le2 lines of  $\mathfrak{L}_{alg}$ . In particular, we get

$$I(\mathfrak{S}_{nonspec}, \mathfrak{L}_{nonspec}) \leq 2S.$$

Combining all the work so far, we see that

$$I(\mathfrak{S}, \mathfrak{L}) \leq C[dL + d^{-1/3}S^{2/3}L^{2/3} + B^{1/3}L^{1/3}S^{2/3} + S + L] + I(\mathfrak{S}_{alg}, \mathfrak{L}_{spec} \setminus \mathfrak{L}_{planar}).$$

This inequality holds for any integer  $d \geq 1$ , and if  $10d^2 \leq L/2$ , then the number of lines in  $\mathfrak{L}_{spec} \setminus \mathfrak{L}_{planar}$  is  $\leq L/2$ , and we can control that term by induction. We optimize d in this range, and we get the bound in the theorem.

(In the full proof, we have to be a touch more careful about some of the terms because of the induction.)

Next lecture we will do the details.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Polynomial Method

**Theorem 0.1** (3D Szemerédi-Trotter). Given S points and L lines in  $\mathbb{R}^3$  with at most B lines in any plane, the number of incidences I(S,L) is at most  $S^{\frac{1}{2}}L^{\frac{3}{4}}+B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}}+S+L$ .

The four terms of that sum are tight for, respectively, a 3-D grid, L/B planes with B lines in each with the 2-D Szemerédi-Trotter arrangement, all points collinear, and all lines concurrent, respectively.

We already know that  $I(S,L) \leq S^2 + L$  and  $I(S,L) \leq L^2 + S$  by counting, and  $I(S,L) \leq C[L^{\frac{2}{3}}S^{\frac{2}{3}} + L + S]$  by Szemerédi-Trotter. So we're already done unless  $S \leq L^2 \leq S^4$  (ignoring constants).

Claim 1 (Cell Estimate). In a polynomial cell decomposition of degree d,  $I(S, L) \leq C[d^{-\frac{1}{3}}S^{\frac{2}{3}}L^{\frac{2}{3}} + dL + S_{cell}] + I(S_{alg}, L_{alg})$ .

Proof. Let the cells be  $O_i$ , and let  $S_i$  and  $L_i$  be the number of points and lines that intersect  $O_i$ . Then  $\sum S_i = S_{cell} \leq S$ ,  $\sum L_i \leq dL$ , and  $S_i \leq d^{-3}S$ . (Here and henceforth, we drop constants.) Then  $I(S_{cell}, L) = \sum_i I(S_i, L_i) \leq \sum_i S_i^{\frac{2}{3}} L_i^{\frac{2}{3}} + L_i + S_i \leq (d^{-1}S^{\frac{1}{3}} \sum_i S_i^{\frac{1}{3}} L_i^{\frac{2}{3}}) + \sum_i L_i + S_i$ . By Hölder's inequality, that's at most  $(d^{-1}S^{\frac{1}{3}}(\sum_i S_i)^{\frac{1}{3}}(\sum_i L_i)^{\frac{2}{3}}) + \sum_i L_i + S_i = d^{-\frac{1}{3}}S^{\frac{2}{3}}L^{\frac{2}{3}} + dL + S_{cell}$ .

Finally,  $I(S_{alg}, L_{cell}) \leq dL$  by degree bounding, so we've counted everything but  $I(S_{alg}, L_{alg})$ , as desired.

Let  $L_p$ ,  $L_m$  and  $L_u$  ("planar," "multiplanar," and "uniplanar") be the sets of lines in at least one, at least two, and exactly one plane of Z(P), respectively, and let  $S_p$ ,  $S_m$ , and  $S_u$  be the same for points.

Claim 2 (Planar Estimate).  $I(S_{alg}, L_p) \leq C[B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}} + dL + S_u] + I(S_m, L_m).$ 

Also,  $|L_m| \leq d^2$ ; we'll choose d small enough that the last term is handleable by induction.

*Proof.*  $I(S_{alg}, L_p) \leq I(S_{alg}, L_u) + I(S_m, L_m)$ , since a line in multiple planes only hits points in multiple planes. Let  $\Pi$  be the set of planes in Z(P).

 $I(S_{alg}, L_u) \leq \sum_{\pi \in \Pi} I(S_{\pi}, L_{u:\pi}) \leq \sum_{\pi} dL_{u:\pi} + I(S_{u:\pi}, L_{u:\pi})$ . By the same application of Hölder's Inequality as before, that's at most  $dL + B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}} + S_u$ .

That leaves the nonplanar algebraic lines (and multiplanar lines) to bound. We'll use special points, that is, flat or critical points, that is, points at which SP (which has degree at most 3d) is 0 and special lines, on which every point is special.

Let  $S_s$  and  $S_n$  be the sets of special and nonspecial points, respectively, in  $S_{alg}$ , and define  $L_s$  and  $L_n$  similarly.

Claim 3 (Algebraic Estimate).  $I(S_{alg}, L_{alg} \setminus L_p) \leq C[dL + S_n] + I(S_s, L_s \setminus L_p)$ , and  $|L_s \setminus L_p| \leq 10d^2$ 

*Proof.* Recall that

1. If x is in three lines of Z(P) then x is special,

- 2. x is special iff SP(x) is 0, where  $deg(SP) \leq 3d$ , and
- 3. The number of lines that are special but not planar is at most  $10d^2$ .

Now,  $I(S_{alg}, L_{alg} \setminus L_p) \leq I(S_n, L_{alg} + I(S_s, L_n) + I(S_s, L_s \setminus L_p)$ . The first term is at most  $2S_n$  by the first recalled property and the second term is at most 3dL by the second recalled property.  $\square$ 

That leaves  $I(S_s, L_s \setminus L_p)$  and  $I(S_m, L_m)$  to bound; those contain at most  $11d^2$  lines. Let  $S' = S \setminus (S_s \cup S_m)$ . We already have  $I(S, L) \leq d^{-\frac{1}{3}}L^{\frac{2}{3}}S^{\frac{2}{3}} + dL + B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}} + S' + I(S_s, L_s \setminus L_p)I(S_m, L_m)$ . Lemma 1. The minimum value of  $d^{-\frac{1}{3}}L^{\frac{2}{3}}S^{\frac{2}{3}} + dL + B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}} + S$  with  $d \in [1, \frac{1}{9}L^{\frac{1}{2}}]$  (and  $B \geq L^{\frac{1}{2}}$  is about  $S^{\frac{1}{2}}L^{\frac{3}{4}} + B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}} + S'$ 

*Proof.* Just do it.  $\Box$ 

So  $I(S,L) \leq C[S^{\frac{1}{2}}L^{\frac{3}{4}} + B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}} + S'] + C_0[S^{\frac{1}{2}}(\frac{L}{2})^{\frac{3}{4}} + B^{\frac{1}{3}}(\frac{L}{2})^{\frac{1}{3}}S^{\frac{2}{3}} + (S - S')]$ , and we can choose  $C_0$  arbitrarily and bigger than, say, 100C, so that's at most  $C_0[S^{\frac{1}{2}}L^{\frac{3}{4}} + B^{\frac{1}{3}}L^{\frac{1}{3}}S^{\frac{2}{3}} + S + L]$ , as desired.

## 0.1 Efficiency of Polynomials

**Theorem 0.2** ("Efficiency of Polynomials"). If  $P : \mathbb{C} \to \mathbb{C}$  is a polynomial and  $F : \mathbb{C} \to \mathbb{C}$  is smooth (not necessarily holomorphic), and F = P outside some bounded domain  $\Omega$ , and  $\theta$  is a regular value of P and F, then P has at most as many zeros in  $\Omega$  as F does.

(If  $F: M^m \to N^n$  is a function, then  $x \in M$  is a critical point iff  $dF_x$  isn't surjective, and a regular point otherwise.  $y \in N$  is regular iff all its preimages are regular. In our case, if  $x \in Z(F)$ , that 0 is a regular value implies that  $dF_x : \mathbb{R}^2 \to \mathbb{R}^2$  is an isomorphism. Call  $\sigma(x)$  1 if  $dF_x$  preserves orientation and -1 otherwise.)

If P is a complex polynomial, then  $\sigma_P(x) = +1$  for all  $x \in Z(P)$ .

**Theorem 0.3.** The winding number of  $F: \partial\Omega \to \mathbb{C}\setminus\{0\}$  is  $\sum_{x\in Z(F)\cap\Omega} \sigma_F(x) = \sum_{x\in Z(P)\cap\Omega} \sigma_P(x)$ .

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## WHAT'S SPECIAL ABOUT POLYNOMIALS? (A GEOMETRIC PERSPECTIVE)

This section is for context and background. We discuss some results about polynomials from the point of view of geometry/topology. I think there are some interesting philosophical ideas here. We build up to an application of the general ham sandwich theorem to prove a geometric estimate about polynomials. This geometric argument is a precursor of the applications of the ham sandwich theorems in this section. We will not give complete proofs here. We sketch the main ideas when we can.

From the point of view of differential geometry and topology, polynomials (over  $\mathbb{C}$  or  $\mathbb{R}$ ) are strikingly efficient. I learned this point of view from V. I. Arnold's essay on the "Topological economy principle in algebraic geometry", in the Arnoldfest.

We begin with examples about complex polynomials. In fact, all these examples are true more generally of holomorphic functions. Polynomials in one variable are efficient in terms of the number of zeroes. We make this precise in the following proposition, which is closely related to material in a first course on complex analysis or in differential topology.

**Theorem 0.1.** Suppose that  $P: \mathbb{C} \to \mathbb{C}$  is a complex polynomial in one variable (or just a holomorphic function). We identify  $\mathbb{C}$  with  $\mathbb{R}^2$ , and suppose that  $F: \mathbb{R}^2 \to \mathbb{R}^2$  is any smooth function which agree with P outside of the unit disk  $\mathbb{D}$ . Finally, assume that  $\theta$  is a regular value for both P and F. Then the number of zeroes of P in  $\mathbb{D}$  is less than or equal to the number of zeroes of F in  $\mathbb{D}$ .

We sketch the main idea of the proof. A point  $x \in \mathbb{R}^2$  is a regular point of F if the derivative  $dF_x : \mathbb{R}^2 \to \mathbb{R}^2$  is an isomorphism. When we say that zero is a regular value, it means that each point x with F(x) = 0 is a regular point. Let  $x_1, ..., x_N$  be the points in the unit disk where F(x) = 0. Each such x can be given a multiplicity of +1 if  $detdF_x > 0$  and -1 if  $detdF_x < 0$ . We denote the multiplicity by  $m(x_i)$ . Let us assume for the sketch that F and P don't vanish on the unit circle  $S^1$ . Then  $F: S^1 \to \mathbb{R}^2 \setminus \{0\}$ , and F has a well-defined winding number around 0, denoted W(F). In differential topology, one proves that the winding number W(F) is equal to the sum of the multiplicities:  $W(F) = \sum_i m(x_i)$ . There is a similar formula for the polynomial P. Since P and F agree on  $S^1$ , W(F) = W(P). But P is a holomorphic function, and so  $dP_x$  is a complex linear map which must be orientation preserving. The multiplicity of P at each of its zeroes is 1, and so the number of zeroes of P in  $\mathbb{D}$  is exactly W(P) = W(F). Therefore, the number of zeroes of F in  $\mathbb{D}$  is at least the number of zeroes of P in  $\mathbb{D}$ .

The result says that P has no unnecessary zeroes. Also, there is nothing special about 0. If  $w \in C$  denotes any regular value of P and F, then there are at least as many points in  $\mathbb{D}$  where F(z) = w as points where P(z) = w. There is also nothing special about the unit disk, which can be replaced by other open sets. I don't know the history of this result. It may have been known in the 19th century.

This result holds for all holomorphic functions, and in fact just for functions whose derivatives are orientation preserving.

Complex polynomials in several variables are efficient in terms of the surface area of their zero sets.

**Theorem 0.2.** Suppose that  $P: \mathbb{C}^n \to \mathbb{C}$  is a complex polynomial (or just a holomorphic function). We identify  $\mathbb{C}$  with  $\mathbb{R}^2$  and  $\mathbb{C}^n$  with  $\mathbb{R}^{2n}$ , and suppose that  $F: \mathbb{R}^{2n} \to \mathbb{R}^2$  is any smooth function which agree with P outside of the unit ball  $\mathbb{B}^{2n}$ . Finally, assume that 0 is a regular value for both P and F. Let Z(P) denote the zero set of P, and let Z(F) denote the zero set of F. Since 0 is a regular value, these are both smooth manifolds of dimension 2n-2.

Then the volume of  $Z(P) \cap B$  is smaller than the volume of  $Z(F) \cap B$ :

$$Vol_{2n-2}[Z(P) \cap B] \le Vol_{2n-2}[Z(F) \cap B].$$

Here we are using the standard Euclidean metric on  $\mathbb{R}^{2n}$ . If we take n=1, then this theorem reduces to the first theorem, because Z(P) is a finite set of points and its volume is just the number of points. A related result is that Z(P) is a minimal surface. If we take  $Z(P) \cap \partial B$ , we get a closed (2n-3)-dimensional surface, and  $Z(P) \cap B$  is the smallest surface with that boundary.

This result plays an important role in the theory of minimal surfaces and in differential geometry. (I am not sure of its history either. I have seen it attributed to DeRham or to Federer. I believe it dates from the 1950's.) The proof uses differential forms. It has had a significant influence in geometry - many other arguments modelled on it have appeared since then. This type of argument was dubbed a calibration argument by Harvey and Lawson who generalized it to many other settings. A good place to read about this material is their paper "Calibrated geometries" in Acta Math. 148 (1982), 47-157.

We can give some idea of the argument without mentioning differential forms as follows. Let L denote any complex line in  $\mathbb{C}^n$ . The intersection  $L \cap Z(P)$  is just the points of L where P vanishes, and  $L \cap Z(F)$  is just the points of L where F vanishes. Let us therefore consider F as a function from L to  $\mathbb{C}$ . It won't necessarily happen that zero is a regular value for this function, but for almost every complex line L, zero is a regular value for both F and P. Then we can apply the one-dimensional result, and we get the following.

**Lemma 0.3.** For almost every complex line  $L \in \mathbb{C}^n$ .

$$|L \cap Z(P) \cap B| < |L \cap Z(F) \cap B|$$
.

The intersections of a surface X with various lines and the volume of X are connected. The branch of math that studies this connection is called integral geometry. Carefully assembling the information in the last lemma, it's possible to prove that  $Vol[Z(P) \cap B] \leq Vol[Z(F) \cap B]$ . We won't sketch the proof here, but we give a tiny introduction to integral geometry below.

Complex polynomials are also efficient in terms of the topological complexity of their zero sets. In particular, there is a striking theorem about polynomials in two variables.

**Theorem 0.4.** (Kronheimer-Mrowka) Suppose that  $P: \mathbb{C}^2 \to \mathbb{C}$  is a complex polynomial in two variables. We identify  $\mathbb{C}^2$  with  $\mathbb{R}^4$ , and suppose that  $F: \mathbb{R}^4 \to \mathbb{R}^2$  is any smooth function which agree with P outside of the unit ball  $\mathbb{B}^4$ . Assume that 0 is a regular value for both P and F. Let Z(P) denote the zero set of P, and let Z(F) denote the zero set of F. Let's also assume that Z(P) and Z(F) are connected. Then the genus of Z(P) is at most the genus of Z(F).

If Z(P) or Z(F) is disconnected, some form of this theorem still holds, but it takes more care to state it. The theorem was proven in the paper "Gauge theory for embedded surfaces. I." in Topology 32 (1993), no. 4, 773-826. The proof of the theorem uses gauge theory, and we can't even sketch it here. It has applications in low-dimensional topology, for example in knot theory. I believe this theorem is also true more generally for holomorphic functions (because an arbitrary holomorphic function can be well-approximated by a polynomial in any compact set). I'm curious whether some version of this topological efficiency holds for complex polynomials  $P: \mathbb{C}^n \to \mathbb{C}$  – as far as I know, this is an open problem.

So far, we have seen examples of the efficiency of complex polynomials, and more generally of holomorphic functions. The reader may well say that the key property involved is being holomorphic, not being polynomial. What about real polynomials? Are any of these theorems true for polynomials over  $\mathbb{R}$ ?

All three theorems are completely false for polynomials over  $\mathbb{R}$ . For example, a real polynomial may have P(-1) = -1, P(1) = 1, and may have 113 zeroes in (-1,1). A competitor function F may have only 1 zero in (-1,1) - the other 112 zeroes are unnecessary. Modifying this example a bit, it's easy to check that the second theorem is false, and the it's not hard to see that the third theorem is false too. In fact, any smooth function can be well approximated by a real polynomial, which suggests that real polynomials cannot have any special properties at all.

But if we switch our point of view from individual polynomials to the whole space of polynomials, then some version of the first two theorems survives for polynomials over  $\mathbb{R}$ . Let  $V_n(d)$  denote the vector space of all polynomials of degree  $\leq d$  in n variables. This vector space of functions is "efficient" in a certain sense.

**Theorem 0.5.** Pick a degree d and consider the space of polynomials of degree  $\leq d$  in one variable:  $V_1(d)$ . This space has dimension d+1. Let W be any other vector space of real-valued functions with dimension d+1. Every polynomial in  $V_1(d) \setminus \{0\}$  has at most d zeroes. Then some function  $F \in W \setminus \{0\}$  has at least d zeroes.

This is a basic dimension counting argument, of the kind we have used many times.

Proof. Pick any d points  $x_1, ..., x_d \in \mathbb{R}$ . Let E be the evaluation map  $E: W \to \mathbb{R}^d$  given by  $E(F) = (F(x_1), ..., F(x_d))$ . The map E is linear, and the dimension of the domain is greater than the dimension of the range. Therefore E has a non-trivial kernel. Let F be a non-zero element in ker E.

The set of real polynomials in n variables is also efficient in a similar way.

**Theorem 0.6.** (Gromov) For any  $d \ge 1$ ,

$$\sup_{0 \neq P \in V_n(d)} Vol_{n-1} Z(P) \cap B^n \sim d.$$

If W is any vector space of continuous functions defined on the unit n-ball  $B^n$ , with dim  $W \ge \dim V_n(d)$ , then

$$\sup_{0 \neq F \in W} Vol_{n-1} Z(F) \cap B^n \gtrsim d.$$

This theorem says that the vector space  $V_n(d)$  is fairly efficient in terms of the volumes of zero sets. For a space of functions W from the unit ball  $B^n$  to  $\mathbb{R}$ , define MaxVol(W) to be  $\sup_{0\neq F\in W}Vol_{n-1}Z(F)\cap B^n$ . The theorem says that if  $dimW=dimV_n(d)$ , then  $MaxVolV_n(d)\leq C_nMaxVolW$ . (It's an open problem whether  $MaxVolV_n(d)\leq MaxVolW$ .)

The first half of the result comes from integral geometry, and it was known in the early 20th century. The second half is much more recent. It was proven by Gromov in the paper, "Isoperimetry of waists and concentration of maps" in Geom. Funct. Anal. 13 (2003), no. 1, 178-215.

We describe the proof of each half.

1. Let P be a non-zero polynomial of degree  $\leq d$ . For a line  $l \subset \mathbb{R}^n$ , either  $|l \cap Z(P)| \leq d$  or else  $l \subset Z(P)$ . If  $X^{n-1} \subset \mathbb{R}^n$  is a hypersurface, then the volume of X is connected to the number of intersections  $|l \cap X|$  with different lines. The connection is made by the Crofton formula, which we now describe.

Let AG(1,n) be the set of affine lines in  $\mathbb{R}^n$ . The group of rigid motions of  $\mathbb{R}^n$ ,  $G_{rigid}$ , acts transitively on AG(1,n). In fact, AG(1,n) is the quotient of the group of rigid motions by the stabilizer of one line. Using the Haar measure on  $G_{rigid}$ , we get a  $G_{rigid}$ -invariant measure on AG(1,n),  $d\mu$ . This measure is unique up to scaling.

**Theorem 0.7.** (Crofton) There exists a constant  $\alpha_n$  so that the following equation holds for every (smooth) hypersurface  $X \subset \mathbb{R}^n$ :

$$Vol_{n-1}(X) = \alpha_n \int_{AG(1,n)} |l \cap X| d\mu(l).$$

We give the idea of the proof. We abbreviate the RHS by Crof(X). We want to prove that the two sides are equal, and we note some qualities that the two sides have in common.

- 1. Disjoint unions. If X is the disjoint union of  $X_1$  and  $X_2$ , we have  $Vol_{n-1}X = Vol_{n-1}X_1 + Vol_{n-1}X_2$  and  $Crof(X) = Crof(X_1) \cap Crof(X_2)$ .
- 2. Rigid motion invariance. If g is a rigid of  $\mathbb{R}^n$ , then  $Vol_{n-1}(gX) = Vol_{n-1}(X)$  and Crof(gX) = Crof(X).

We choose  $\alpha_n$  so that  $Crof([0,1]^{n-1}) = 1 = Vol_{n-1}([0,1]^{n-1})$ . By the two properties above, we easily see that  $Crof([0,s]^{n-1}) = s^{n-1}$  for any s. (We start with positive integers and with s = 1/N, and then rational s, and then take a limit to get all s.) Next if X is a finite union of (n-1)-cubes with various side lengths, we see that  $Vol_{n-1}X = Crof(X)$ .

Finally, given an arbitrary hypersurface X, we approximate X by  $X_{cub}$  - a finite union of (n-1)-cubes. We just have to check that  $Vol_{n-1}(X_{cub})$  approximates  $Vol_{n-1}(X)$  and that  $Crof(X_{cub})$  approximates Crof(X).

Now using the Crofton formula, we can bound the volume of  $Z(P) \cap B^n$ . Note that if l is any line which intersects  $B^n$ , then  $|S^{n-1} \cap l| = 2$ . The set of lines l with  $l \subset Z(P)$  has measure 0. So we see that for  $d\mu$  almost every  $l \subset \mathbb{R}^n$ ,

$$|Z(P) \cap B^n \cap l| \le (d/2)|S^{n-1} \cap l|.$$

Using the Crofton formula, we see that  $Vol_{n-1}Z(P) \cap B \leq (d/2)VolS^{n-1}$ . This inequality is sharp for every even d by taking Z(P) to be a union of d/2 spheres with radii very close to 1. (The sharp argument and example were explained to me by Jake Solomon.)

The second half of the theorem follows from the general ham sandwich theorem, which we recall.

**Theorem 0.8.** (Stone-Tukey) If W is a vector space of continuous functions from  $B^n$  to  $\mathbb{R}$ , and  $U_1, ..., U_N \subset B^n$  are finite volume open sets, with  $N < \dim W$ , and if each function  $F \in W \setminus \{0\}$  has meas(Z(F)) = 0, then there is a non-zero  $F \in W$  which bisects each set  $U_i$ .

In our case,  $dimW \ge dimV_n(d) \sim d^n$ . (If any non-zero  $F \in W$  has Z(F) with positive Lebesgue measure, then  $Vol_{n-1}Z(F)$  is infinite.) We can apply the theorem. We let  $U_1, ..., U_N$  be  $\sim d^n$  disjoint balls in  $B^n$ , each with radius  $\sim d^{-1}$ .

A hypersurface which bisects the unit n-ball must have (n-1)-volume at least  $c_n > 0$ . This fact follows, for example, from the isoperimetric ienquality. By scaling,  $Z(F) \cap U_i$  must have (n-1)-volume at least  $c_n d^{-(n-1)}$ . Therefore,  $Vol_{n-1}Z(F) \gtrsim d^n d^{-(n-1)} = d$ .

To end this chapter, let's mention a couple themes that appear in both the geometry today and the combinatorics we've been studying. We always exploit the fundamental fact that a non-zero degree d polynomial in one variable vanishes at most d times. Next we come to polynomials in several variables. This is a very large space, and it has the simple but remarkable property that if we restrict a degree d polynomial in several variables to a line, then we get a degree d polynomial in one variable. So we get a lot of information about what the polynomial is doing on each line. In both settings, we want to assemble that information to give global information about what the polynomial is doing globally. In the geometric setting, integral geometry gives an important tool for assembling the information, leading to some of the geometric estimates above.

We've also seen the general ham sandwich theorem in both settings. The way it's applied is a little different, but the geometric theorem on efficiency of real polynomials is still a kind of precursor for the approach in this chapter.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### DETECTING REGULI AND PROJECTION THEORY

We have one more theorem about the incidence theory of lines in  $\mathbb{R}^3$ .

**Theorem 0.1.** If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane or regulus, and if  $B \geq L^{1/2}$ , then the number of intersection points of  $\mathfrak{L}$  is  $\leq BL$ .

This theorem is an improvement of our earlier estimate on 3-rich points.

**Theorem 0.2.** If  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane, and if  $B \geq L^{1/2}$ , then  $|P_3(\mathfrak{L})| \lesssim BL$ .

Recall that  $P_k(\mathfrak{L})$  is the set of k-rich points of  $\mathfrak{L}$  – in particular  $P_2(\mathfrak{L})$  is the set of intersection points of  $\mathfrak{L}$ .

The proof of Theorem 0.2 uses the theory of critical points and flat points. We can't directly apply this theory to Theorem 0.1, because a point lying in two lines in a surface may be neither critical nor flat. So we will have to modify/refine these tools.

Let's package what we need about critical/flat points into one lemma for generalization.

**Plane detection lemma.** For any polynomial P in  $\mathbb{R}[x_1, x_2, x_3]$ , we can associate a list of polynomials SP with the following properties.

- (1)  $DegSP \leq 3DegP$ .
- (2) If x is contained in three lines in Z(P), then SP(x) = 0.
- (3) If P is irreducible and SP vanishes on Z(P), then Z(P) is a plane.

Roughly speaking, SP has the job of detecting whether Z(P) looks like a plane. If SP(x) = 0, then it (roughly) means that Z(P) looks kind of like a plane near x. If SP vanishes on Z(P) (and P irreducible), then it means that Z(P) is a plane. We will refine this technique and build a polynomial RP that detects whether Z(P) looks like a regulus.

**Regulus detection lemma.** For any polynomial P in  $\mathbb{R}[x_1, x_2, x_3]$ , we can associate a list of polynomials RP with the following properties.

- (1) DegRP < CDegP.
- (2) If x is contained in two lines in Z(P), then RP(x) = 0.
- (3) If P is irreducible and RP vanishes on Z(P), and if there is a non-special point x contained in two lines in Z(P), then Z(P) is a regulus.

The proof of Theorem 0.1 is essentially the proof of Theorem 0.2 using the regulus detection lemma instead of the plane detection lemma. We will include the details later, but there are no significant new ingredients. The new tool is the regulus detection lemma.

(The two detection lemmas are quite similar. The regulus detection lemma has an extra condition in the last item: "if there is a non-special point x contained in two lines in Z(P)". Recall that x is special if it is either critical or flat. This condition is not very elegant, but it will be easy to meet in the application to Theorem 0.1. If all the intersection points were critical or flat, then we could handle the situation with the plane detection lemma anyway.)

The regulus detection lemma is based on ideas about "ruled surfaces" developed by Salmon and Cayley in the 19th century. They proved the first interesting example of a detection lemma.

#### 1. Ruled surfaces and flecndes

We consider algebraic surfaces in  $\mathbb{C}^3$  in this section.

Suppose P is an irreducible polynomial. How many lines can there be in Z(P)? There can be infinitely many, which happens for planes, reguli, cones, and cylinders. There are actually many other examples.

For instance, consider a polynomial map  $\Phi: \mathbb{C}^2 \to \mathbb{C}^3$  of the form  $\Phi(s,t) = \Phi_1(s)t + \Phi_0(s)$ . The image contains infinitely many lines (fix s and let t vary). Also, the image is contained in Z(P) for some P. (Is the image exactly Z(P) for some P?)

An algebraic surface Z(P) is called 'ruled' if each  $x \in Z(P)$  lies in a line  $\subset Z(P)$ . Now we can ask a more refined question. If P is irreducible of a given degree, and Z(P) is not ruled, then how many lines can there be in Z(P)?

**Theorem 1.1.** If P is an irreducible polynomial in  $\mathbb{C}[z_1, z_2, z_3]$ , then either Z(P) is ruled or the number of lines in Z(P) is  $\leq C(\deg P)^2$ .

This theorem follows from the work of Salmon and Cayley from the 1800's. It appears in Salmon's book A Treatise on the Analytic Geometry of Three Dimensions. Chapter XIII deals with ruled surfaces, and ... First published in?

In particular, the theorem follows from Salmon and Cayley's work on the flecnode polynomial. They proved the following result.

Ruled surface detection lemma. For any polynomial P in  $\mathbb{C}[x_1, x_2, x_3]$ , we can define a finite set of polynomials FP with the following properties.

- (1)  $DegFP \leq CDegP$ .
- (2) If x is contained in a line in Z(P), then FP(x) = 0.
- (3) If FP vanishes on Z(P), then Z(P) is ruled.

The polynomial FP is called the flecnode polynomial. In fact FP is a single polynomial (not a set of several polynomials), but this fact doesn't matter that much in applications, and it's easier to prove the Ruled surface detection lemma in the form above. Given the flecnode polynomial, the estimate on the number of lines in a non-ruled surface follows from Bezout's theorem.

Salmon defined FP (and gave a formula for it), and he proved properties 1 and 2. Then Cayley proved property 3. (See pages 277-78 of Salmon's book.)

We will try to explain the main ideas in this type of detection lemmas. We will try to give a fairly general point of view about how to prove this type of lemma, and we will try to avoid writing long formulas. We will give a complete proof of the regulus detection lemma, and we will give the main ideas of the proof of the ruled surface detection lemma.

We say a point  $z \in \mathbb{C}^3$  is flectoral (for P) if there exists a non-zero vector V so that P vanishes in the direction V to fourth order. We write  $\nabla_V^s P$  to denote the  $s^{th}$  directional derivative of P in the direction V. We say P is flectoral at z if there exists a non-zero vector V so that

$$0 = \nabla_V P(z) = \nabla_V^2 P(z) = \nabla_V^3 P(z). \tag{1}$$

If z is contained in a line in Z(P), and if V is tangent to the line, then equation (1) holds.

It can be helpful to expand this expression in terms of derivatives of P in the coordinate directions. V is a vector  $(V_1, V_2, V_3) \in \mathbb{C}^3$ . For a multi-index  $I = (i_1, i_2, i_3)$ , we write  $V^I$  for  $V_1^{i_1} \dots V_3^{i_3}$ ,  $\partial_I$  for  $\frac{\partial^{i_1}}{\partial z_1^{i_1}} \dots \frac{\partial^{i_3}}{\partial z_3^{i_3}}$ , and I! for  $i_1! \cdot i_2! \cdot i_3!$ .

$$\nabla_V^s P(z) := \sum_{|I|=s} I! V^I \partial_I P(z).$$

Salmon defined his polynomial FP and proved that FP(z) = 0 if and only if z is a flectoral point. So the flectoral polynomial detects flectoral points. These facts boil down to the following lemma.

#### **Lemma 1.2.** Consider the set of equations

$$0 = \sum_{|I|=s} V^I a_I, s = 1, 2, 3.$$
 (2)

In these equations,  $a_I$  are parameters in  $\mathbb{C}$ . We let a be the vector with components  $a_I$ , so  $a \in \mathbb{C}^M$  for some M.

 $Sol := \{ a \in \mathbb{C}^M | Equation (2) \text{ has a non-zero solution } V \in \mathbb{C}^3 \}.$ 

The set Sol is an algebraic set in  $\mathbb{C}^M$ . In other words, Sol is the zero set of some list of polynomials G.

Given the lemma, we define  $FP(z) = G(\partial_I P(z))$ . If G is a set of polynomials of degree  $\leq C$  in  $a_I$ , then FP is a set of polynomials of degree  $\leq C(degP)$  in z. By the lemma, a point z is flectored if and only if FP(z) = 0.

In summary, given the Lemma 1.2, we can immediately define FP and prove properties 1 and 2 of the ruled surface detection lemma.

Lemma 1.2 is part of an area called projection theory. It's a special case of the fundamental theorem of projection theory. We introduce projection theory and prove the fundamental theorem in the next section.

## 2. Projection Theory

Let  $\mathbb{F}$  be a field. Recall that an algebraic set in  $\mathbb{F}^M$  is just the zero set of a finite list of polynomials. Suppose that Z is an algebraic set in  $\mathbb{F}^m \times \mathbb{F}^n$ , and we consider the projection of Z onto the second factor. Is the projection also an algebraic set?

In general the answer is no. Let's consider two examples. We begin working over the field  $\mathbb{R}$  where everything is as simple as possible to visualize.

**Example 2.1.** (Circle example) Let Z be the zero set of  $x^2 + y^2 - 1$  in  $\mathbb{R}^2$ . If we project Z to the x axis we get the closed segment [-1,1]. This is not an algebraic set.

**Example 2.2.** (Hyperbola example) Let Z be the zero set of xy = 1 in  $\mathbb{R}^2$ . If we project Z to the x-axis, we get  $\mathbb{R} \setminus \{0\}$ . This is not an algebraic set.

Projection theory studies this situation. What kind of structure do the projections have? Are there some situations where the projection is an algebraic set?

What would happen if we work over  $\mathbb{C}$  instead of  $\mathbb{R}$ ? The example with the circle gets better. If we let Z be the zero set of  $x^2 + y^2 - 1$  in  $\mathbb{C}^2$ , then the projection of Z to the x axis is  $\mathbb{C}$ . But the hyperbola example is the same as before – if we work over  $\mathbb{C}$ , the image of the projection is  $\mathbb{C} \setminus \{0\}$ .

We can loosely describe the situation with the hyperbola in the following way. For each  $x \in \mathbb{C} \setminus \{0\}$ , there is a unique solution to the equation xy - 1 = 0. As x approaches zero, this solution y(x) tends to infinity. In some sense, when x is equal to zero, the solution is "at infinity". We can make this precise by working with projective space. Instead of  $y \in \mathbb{F}^n$ , we can consider  $y \in \mathbb{FP}^n$ . Instead of starting with an algebraic set  $Z \subset \mathbb{F}^m \times \mathbb{FP}^n$ . If  $\mathbb{F}$  is algebraically closed and if we work projectively, then the projection of Z is also algebraic.

Working with y in projective space is equivalent to using polynomials that are homogeneous in y. We can phrase the fundamental theorem of projection theory in the following way.

Fundamental Theorem of Projection Theory. Suppose that Q(x,y) is a finite list of polynomials in  $x \in \mathbb{F}^m$  and  $y \in \mathbb{F}^n$ , each of which is homogeneous in y. Let  $SOL \subset \mathbb{F}^m$  be the set

 $SOL := \{x \in \mathbb{F}^m | \text{the equation } Q(x,y) = 0 \text{ has a non-zero solution } y \in \mathbb{F}^n \}.$ 

If  $\mathbb{F}$  is algebraically closed, then SOL is an algebraic set.

For example, consider the equations in Lemma 1.2. We have the equations  $0 = \sum_{|I|=s} a_I V^I$ , for s=1,2,3. Each equation is homogeneous in V. By the fundamental theorem of projection theory, the set of a so that these equations have a non-zero solution  $V \in \mathbb{C}^3 \setminus \{0\}$  is an algebraic set. So Lemma 1.2 is a corollary of the fundamental theorem of projection theory.

# 3. Proof of the fundamental theorem of projection theory

Let  $\mathbb{F}$  be any field. Let  $Q_j(x,y)$  be homogeneous in y with degree  $d_j$ . If we think of x as a parameter, for each x, we get  $Q_{j,x}(y)$ , a polynomial in y which is homogeneous of degree  $d_j$ . We let  $I(x) \subset \mathbb{F}[y]$  be the ideal spanned by the polynomials  $Q_{j,x}(y)$ .

This ideal is homogeneous. Recall that for any polynomial Q we write  $Q_{=d}$  for the degree d part of Q. An ideal is homogeneous if for any  $Q \in I$ , and any d, we have  $Q_{=d} \in I$  also. In particular, any ideal generated by homogeneous polynomials is homogeneous. We let  $I(x)_{=d}$  be the homogeneous degree d polynomials in I(x).

**Proposition 3.1.** For any integers  $d, B \ge 0$ , the set  $\{x \in \mathbb{F}^m | dim I(x)_{=d} \le B\}$  is an algebraic set.

This proposition follows from the homogeneity of Q(x, y) (in y). Let  $H_{=d} \subset \mathbb{F}[y_1, ..., y_n]$  be the degree d homogeneous polynomials.

*Proof.* Consider the multiplication map  $M(x)_{=d}: \bigoplus_j H_{=d-d_j} \to I(x)_{=d}$ , given by

$$M_{=d}(R) := \sum_{j} Q_{j,x} R_j.$$

Since  $R_j$  is homogeneous of degree  $d - d_j$  and  $Q_{j,x}$  is homogeneous of degree  $d_j$ , we see that  $M_{=d}(R)$  is homogeneous of degree d. Since I(x) is the ideal spanned by  $Q_{j,x}$ , the image of  $M(x)_{=d}$  is in I(x). So we see that  $M(x)_{=d}$  is a linear map to  $I(x)_{=d}$  as claimed.

The key point of the proof is that  $M(x)_{=d}$  is surjective! This follows from the homogeneity. Suppose that  $f \in I(x)_{=d}$ . By definition, f is degree d and  $f = \sum_{j} Q_{j,x} f_{j}$  for some polynomials  $f_{j}$ . But since  $Q_{j,x}$  is homogeneous of degree  $d_{j}$ , we see that  $f = \sum_{j} Q_{j,x} f_{j,=d-d_{j}}$ . So f is in the image of  $M(x)_{=d}$ .

The linear map  $M(x)_{=d}$  can be described by a matrix. The dimension of  $I(x)_{=d}$  is exactly the rank of this matrix. The entries of the matrix are polynomials in x. The matrix  $M(x)_{=d}$  has rank  $\leq B$  if and only if each  $(B+1) \times (B+1)$  subdeterminant vanishes. Therefore, the set of matrices  $M(x)_{=d}$  with rank  $\leq B$  is an algebraic set.

**Proposition 3.2.** For any integers  $d, B \ge 0$ , the set  $\{x \in \mathbb{F}^m | \mathbb{F}[y]/I(x) \text{ is infinite dimensional}\}$  is an algebraic set.

*Proof.* The first step is to see that  $\mathbb{F}[y]/I(x)$  is infinite dimensional if and only if  $I(x)_{=d}$  is a proper subspace of  $H_{=d}$  for every  $d \geq 0$ . Indeed, if  $I(x)_{=d} = H_{=d}$  for some d, then I(x) contains all homogeneous polynomials of degree  $\geq d$ , and so  $\mathbb{F}[y]/I(x)$  is finite dimensional. The other direction is straightforward.

So the set of x where  $\mathbb{F}[y]/I(x)$  is infinite dimensional is exactly

$$\bigcap_{d>0} \{x \in \mathbb{F}^m | dim I(x)_{=d} \le dim H_{=d} - 1\}.$$

By the last proposition this is a countable intersection of algebraic sets. By the Noetherian property of  $\mathbb{F}[y]$ , the intersection stabilizes after finitely many values of d, and so the infinite intersection is also an algebraic set.

**Proposition 3.3.** If  $\mathbb{F}$  is algebraically closed and  $I \subset \mathbb{F}[y]$  is a homogeneous ideal, then Z(I) contains a non-zero point if and only if  $\mathbb{F}[y]/I$  is infinite dimensional (as a vector space over  $\mathbb{F}$ ).

*Proof.* We begin with the easy direction. Suppose that  $0 \neq y$  lies in Z(I). By homogeneity, the line through 0 and y also lies in Z(I). Now we consider the evaluation map from  $\mathbb{F}[y]/I$  to the functions on this line. Since  $\mathbb{F}$  is algebraically closed, there are infinitely many points on the line. For any finite subset of the points on the line, a polynomial can take arbitrary values. Therefore, the rank of the evaluation map is infinite, and the dimension of  $\mathbb{F}[y]/I$  is infinite.

Suppose instead that 0 is the only point in Z(I). By the Nullstellensatz, the radical of I is the ideal generated by  $y_1, ..., y_n$ . This use of the Nullstellensatz uses the fact that  $\mathbb{F}$  is algebraically closed. If I happens to be radical, then  $\mathbb{F}[y]/I$  is  $\mathbb{F}$ , and we are done. In not, then we get some finite sequence of ideals  $I = I_0 \subset I_1 \subset ... \subset I_J = (y_1, ..., y_n)$ , where each ideal is formed by adding a radical element to the previous ideal. By backwards induction on j, we check that  $R_j = \mathbb{F}[y]/I_j$  is finite

dimensional. This is true for j = J. Now  $R_{j-1}$  is formed by adjoining a nilpotent element to  $R_j$ . The inductive step is then straightforward.

Assembling these three propositions gives the fundamental theorem of projection theory.

#### 4. Taking stock

We have now defined the polynomial FP. We proved that  $degFP \leq \alpha degP$  for some constant  $\alpha$ . We proved that FP(x) = 0 if and only if the point x is flectoral. If x lies in a line in Z(P), then x is obviously flectoral and so FP(x) = 0.

Suppose that P is irreducible and that Z(P) contains  $> \alpha(degP)^2$  lines. The polynomial FP vanishes on each of these lines. Since the number of lines is > (degP)(degFP), it follows that P divides FP, and so FP = 0 on Z(P). We conclude that every point of Z(P) is flectoral: at every point there is a direction V in which P vanishes to fourth order.

The next step is to prove that the surface is actually ruled. Because every point is flechodal, the surface "looks nearly ruled" at every point. The next step is a local-to-global argument: because there is locally always a line nearly in the surface, the surface is globally ruled. This argument is quite different - it has to do more with differential geometry than with algebra. We discuss it more next time.

Finally, we note that our set up so far is pretty flexible. For example, suppose we define a point z to be t-flecthodal if there is a non-zero vector V so that  $\nabla_v^s P(x) = 0$  for all s from 1 to t. By the same argument as above, we can construct a finite set of polynomials  $F_t P$  with degree  $\leq \alpha(t) deg P$  so that z is t-flecthodal if and only if  $F_t P(z) = 0$ . If P is irreducible and Z(P) contains  $> \alpha(t) (deg P)^2$  lines, then every point of Z(P) is t-flecthodal. The flecthode is defined with t = 3, because that's the smallest value of t where the local-to-global argument works. But we can choose to work with any value of t, and it's actually a little easier to prove the local-to-global result with t = 4 or t = 10...

If a point lies in two lines in Z(P) we can find two linearly independent vectors  $V_1, V_2$  where  $\nabla_V^s P(z) = 0$  for all s. With a little modification of the technology, we can build a polynomial RP that vanishes whenever there are two independent directions in which P vanishes to order 4. We pick that up next time.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## FROM LOCAL TO GLOBAL

In this lecture, we discuss Cayley's theorem on flecnodes and ruled surfaces.

**Theorem 0.1.** If P is a polynomial in  $\mathbb{C}[z_1, z_2, z_3]$ , and if FP vanishes on Z(P), then Z(P) is ruled.

We know from last lecture that FP(z) = 0 if and only if z is flectoral. So for each  $z \in Z(P)$ , we know that there is a non-zero vector V so that P vanishes in the direction V to fourth order. Informally, this means that Z(P) locally looks ruled. We want to put the local information together and prove that there are actual global lines contained in Z(P).

Here is the basic difficulty with the proof. Suppose that V(z) is a smooth non-vanishing vector field on Z(P) which obeys the flecthodal equation at each point of Z(P). How can we use V to find lines? A natural method is to look at the integral curves of V. But consider the following example. The surface Z(P) may be a plane. At each point z in the plane Z(P), every tangent vector obeys the flecthodal equation. So let V be any smooth (tangent) vector field in Z(P). It obeys the flecthodal equation at every point, but the integral curves of V are basically arbitrary curves in the plane. If Z(P) is irreducible and not a plane, then this method actually works, but we can see the proof needs to be a little subtle because we need to use the fact that Z(P) is not a plane.

There are also unfortunately a couple of cases in the proof. We won't give a complete proof. Instead we will carefully do one case, which I think of as the main case. Moreover, this one case is enough to give the full proof of the regulus detection lemma.

In our model case, we will work over the real numbers, which is technically easier (and all we need in the regulus detection lemma). The argument works over the complex numbers with minor modifications, but we think it's easier to see the main ideas over  $\mathbb{R}$ .

Let's recall/clarify our notation for derivatives and higher derivatives, because we will need to be clear-headed about it.

If  $F: \mathbb{R}^3 \to \mathbb{R}$  is a function, we write  $\partial_i F$  to abbreviate the standard partial derivative  $\frac{\partial}{\partial x_i} F$ . If V is a vector, we write  $\nabla_V F(x)$  for  $\sum_i V_i \partial_i F(x)$ . The most important role in our story is played by second derivatives. If V, W are two vectors, then we write

$$\nabla^2_{V,W} F(x) = \sum_{i,j} V_i W_j \partial_i \partial_j F(x).$$

We abbreviate  $\nabla_V^2 = \nabla_{V,V}^2$ . Higher derivatives are similar. Now we can state our special case.

**Proposition 0.2.** Suppose that  $P \in \mathbb{R}[x_1, x_2, x_3]$ . Let  $O \subset Z(P)$  be an open subset of Z(P). Suppose that V is a smooth, non-zero vector field on O, obeying the flectodal equation:

$$0 = \nabla_V^s P(x)$$
, for all  $x \in O, s = 1, 2, 3$ .

We add a technical assumption. Suppose that at each point  $x \in O$ ,  $\nabla P(x) \neq 0$  and  $\nabla^2 P(x) : TZ \times TZ \to \mathbb{R}$  is non-degenerate.

Then the integral curves of V are straight line segments. Therefore, every point in O lies in a line in Z(P).

A word about the technical assumption. We defined above  $\nabla^2_{V,W}P(x)$  for any vectors V,W. Therefore,  $\nabla^2 P(x)$  is a map from  $\mathbb{R}^3 \times \mathbb{R}^3 \to \mathbb{R}$ . We restrict it to a map  $TZ \times TZ \to \mathbb{R}$ . Being non-degenerate means that for each non-zero  $V \in TZ$ , there is some  $W \in TZ$  so that  $\nabla^2_{V,W}P(x) \neq 0$ . For most surfaces Z(P),  $\nabla^2 P$  is non-degenerate on a dense open set. In this case, our propisition allows us to find a line of Z(P) thru almost every point. And since the non-degenerate points are dense, we can find a line of Z(P) thru the other points by taking limits. There are, however, some surfaces where  $\nabla^2 P$  is degenerate at every point of Z(P). These surfaces require a different argument - so we begin to see that the general theorem requires cases.

*Proof.* It suffices to show that at each point  $x \in O$ ,  $\nabla_V V$  is a multiple of V. If we let  $V_1$  be a unit length renormalization of V, then if follows that  $\nabla_{V_1} V_1 = 0$  on O. This equation implies that the integral curves of  $V_1$  (or V) are straight lines.

(Suppose that  $\gamma: \mathbb{R} \to O$  is an integral curve of  $V_1$ . In other words,  $\gamma'(t) = V_1(\gamma(t))$ . If we differentiate, we get  $\gamma''(t) = \nabla_{V_1(\gamma(t))} V_1(\gamma(t)) = 0$ .)

To explain the argument, we need a different derivative - the Lie derivative. If V is a vector field, we let  $L_V$  denote the Lie derivative, defined by  $L_V F(x) = \sum_i V_i(x) \partial_i F(x)$ . Actually,  $L_V F(x) = \nabla_V F(x)$ , but we come to second derivatives, there is an important difference:

$$L_V(L_V F) \neq \nabla_V^2 F! \tag{1}$$

Let's clarify what the left-hand side means.  $L_V F$  is a function. Then  $L_V(L_V F)$  is the Lie derivative of that function. The reason that the two sides are different is that on the left-hand side, the outer differentiation hits the vector field V appearing

in  $(L_V F)$ . On the right-hand side it doesn't. To compute the right-hand side at a point x, we only need to know V at the point x. But to compute the left-hand side, we need to know V in a small neighborhood - or at least the value of the derivative  $\nabla_V V$ . This  $\nabla_V V$  is a vector field with  $j^{th}$  component  $= \sum_i V_i \partial_i V_j$ . Expanding both sides of (1) and computing, we get:

$$L_V(L_V F) = \nabla_V^2 F + \nabla_{\nabla_V V} F. \tag{2}$$

Now we return to P. We know that  $L_V P = \nabla_V P = 0$  on O. Therefore, its derivative vanishes on O, and we get

$$0 = L_V(L_V P) = \nabla_V^2 P + \nabla_{\nabla_V V} P = \nabla_{\nabla_V V} P.$$

So we conclude that  $\nabla_{\nabla_V V} P = 0$  on O, and hence  $\nabla_V V \in TZ$ .

We can get more information by doing a similar computation with third derivatives. A third-order formula analogous to equation (2) reads

$$L_V(\nabla_V^2 F) = \nabla_V^3 F + 2\nabla_{\nabla_V V V}^2 F. \tag{3}$$

We know that  $\nabla_V^2 P$  vanishes on O, and therefore its derivative vanishes on O also, and we get:

$$0 = L_V(\nabla_V^2 P) = \nabla_V^3 P + 2\nabla_{\nabla_V V, V}^2 P = 2\nabla_{\nabla_V V, V}^2 P.$$
 (4)

So at each point of O, we know that  $\nabla_V V \in TZ$  and that  $\nabla^2_{\nabla_V V, V} P = 0$ . Since we assumed that  $\nabla^2 P$  is non-degenerate on TZ, this implies that  $\nabla_V V$  is a multiple of V. Here are the details. We assumed that  $\nabla^2 P$  is non-degenerate at each point of O. In other words, for each non-zero  $v \in TZ$ , the kernel of the map  $K_v : w \to \nabla^2_{w,v} P$  is one-dimensional. For our particular, V, we know that  $\nabla^2_{V,V} P = 0$ , and so the kernel of  $K_V$  is exactly the span of V. Since  $\nabla_V V \in TZ$  and  $\nabla^2_{\nabla_V V,V} P = 0$ , we conclude that  $\nabla_V V$  is in the span of V.

Exercises and comments. 1. Check that the above argument can be adapted to  $\mathbb{C}^3$ .

- 2. The above argument is fundamentally geometric, and it can be adapted to any smooth surface  $\Sigma \subset \mathbb{R}^3$ . The condition that  $\nabla^2 P$  is non-degenerate is equivalent to the second fundamental form of  $\Sigma$  being non-degenerate, which is equivalent to the Gauss curvature of  $\Sigma$  being non-zero.
- 3. Suppose that  $\nabla^2 P$  is degenerate at every point of Z(P). This is equivalent to saying that the Gauss curvature of Z(P) vanishes at every regular point. One example is a cylinder  $S^1 \times \mathbb{R}$ . In the category of smooth surfaces there are many other examples take a piece of paper and bend it gently in space. I think there are

also many examples of Gauss flat algebraic surfaces Z(P), but I'm not positive. If Z(P) is Gauss flat and FP=0 on Z(P), prove that Z(P) is still ruled.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## THE REGULUS DETECTION LEMMA

In this lecture we prove the regulus detection lemma, our last result about incidence of lines in  $\mathbb{R}^3$ .

**Regulus detection lemma.** For any polynomial P in  $\mathbb{R}[x_1, x_2, x_3]$ , we can associate a list of polynomials RP with the following properties.

- (1)  $DegRP \leq CDegP$ .
- (2) If x is contained in two lines in Z(P), then RP(x) = 0.
- (3) If P is irreducible and RP vanishes on Z(P), and if there is a non-special point x contained in two lines in Z(P), then Z(P) is a regulus.

The key fact about a regulus that we will use is that it is doubly ruled. A surface Z(P) is called doubly ruled if each point of Z(P) lies in two distinct lines in Z(P). The regulus and the plane are the only irreducible doubly ruled algebraic surfaces in  $\mathbb{R}^3$  (as we will prove). The job of the polynomial RP is roughly to detect whether there are two distinct directions in which the polynomial P vanishes to high order. (However, there is no polynomial that would do exactly this job. We discuss the problems below and we will see that RP almost does the job.)

Our first task is to define RP. Suppose that  $v = (v_1, v_2, v_3)$ . Suppose that  $Q_s(v)$  is a homogeneous polynomial of degree s, for s = 1, 2, 3. Let I be the ideal generated by  $Q_1, Q_2, Q_3$  in  $\mathbb{R}[v]$ . Recall that  $I_{=3}$  denotes the homogeneous degree 3 polynomials in I and that  $I_{=d}$  denotes the homogeneous degree d polynomials in  $\mathbb{R}[v]$ .

**Lemma 0.1.** The set  $\{(Q_1, Q_2, Q_3) \in H_{=1} \times ... \times H_{=3} | dim I_{=3} \leq 8\}$  is an algebraic set. It is equal to Z(R), where R is a finite list of polynomials in the coefficients of the  $Q_s$ . Each polynomial in R has degree  $\leq 9$ .

(This is just a special case of a previous lemma. Our set is given by the vanishing of some  $9 \times 9$  subdeterminants of a multiplication matrix, whose coefficients are coefficients of  $Q_s$ .)

We define  $Q_{s,x}(v) = \nabla_v^s P(x) = \sum_{|I|=s} I! \partial_I P(x) v^I$ , a homogeneous polynomial in v of degree s. The coefficients of  $Q_{s,x}(v)$  are polynomials in x of degree  $\leq degP$ . We let RP be  $R(Q_{1,x}, Q_{2,x}, Q_{3,x})$ . Therefore, RP is a finite list of polynomials of degree  $\leq 9degP$ . We have now checked property 1 of the regulus detection lemma.

We let I(x) be the ideal generated by  $Q_{1,x}, Q_{2,x}, Q_{3,x}$ . We have RP(x) = 0 if and only if  $I(x)_{=3}$  has dimension  $\leq 8$ .

The next task is to discuss the geometric meaning of the condition  $dim I(x)_{=3} \leq 8$ . The most important fact is contained in the following lemma.

**Lemma 0.2.** Suppose that x is a regular point of Z(P). Suppose that  $\nabla^2 P(x)$ :  $T_x Z \times T_x Z \to \mathbb{R}$  has signature (1,1). In this case there are two linearly-independent directions,  $\nu_1, \nu_2 \in TZ$  so that  $\nabla^2_{\nu_i} P(x) = 0$ . Given these assumptions,

$$RP(x) = 0 \text{ if and only if } \nabla^3_{\nu_1} P(x) = \nabla^3_{\nu_2} P(x) = 0.$$

This lemma says that under some fairly mild conditions, RP detects whether there are two linearly independent vectors which solve the equations  $0 = \nabla_{\nu}^{s} P(x)$  for s = 1, 2, 3.

*Proof.* We start by understanding the ideal  $I_{1,2}$  generated by  $Q_{1,x}$  and  $Q_{2,x}$ . We claim that  $I_{1,2}$  is exactly the ideal of polynomials that vanishes on the multiples of  $\nu_1$  and  $\nu_2$ . In other words, for any degree d,  $I_{1,2,=d}$  is the space of degree d polynomials that vanish on  $\nu_1$  and  $\nu_2$ .

We prove the claim as follows. Since x is a regular point of Z(P),  $\nabla P(x)$  is non-zero. The ideal generated by  $Q_{1,x}$  is exactly the set of polynomials that vanish on TZ. After performing a linear transformation, we can arrange that TZ is spanned by  $(1,0,0)=\nu_1$  and  $(0,1,0)=\nu_2$ . Now  $\mathbb{R}[v_1,v_2,v_3]/(Q_{1,x})$  is isomorphic to  $\mathbb{R}[v_1,v_2]$ . Next, we consider the image of  $Q_{2,x}$  in  $\mathbb{R}[v_1,v_2,v_3]/(Q_{1,x})=\mathbb{R}[v_1,v_2]$ . This image is non-zero, because  $\nabla^2 P(x): T_x Z \times T_x Z \to \mathbb{R}$  is non-degenerate. It vanishes on (1,0,0) and on (0,1,0), so it must be a non-zero multiple of  $v_1v_2$ . Therefore, I(x) is the ideal generated by  $v_3$  and  $v_1v_2$ . The rest of the claim is easy to check.

We see that  $I_{1,2,=d}$  is the kernel of the evaluation map from  $\mathbb{R}[v]_{=d}$  to the two points  $\nu_1$  and  $\nu_2$ . For each  $d \geq 1$ , this map is surjective, and so for all  $d \geq 1$ ,  $dim I_{1,2,=d} = dim \mathbb{R}[v]_{=d} - 2$ . In particular, for d = 3, we get  $dim I_{1,2,=3} = 8$ .

Now we are ready to show the the conclusion of the lemma. We know that RP(x) = 0 if and only if the dimension of  $I_{=3}$  is  $\leq 8$ . Now  $I_{=3}$  is spanned by  $I_{1,2,=3}$  and  $Q_{3,x}$ , and the dimension of  $I_{1,2,=3}$  is already 8. So  $dim I_{=3} \leq 8$  if and only if  $Q_{3,x} \in I_{1,2}$  if and only if  $Q_{3,x}(\nu_1) = Q_{3,x}(\nu_2) = 0$ . Since  $Q_{3,x}(v) = \nabla_v^3 P(x)$ , this last equation is equivalent to  $\nabla_{\nu_1}^3 P(x) = \nabla_{\nu_2}^3 P(x) = 0$ .

We talk briefly about other situations. If x is a critical point of P, then RP(x) = 0. If x is a flat point of Z(P) then RP(x) = 0. These are the only situations we will actually need. We put the write-up in the appendix.

For context, we talk a little more generally. The basic issue is that we are trying to detect whether some equations have two distinct roots. But having two distinct roots is not an algebraic condition - which we can see already by considering quadratic polynomials. Roughly speaking, if RP(x) = 0 then there are either two independent directions which satisfy the flecnodal equation, or else there may be one direction that satisfies the equation "with multiplicity 2". I believe that this happens for Gaussian

flat surfaces. So I believe that there are lots of irreducible P where RP = 0 on Z(P): planes and reguli and also Gaussian flat algebraic surfaces such as cylinders...

Now we are ready to verify the second property in the regulus detection lemma.

**Lemma 0.3.** If x lies in two lines in Z(P), then RP(x) = 0.

Proof. If x is critical or flat, then we have seen that RP(x) = 0. Suppose that x is not critical or flat. Let  $\nu_1$  and  $\nu_2$  be the tangent directions of the two lines. We know that  $\nabla_{\nu_i}^s P(x) = 0$  for i = 1, 2 and for any s. In particular,  $\nabla^2 P(x) : T_x Z \times T_x Z \to \mathbb{R}$  is a non-zero quadratic form (in two variables) that vanishes on two independent vectors, and so it must have signature (1, 1). Now Lemma 0.2 implies that RP(x) = 0.

Finally, we are ready to prove the third property - that under some conditions RP = 0 implies that Z(P) is a regulus. We state the result as a lemma.

**Lemma 0.4.** If P is irreducible and RP vanishes on Z(P), and if there is a non-special point  $x_0$  contained in two lines in Z(P), then Z(P) is a regulus.

The proof is based on local-to-global results for ruled surfaces. In particular, we will use the following result from last lecture:

**Proposition 0.5.** Suppose that  $P \in \mathbb{R}[x_1, x_2, x_3]$ . Let  $O \subset Z(P)$  be an open subset of Z(P). Suppose that V is a smooth, non-zero vector field on O, obeying the flectodal equation:

$$0 = \nabla_{V}^{s} P(x)$$
, for all  $x \in O, s = 1, 2, 3$ .

Suppose that at each point  $x \in O$ ,  $\nabla P(x) \neq 0$  and  $\nabla^2 P(x) : TZ \times TZ \to \mathbb{R}$  is non-degenerate.

Then the integral curves of V are straight line segments.

*Proof.* We know that  $\nabla^2 P(x_0)$  vanishes in the tangent directions to the two lines. Since  $x_0$  is not flat,  $\nabla^2 P(x_0) : T_x Z \times T_x Z \to \mathbb{R}$  is non-zero, and we see that it must have signature (1,1). We can choose an open neighborhood  $O \subset Z(P)$  around  $x_0$ , so that  $\nabla P \neq 0$  and  $\nabla^2 P : TZ \times TZ \to \mathbb{R}$  has signature (1,1) in O. (In particular,  $\nabla^2 P$  is non-degenerate on O.)

At each point of O, there are two independent vectors  $V_1, V_2 \in TZ$  with  $\nabla_V^2 P(x) = 0$ . We can normalize them to get two smooth vector fields  $V_1$  and  $V_2$ . Since RP = 0 on O, Lemma 0.2 implies that  $V_1$  and  $V_2$  each satisfy the flecthodal equation:  $\nabla_{V_i}^s P(x) = 0$  for s = 1, 2, 3. Now by the proposition above, the integral curves of  $V_1$  and  $V_2$  are each straight line segments. We call the integeral curves of  $V_1$  "horizontal" lines, and we call the integral curves of  $V_2$  "vertical lines".

In a small neighborhood of  $x_0$ , we will check that each horizontal line intersects each vertical line. Then we will find a plane or regulus that contains infinitely many

horizontal lines, and we will conclude that Z(P) is a plane or a regulus. (Finally the assumption that  $x_0$  is not flat means that Z(P) can only be a regulus.)

The set  $O \subset Z(P)$  is given by a graph. After a rotation and possibly shrinking O, we can assume that O is given by equation  $h(x_1, x_2) = x_3$  for a smooth function h, and that  $x_0$  is the origin (0,0,0). After a linear change of coordinates, we can assume that at  $x_0$ , the direction  $V_1$  is (1,0,0) and  $V_2$  is (0,1,0). Let  $L_1$  be the horizontal line through  $x_0$ , and let  $L_2$  be the vertical line through  $x_0$ . Notice that  $L_1$  is just the line  $x_2 = x_3 = 0$ . For each point (t,0,0) in  $L_1$ , let  $L_2(t)$  be the vertical line through (t,0,0). Notice that  $L_2(t)$  is the graph of h restricted to a line  $l_2(t)$  in the  $x_1 - x_2$  plane. The line  $l_2(t)$  passes through (t,0), and if t is small, it has slope close to (0,1). Similarly, let  $L_1(u)$  be the horizontal line through (0,u,0), which is the graph of h restricted to  $l_1(u)$  - a line in the plane thru (0,u) with slope close to (1,0). If t,u are small enough, then  $l_1(u)$  and  $l_2(t)$  intersect in a small neighborhood of 0, and so  $L_1(u)$  and  $L_2(t)$  interect in O.

By shrinking O, we can arrange that no two vertical lines intesect in O. Now fix three vertical lines close to  $L_2$ . There are infinitely many horizontal lines that intersect all three of the vertical lines in O. If the three vertical lines are skew, then infinitely many horizontal lines lie in a regulus. Now Z(P) intersects the regulus in infinitely many lines - and since P is irreducible, Z(P) is a regulus. If two of the vertical lines are coplanar, then infinitely many horizontal lines lie in a plane, and so Z(P) would be a plane.

## 0.1. On RP at critical and flat points.

**Lemma 0.6.** If  $\nabla P(x) = 0$ , then RP(x) = 0.

*Proof.* Since  $\nabla P(x) = 0$ , we have  $Q_{1,x}(v) = 0$ . Therefore, I(x) is the ideal generated by  $Q_{2,x}$  and  $Q_{3,x}$ . Therefore, the dimension of  $I(x)_{=3}$  is at most  $3+1=4\leq 8$ .

**Lemma 0.7.** Assume x is a regular point of Z(P). Then x is flat if and only if  $\nabla^2 P(x) : T_x Z \times T_x Z \to \mathbb{R}$  is equal to zero, if and only if  $Q_{2,x}$  is a multiple of  $Q_{1,x}$ .

*Proof.* The first equivalence is an exercise in multivariable calculus. Rotate and translate space so that x = 0, and  $\partial_1 P(0) = \partial_2 P(0) = 0$  but  $\partial_3 P(0) \neq 0$ . Without loss of generality we can work with these coordinates for the rest of the proof.

Locally near 0, the surface Z(P) is given by a graph of a function h:  $x_3 = h(x_1, x_2)$ . Therefore  $P(x_1, x_2, h(x_1, x_2)) = 0$  for all  $(x_1, x_2)$  in a neighborhood of 0. Differentiating once, we see that  $\partial_1 h(0) = \partial_2 h(0) = 0$ . Using this information and differentiating twice, we see that

$$\partial_{ij}P(0) = \partial_3 P(0)\partial_{ij}h(0)$$
, for  $i, j \in \{1, 2\}$ .

This proves the first equivalence. In these coordinates, we have at x=0,  $Q_{1,x}(v)=cv_3$  for a non-zero constant c. Also,  $Q_{2,x}(v)=\sum_{|I|=2}I!v^I\partial_IP(x)$ . So  $Q_{2,x}(v)$  is a multiple of  $v_3$  if and only if  $\partial_{1,1}P(x)=\partial_{1,2}P(x)=\partial_{2,2}P(x)=0$ , if and only if x is a flat point of Z(P).

**Lemma 0.8.** If x is a flat point of Z(P), then RP(x) = 0.

*Proof.* By the last lemma,  $Q_{2,x}$  is in the ideal generated by  $Q_{1,x}$ . Therefore, I(x) is the ideal generated by  $Q_{1,x}$  and  $Q_{3,x}$ . Therefore, the dimension of  $I(x)_{=3}$  is at most  $6+1=7\leq 8$ .

## 1. Incidence estimates

Using the regulus detection lemma, and the ideas in the proof of the  $P_3$  estimate (lecture 15), it's straightforward to prove the following.

**Theorem 1.1.** Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane or regulus, and suppose that  $B \geq L^{1/2}$ . Then  $|P_2(\mathfrak{L})| \lesssim BL$ .

Remark: It's not clear at all what happens for B smaller than  $L^{1/2}$  - for example B=10.

This finishes our work on incidences of lines in  $\mathbb{R}^3$ . For large k, the number of k-rich points is covered by the incidence estimate using polynomial ham sandwich (lecture 20). All together we get the following result.

**Theorem 1.2.** Suppose that  $\mathfrak{L}$  is a set of L lines in  $\mathbb{R}^3$  with  $\leq B$  lines in any plane or regulus. Suppose that  $B \geq L^{1/2}$  and  $2 \leq k \leq L^{1/2}$ . Then  $|P_k(\mathfrak{L})| \lesssim BLk^{-2}$ .

Remark. The incidence estimate in lecture 20 gives the slightly sharper but more complicated estimate  $\leq L^{3/2}k^{-2} + BLk^{-3} + Lk^{-1}$ , which holds for all  $2 \leq k \leq L$ .

This incidence estimate gives enough information to carry out the program of Elekes and Sharir on distinct distances (lecture 11).

At the beginning of next lecture, we'll talk briefly about how everything fits together, and then we'll close this chapter of the course.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# INTRODUCTION TO DIOPHANTINE EQUATIONS

In the early 20th century, Thue made an important breakthrough in the study of diophantine equations. His proof is one of the first examples of the polynomial method. His proof influenced a lot of later work in number theory, including diophantine equations, transcendental number theory, and later exponential sums. In this lecture, we will introduce some basic questions and conjectures and explain what Thue proved.

## 1. Naive guesses about diophantine equations

The most famous diophantine equation is the Fermat equation  $x^d + y^d - z^d = 0$ . For d = 2 there are many integer solutions, and for  $d \ge 3$  there are no positive integer solutions. The proof of the second part is extremely deep and hard. But is there any simple reason to expect that this situation is likely? In this section, we explore some naive guesses about diophantine equations.

Suppose that P is a homogeneous polynomial of degree d in n variables, with integer coefficients. Let us consider the equation P(x) = A, for some integer A. Let's try to guess how many solutions this equation is likely to have. Let's try to guess the number of solutions of size  $|x| \sim 2^s$ .

Guess the size of the set $\{x \in \mathbb{Z}^n | P(x) = A, |x| \sim 2^s\}$ .

Notice that if  $|x| \sim 2^s$ , then  $|P(x)| \lesssim 2^{sd}$ . It's hard to say much else about P(x) based on the information so far, so we make a primitive probabilistic model.

For each x with  $|x| \sim 2^s$ , let  $\tilde{P}(x)$  be a random integer of norm  $\leq 2^{sd}$ . The expected size of the set  $\{x \in \mathbb{Z}^n | \tilde{P}(x) = A, |x| \sim 2^s\}$  is  $\sim 2^{ns}/2^{ds} = 2^{(n-d)s}$ . If the polynomial P "behaved randomly", then the set of solutions of size  $|x| \sim 2^s$  would be  $\sim 2^{(n-d)s}$ . This suggests the following naive conjectures.

**Naive conjecture 1.** If degP < n, then the equation P(x) = A has infinitely many integer solutions, and the number of solutions of size  $\sim 2^s$  is  $\sim 2^{(n-d)s}$ .

Naive conjecture 2. If degP > n, then the equation P(x) = A has only finitely many integer solutions.

(The case degP = n is more delicate. Our heuristic gives that the number of solutions of size  $\sim 2^s$  is  $\sim 1$ , which would suggest infinitely many solutions. But having no solutions would not be such a large departure from the estimate in the heuristic...)

These conjectures are both false, but they are still useful.

We give some counterexamples.

Consider the equation 2x + 2y = 1. Our model predicts it should have many solutions, but it has none because the left-hand side is always even. Therefore, naive conjecture 1 is false. (To fix this particular counterexample, we should also assume that the equation has lots of solutions modulo p for some small primes p.)

Consider the equation  $(x^2 + y^2 - z^2)^{10} = 0$ . This equation has degree 20 in 3 variables, but every Pythagorean triple is a solution. There are also examples in two variables. The equation  $(x - y)^{10} = 1$  has infinitely many solutions. The equation  $x^2 - 2y^2 = 1$  has infinitely many solutions (approximately one for each scale  $|x| \sim 2^s$ , as predicted by the heuristic). Therefore, the equation  $(x^2 - 2y^2)^{10} = 1$  has infinitely many solutions. (We can rule out these particular counterexamples by insisting that P is irreducible.)

Although the conjectures are false, they give some useful intuition. If the degree d > n and there are infinitely many solutions, then that seems to be a big coincidence, and one may hope that there is some structure that explains what is happening.

Two of the big achievements in diophantine equations from the early 1900's confirm this intuition. The circle method of Hardy-Littlewood proves that equations have lots of solutions if the number of variables is much larger than the degree and if nothing bad happens modulo p for small primes p. Thue proved that Naive Conjecture 2 is actually true in two variables, as long as the polynomial is irreducible.

**Theorem 1.1.** (Thue) Suppose  $P \in \mathbb{Z}[x,y]$  is a homogeneous polynomial with degree  $\geq 3$  which is irreducible (over  $\mathbb{Z}$ ). If A is any integer, then the equation P(x) = A has only finitely many integer solutions.

#### 2. Diophantine approximation

Thue actually proved an even stronger theorem about rational approximations of algebraic numbers. To see the connection, let us consider the equation  $x^3 - 2y^3 = 7$ . If  $(x, y) \in \mathbb{Z}^2$  solves this equation, then we see that

$$(\frac{x}{y})^3 - 2 = 7y^{-3}.$$

Therefore, x/y is a good approximation of the cube root of 2, especially if y is large. A short calculation shows that

$$|2^{1/3} - \frac{x}{y}| \lesssim |y|^{-3}.$$

These are really very good rational approximations. For context, consider the following.

**Proposition 2.1.** For any  $\epsilon > 0$ , for almost every real number  $\beta$ , there are only finitely many integer solutions to the inequality

$$|\beta - \frac{x}{y}| \le |y|^{-2-\epsilon}. (*)$$

(The proof is a standard exercise in measure theory. Consider all the  $\beta$  in an interval so that (\*) has a solution with y > Y. This set is a union of intervals of total length  $\lesssim Y^{-\epsilon}$ .)

Although it's easy to prove this result for almost every  $\beta \in \mathbb{R}$ , it's hard to check it for any particular  $\beta$ , say  $\beta = 2^{1/3}$ . Liouville gave the first estimates about diophantine approximation of algebraic numbers.

**Proposition 2.2.** (Liouville, 1840's?) If  $\beta$  is an irrational algebraic number and  $\frac{x}{y}$  is a rational number, then

$$|\beta - \frac{x}{y}| \ge c(\beta)|y|^{-deg(\beta)}.$$

Recall that an algebraic number is a solution to a polynomial with integer coefficients. The degree  $deg\beta$  is the minimal degree of such a polynomial.

We will use a couple basic facts about algebraic numbers. There is actually a unique minimal polynomial Q with  $Q(\beta) = 0$ . (Minimal here means that the degree and the size of the coefficients are minimal.) The polynomial Q will be irreducible over  $\mathbb{Z}$ , and so it will have no rational roots. This polynomial also has  $Q'(\beta) \neq 0$ .

*Proof.* Notice that Q(x/y) is a non-zero rational number. The denominator can be taken to be  $y^{deg(\beta)}$ . Therefore,  $|Q(x/y)| \ge |y|^{-deg(\beta)}$ . If x/y is very close to  $\beta$ , then

$$|Q(x/y)| = |Q(\beta) + Q'(\beta)(\beta - x/y)| + \text{ lower order terms } \sim |Q'(\beta)||\beta - x/y|.$$

For example,  $|2^{1/3} - \frac{x}{y}| \ge c|y|^{-3}$ . This inequality is not strong enough to say anything about the number of solutions of  $x^3 - 2y^3 = 7$ . If we look back inside the proof of the Liouville inequality, it boils down to saying that  $x^3 - 2y^3 = 0$  has no integer solutions and so  $|x^3 - 2y^3| \ge 1$ . But this does nothing to constrain the solutions of  $x^3 - 2y^3 = 7$ . However, an inequality even slightly stronger than Liouville's does constrain the solutions to diophantine equations.

**Theorem 2.3.** (Thue) If  $\beta$  is an irrational algebraic number, and  $\gamma > \frac{\deg(\beta)+2}{2}$ , then there are only finitely many integer solutions to the inequality

$$|\beta - \frac{x}{y}| \le |y|^{-\gamma}.$$

The diophantine approximation theorem implies the diophantine equations theorem for the following reason. ...

### 3. Outline of Thue's proof

In this section we outline Thue's proof, and we explain how it is analogous to other arguments we have seen. We recall the main steps in the polynomial method by outlining the proof of the finite field Nikodym theorem.

Outline of the proof of finite field Nikodym: Suppose that N is a small Nikodym set in  $\mathbb{F}^n$ .

- (1) Find a non-zero polynomial P with controlled degree that vanishes on N. (Use parameter counting.)
- (2) Because N is a Nikodym set, the polynomial P must also vanish at many other points. (Vanishing lemma.)
- (3) The polynomial P vanishes at too many points, so it must be zero. Contradiction.

Here is the outline of Thue's proof. Suppose that the algebraic number  $\beta$  has two very good rational approximations  $r_1$  and  $r_2$ .

- (1) Find a non-zero polynomial  $P \in \mathbb{Z}[x, y]$  with controlled degree and coefficients that vanishes to high order at  $(\beta, \beta)$ . (Use parameter counting.)
- (2) Because  $r_1$  and  $r_2$  are good approximations of  $\beta$ , the polynomial must also vanish to high order at  $(r_1, r_2)$ .
- (3) The polynomial P vanishes too much at  $(r_1, r_2)$ , and so it must be zero. Contradiction.

The first step took Thue the longest to figure out. In the special case that  $\beta$  is the  $d^{th}$  root of a rational number, he constructed the polynomial P by hand with some difficulty. In this way, we was able to prove his finiteness theorem only for equations of the form  $Ax^d + By^d = C$ . After trying hard to construct the polynomial P for other values of  $\beta$ , Thue realized that he could find it by parameter counting.

Another important point about Thue's proof is that it uses two good rational approximations  $r_1$  and  $r_2$ . It might seem simpler to start with one rational approximation r and try to get a contradiction. But it seems very difficult to do this. We will come back to this point more later.

3.1. **Final comment.** Suppose that  $\alpha$  and  $\beta$  are two algebraic numbers. Then  $\alpha + \beta$  is an algebraic number. Why? This is a bit in the same spirit as the polynomial method...

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## PROOF OF THUE'S THEOREM - PART I

In this lecture we'll do the first half of the proof of Thue's theorem.

Suppose that P is a polynomial with integer coefficients. Let r be a rational point. We would like to understand the relationship between P vanishing to high order at r and the "size" of P in terms of its degree and size of its coefficients. Define |P| to be the maximum absolute value of the coefficients of P.

### 1. Polynomials vanishing to high order at a rational point

Let us start with the simple case where P is a one-variable polynomial. Let r = p/q, written in lowest form. We suppose that P vanishes to  $\ell$  orders at r, i.e.,

$$\partial^{j} P(r) = 0, \quad j = 0, 1, \dots, \ell - 1.$$

Here is the first example of such a polynomial that comes to mind.

Example 1:  $P(x) = (qx - p)^{\ell}$ . Then  $|P| \sim ||r||^{\ell}$ , where  $||r|| := \max(|p|, |q|)$ .

Could we do better? In other words, can we find a polynomial P with smaller coefficients, i.e., |P| smaller? As we shall see, the answer is no.

**Proposition 1.1** (Gauss). If  $P \in \mathbb{Z}[x]$  satisfies  $\partial^j P(r) = 0$  for  $j = 0, 1, ..., \ell - 1$ , then  $P(x) = (qx - p)^{\ell} P_1(x)$  for some  $P_1 \in \mathbb{Z}[x]$ .

*Proof.* The vanishing condition tells us that  $P(x) = (qx - p)^{\ell} P_2(x)$  for some polynomial  $P_2 \in \mathbb{R}[x]$ . It remains to show that the coefficients of  $P_2$  are integers. By expanding and comparing coefficients, we see that we can solve for the coefficients of  $P_2$  in terms of the coefficients of  $P_3$  and we deduce that the coefficients of  $P_2$  are at least rational.

Taking out the lowest common demoninator, we write  $P(x) = \frac{1}{M}(qx-p)^{\ell}\tilde{P}_2(x)$ , for some  $\tilde{P}_2 \in \mathbb{Z}[x]$  so that there is no prime dividing all the coefficients of  $\tilde{P}_2$  as well as M. So  $MP(x) = (qx-p)^{\ell}\tilde{P}_2(x)$ . If  $M \neq \pm 1$ , then let s be any prime divisor of M. Then we get a contradiction modulo s, since qx-p is not 0 mod s as p/q was already given in lowest terms, and  $\tilde{P}_2$  is also not 0 mod s. It follows that  $M=\pm 1$  and hence  $P_1 \in \mathbb{Z}[x]$ .

We're not quite done yet, as it's not always true that the norm of a polynomial is always at least as large as its factors.

Example 2: The polynomial  $(x-1)^2 = x^2 - 2x + 1$  has norm 2, while  $(x-1)^2(x+1) = x^3 - x^2 - x + 1$  has norm 1, which is smaller.

Fortunately, this example does not really pose an issue. The follow corollary answers our question for one variable polynomials.

## Corollary 1.2. $|P| \ge ||r||^{\ell}$ .

*Proof.* In  $P(x) = (qx - p)^{\ell} P_1(x)$ , we see that  $q^{\ell}$  divides the top coefficient and  $p^{\ell}$  divides the bottom non-zero coefficient.

Now, what about polynomials in two variables? Let  $P \in \mathbb{Z}[x_1, x_2]$ , and  $r = (r_1, r_2) = (p_1/q_1, p_2/q_2) \in \mathbb{Q}^2$ . We want to assume that P vanishes to high order at r. Let's say  $\partial_j P(r) = 0$  for all  $j \in J$ , where J is some list of pairs, e.g., all  $j = (j_1, j_2)$  with  $|j| := j_1 + j_2 \le \ell - 1$ .

Define  $||r|| := \max(||r_1||, ||r_2||)$ . If ||r|| is large, does P(r) = 0 imply something about the norm of P (as in the single variable case)? The following examples show that the answer is no.

Example 3:  $P(x_1, x_2) = x_1 - x_2$  and  $r = (r_1, r_1)$ . Then P(r) = 0 but |P| = 1.

What if we assume P vanishes at r to high order? Say  $\partial_j P(r) = 0$  for all j with  $|j| \le \ell - 1$ ? Still the answer is no.

Example 4:  $P(x_1, x_2) = (x_1 - x_2)^{\ell}$  and  $r = (r_1, r_1)$ . Then  $\partial_j P(r) = 0$  for all j with  $|j| \leq \ell - 1$ , but  $|P| \leq 2^{\ell}$ , independent of ||r||.

These examples suggest that perhaps our notion of vanishing to high order at a point isn't very useful. It prompts us to modify the question. Let us consider polynomials of the form

$$P(x_1, x_2) = P_1(x_1)x_2 + P_0(x_1).$$

Suppose we have

$$\partial_1^j P(r) = 0, \quad j = 0, 1, \dots, \ell - 1.$$

In this case, can we infer something about the size of P from the size of r? Since we are only differentiating with respect to  $x_1$ , this condition is equivalent to

$$\partial^{j}[p_{2}P_{1} + q_{2}P_{0}](r) = 0, \quad j = 0, 1, \dots, \ell - 1.$$

It follows by Corollary 1.2 that  $||p_2P_1+q_2P_0|| \ge ||r_1||^{\ell}$ . We see that  $||p_2P_1+q_2P_0|| \le ||p_2P_1|| + ||q_2P_0|| \le 2||r_2|||P||$ . It follows that  $|P| \ge \frac{1}{2} \frac{||r_1||^{\ell}}{||r_2||}$ .

Let us look at some examples of polynomials that satisfy the above vanishing conditions.

Example 5: Let  $P = q_2x_2 - p_2$ . Then  $|P| = ||r_2||$  and  $\partial_1^j P(r) = 0$  for all j.

Example 6: Let  $P = (q_2 x_2 - p_1)^{\ell}$ . Then  $|P| \ge ||r_1||^{\ell}$ .

#### 2. Integer solutions to linear systems

So far we've been looking at explicit examples of polynomials that satisfy the vanishing to high order condition. This is somewhat reminiscent of the first lecture in the course where we wanted to know how big the degree of a polynomial P must be if  $P(j, 2^j) = 0$  for  $j = 1, 2, ..., 10^6$ . There we also started by finding explicit examples, but at the end we arrived at our bound by counting dimensions. In a similar vein, we are going to find polynomials in  $\mathbb{Z}[x_1, x_2]$  by parameter counting.

**Proposition 2.1.** If  $L: \mathbb{Z}^M \to \mathbb{Z}^N$  is a linear map, given by a matrix with integer coefficients, with M > N, then there exists a nonzero  $x \in \mathbb{Z}^M$  such that Lx = 0.

For real vector spaces, this result follows from elementary results from linear algebra. For integers, it's actually even more elementary — it's just pigeonhole principle. Let's quickly sketch a proof first. Afterwards we'll be more careful quantitative bounds.

Proof. (Sketch) Let  $Q_S^M:=\{x\in\mathbb{Z}^M:|x_i|\leq S,i=1,\ldots,M\}$ . Since the map L restricted to  $Q_S^M\to Q_{C\cdot S}^N$  where C=C(L) is some sufficiently large constant. We have  $|Q_S^M|\sim S^M$  and  $|Q_{C\cdot S}|\sim C^NS^N$ . So we can choose S so that  $|Q_S^M|>|Q_{C\cdot S}^N|$ . Then by pigeonhole, there are  $x_1\neq x_2\in Q_S^M$  such that  $L(x_1)=L(x_2)$ , so that  $L(x_1-x_2)=0$ .

How big is the x produced by the proof? Let us look for some quantitative bounds. We can take  $C = |L|_{op} := \max_{|x|_{\infty}=1, x \in \mathbb{R}^M} |Lx|_{\infty}$  by the operator norm of L. In particular,  $|L|_{op} \leq M \cdot \max |\operatorname{coeff} \text{ of } L|$ . We need to take S so that  $(2S+1)^M > (2|L|_{op}S+1)^N$ . It suffices to have  $(2S+1)^M > |L|_{op}(2S+1)^N$ , or equivalently  $2S+1 > |L|_{op}^{M/(M-N)}$ . It follows that we can always find a nonzero  $x \in \mathbb{Z}^M$  with Lx = 0 and  $|x|_{\infty} \leq |L|_{op}^{N/(M-N)}$ . So we can revise the proposition to a more quantitative version.

**Proposition 2.2.** If  $L: \mathbb{Z}^M \to \mathbb{Z}^N$  is a linear map, given by a matrix with integer coefficients, with M > N, then there exists a nonzero  $x \in \mathbb{Z}^M$  with  $|x|_{\infty} \leq |L|_{op}^{N/(M-N)}$  such that Lx = 0.

Note that if M = N + 1, then our bound is  $|L|_{op}^{N}$  which is not too great, where as if M = 1.01N then our bound is  $|L|_{op}^{100}$  which is pretty good.

Let's go back to the one-variable polynomial case for a moment. Recall that we already know that  $(px - q)^{\ell}$  is the optimal polynomial vanishing to  $\ell$ -th order at r = p/q. Nevertheless, let us try this counting machinery here and see how well it does in comparison.

Suppose we are looking for a polynomial P of degree D such that  $\partial^j P(r) = 0$  for  $j = 0, 1, \ldots, \ell - 1$ . Let

$$P = \sum_{i=0}^{D} a_i x^i$$

We have

$$\partial^{j} P(x) = \sum_{i=0}^{D} a_{i} \frac{i!}{(i-j)!} x^{i-j} = j! \sum_{i=0}^{D} a_{i} {i \choose j} x^{i-j}.$$

(Extracting out the j! factor in the last step is a useful trick of the trade that makes it easier to bound the coefficients.) Setting  $\partial^j P(r) = 0$ , we have

$$\sum_{i=0}^{D} a_i \binom{i}{j} q^{D-(i-j)} p^{i-j} = 0.$$

The coefficients of the  $a_i$ 's are all bounded in absolute value by  $2^D ||r||^D$ . Viewing  $(a_0, \ldots, a_D) \in \mathbb{Z}^{D+1}$  as our unknowns, it follows from Proposition 2.2 that we can find a polynomial P of degree D with  $\partial^j P(r) = 0$  for  $j = 0, 1, \ldots, \ell - 1$  such that

$$|P| \le (2^D ||r||^D)^{\ell/(D-\ell)} \sim ||r||^{\ell D/(D-\ell)}.$$

So we could take, for example,  $D = 100\ell$  to get  $|P| \sim ||r||^{1.01\ell}$ . For comparison, the optimal example  $(qx - p)^{\ell}$  has  $D = \ell$  and  $|P| \sim ||r||^{\ell}$ .

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## PROOF OF THUE'S THEOREM - PART II

1. POLYNOMIALS THAT VANISH TO HIGH ORDER AT A RATIONAL POINT Suppose that  $P \in \mathbb{Z}[x_1, x_2]$  has the special form

$$P(x_1, x_2) = P_1(x_1)x_2 + P_0(x_1).$$

Suppose that  $r \in \mathbb{Q}^2$ . If P vanishes to high order at a complicated point r, how big do the coefficients of P have to be? More precisely, we suppose that  $\partial_1^j P(r) = 0$  for  $0 \le j \le l-1$ . Last time we gave two examples. The polynomial  $q_2x_2 - p_2$  which has size  $||r_2||$ , and the polynomial  $(q_1x_1 - p_1)^l$ , which has size  $||r_1||^l$ .

By parameter counting it is possible to do somewhat better.

**Proposition 1.1.** For any  $r \in \mathbb{Q}^2$ , and any  $l \geq 0$ , there is a polynomial  $P \in \mathbb{Z}[x_1, x_2]$  with the form  $P(x_1, x_2) = P_1(x_1)x_2 + P_0(x_1)$  obeying the following conditions.

- $\partial_1^j P(r) = 0$  for j = 0, ..., l 1.
- $|P| \le C(\epsilon)^l ||r_1||^{\frac{l}{2} + \epsilon}$ , for any  $\epsilon > 0$ .
- The degree of P is  $\lesssim \epsilon^{-1} \left( l + \log_{\|r_1\|} \|r_2\| \right)$ .

*Proof.* We will find our solution by counting parameters. We will choose a degree D, and let  $P_0, P_1$  be polynomials of degree  $\leq D$ . The coefficients of  $P_0$  and  $P_1$  are  $\geq 2D$  integer variables at our disposal. We wish to satisfy the l equations

$$\partial_1^j P(r) = 0, j = 0, ..., l - 1.$$
 (1)

After a minor rewriting, each of these equations is a linear equation in the coefficients of P with integer coefficients. If we write  $P_1(x_1) = \sum_i b_i x_1^i$  and  $P_0(x_1) = \sum_i a_i x^i$ , then

$$0 = q_1^D q_2(1/j!) \partial_1^j P(r) = q_2(\sum_i b_i \binom{i}{j} p_1^{i-j} q_1^{D-i+j}) + (\sum_i a_i \binom{i}{j} p_1^{i-j} q_1^{D-i+j} p_2).$$

The size of the coefficients in the equations is  $\leq 2^{D} ||r_1||^{D} ||r_2||$ .

By Siegel's lemma on integer solutions of linear integer equations (in the last lecture), we find a non-zero integer solution of these equations with

$$|P| \le \left[3D \cdot 2^D \|r_1\|^D \|r_2\|\right]^{\frac{l}{2D-l}} \le C^l \|r_1\|^{l\frac{D}{2D-l}} \|r_2\|^{\frac{l}{2D-l}}.$$

We choose  $D = 1000\epsilon^{-1}l + 1000\epsilon^{-1}\log_{\|r_1\|}\|r_2\|$ . With this value of D,  $\frac{D}{2D-l} \leq \epsilon/10$ , and so the exponent of  $\|r_1\|$  is almost l/2. Also, the term  $\|r_2\|^{\frac{l}{2D-l}} \leq \|r_1\|^{\epsilon/10}$ .

Combining our parameter counting with the elementary example  $q_2x_2 - p_2$ , we can find P vanishing to order l at r with |P| on the order of  $\min(||r_1||^{l/2}, ||r_2||)$ . The following result shows that these examples are quite sharp. I believe it is a special case of a lemma of Schneider.

**Proposition 1.2.** (Schneider) If  $P(x_1, x_2) = P_1(x_1)x_2 + P_0(x_1) \in \mathbb{Z}[x_1, x_2]$ , and  $r \in \mathbb{Q}^2$ , and  $\partial_1^j P(r) = 0$  for j = 0, ..., l - 1, and if  $l \ge 2$ , then

$$|P| \ge \min((2DegP)^{-1}||r_1||^{\frac{l-1}{2}}, ||r_2||).$$

Remark. We need to assume that  $l \geq 2$  to get any estimate. If we have vanishing only to order 1, then we could have  $P(x_1, x_2) = 2x_1 - x_2$ , which vanishes at  $(r_1, 2r_1)$  for any rational number  $r_1$ . As soon as  $l \geq 2$ , the size of |P| constrains the complexity of r. It can still happen that one component of r is very complicated, but they can't both be very complicated.

*Proof.* Our assumption is that

$$\partial^{j} P_{1}(r_{1})r_{2} + \partial^{j} P_{0}(r_{1}) = 0, 0 < j < l - 1.$$

Let V(x) be the vector  $(P_1(x), P_0(x))$ . Our assumption is that for  $0 \le j \le l-1$ , the derivatives  $\partial^j V(r_1)$  all lie on the line  $V \cdot (r_2, 1) = 0$ . In particular, any two of these derivatives are linearly dependent. This tells us that many determinants vanish. If V and W are two vectors in  $\mathbb{R}^2$ , we write [V, W] for the  $2 \times 2$  matrix with first column V and second column W. Therefore,

$$det[\partial^{j_1}V, \partial^{j_2}V](r_1) = 0$$
, for any  $0 \le j_1, j_2 \le l - 1$ .

Now it follows by the Liebniz rule that

$$\partial_j det[V, \partial V](r_1) = 0$$
, for any  $0 \le j \le l - 2$ .

Remark: Because the determinant is multilinear, we have the Leibniz rule  $\partial det[V, W] = det[\partial V, W] + det[V, \partial W]$ , which holds for any vector-valued functions  $V, W : \mathbb{R} \to \mathbb{R}^2$ .

Now  $det[V, \partial V]$  is a polynomial in one variable with integer coefficients. If this polynomial is non-zero, then by Gauss's lemma (see last lecture) we conclude that

$$|det[V, \partial V]| \ge ||r_1||^{l-1}.$$

Expanding out in terms of P, we have  $|det[V, \partial V]| = |\partial P_0 P_1 - \partial P_1 P_0| \le 2(Deg P)^2 |P|^2$ . Therefore, we have  $|P| \ge (2Deg P)^{-1} ||r_1||^{\frac{l-1}{2}}$ .

The polynomial  $det[V, \partial V]$  may also be identically zero. This is a degenerate case, and the polynomial must simplify dramatically. One possibility is that  $P_1$  is identically zero. In this case  $P(x_1, x_2) = P_0(x_1)$ , and by the Gauss lemma we have that  $|P| \geq ||r_1||^l$ . If  $P_1$  is not identically zero, then the derivative of the ratio  $P_0/P_1$ is identically zero. (The numerator of this derivative is  $det[V, \partial V]$ .) In this case, the polynomial P factors as  $(q_2x_2 - p_2)\tilde{P}(x_1)$ , where  $\tilde{P}(x_1)$  has integer coefficients. (compare proof of Gauss lemma) In this case,  $|P| > ||r_2||$ .

The lower bounds on |P| in this lemma are pretty close to the upper bounds on |P| in the examples above. Speaking informally, both bounds are pretty close to  $\min(\|r_1\|^{l/2}, \|r_2\|).$ 

## 2. Polynomials that vanish at algebraic points

Our whole discussion can be generalized in a straightforward way to algebraic points instead of rational points. In the proof of Thue's theorem, we have an algebraic number  $\beta$ , and  $r_1$  and  $r_2$  are rational numbers that approximate  $\beta$  with very large heights. The point  $(r_1, r_2)$  is close to  $(\beta, \beta)$ . We are going to compare finding an integral polynomial that vanishes to high order at  $(\beta, \beta)$  and finding an integral polynomial that vanishes to high order at  $(r_1, r_2)$ .

By using parameter counting, we will see that there is an integral polynomial vanishing to high order at  $(\beta, \beta)$  whose coefficients are much smaller than what we could find for a polynomial vanishing to high order at  $(r_1, r_2)$ .

**Proposition 2.1.** Let  $\beta \in \mathbb{R}$  be an algebraic number. For any natural number l, and any  $\epsilon > 0$ , there is a polynomial  $P \in \mathbb{Z}[x_1, x_2]$  with the form  $P(x_1, x_2) =$  $P_1(x_1)x_2 + P_0(x_1)$  with the following properties.

- $\partial_1^j P(\beta, \beta) = 0$  for  $0 \le j \le l 1$ .  $|P| \le C(\beta)^{l/\epsilon}$ .
- The degree of P is  $< (1+\epsilon)(1/2)deq(\beta)l+1$ .

*Proof.* This Proposition follows by the same parameter counting argument as above. There is one significant new idea in order to deal with algebraic numbers. We let D a degree to choose later. As above, we write  $P_1(x) = \sum_{i=0}^{D} b_i x^i$  and  $P_0(x) = \sum_{i=0}^{D} a_i x^i$ . The coefficients  $a_i$  and  $b_i$  are  $\geq 2D$  integer variables at our disposal. For each  $0 \leq 2D$  $j \leq l-1$ , our vanishing equation is

$$0 = (1/j!)\partial_1^j P(\beta, \beta) = \sum_i b_i \binom{i}{j} \beta^{i-j+1} + \sum_i a_i \binom{i}{j} \beta^{i-j}. \tag{1}$$

This is a linear equation in  $a_i, b_i$  with coefficients in  $\mathbb{Z}[\beta]$ . We will see that it is equivalent to  $deq(\beta)$  linear equations with coefficients in  $\mathbb{Z}$ . Since  $\beta$  is an algebraic number, we will check that  $1, \beta, ..., \beta^{deg(\beta)-1}$  form a basis for the vector space  $\mathbb{Q}[\beta]$  over the field  $\mathbb{Q}$ . In particular, any power  $\beta^i$  can be expanded as a rational combination of  $1, \beta, ..., \beta^{deg(\beta)-1}$ . Substituting in, we can rewrite equation (1) in the form:

$$0 = \sum_{k=0}^{\deg(\beta)-1} \beta^k \left[ \sum_i b_i B_{ik} + \sum_i a_i A_{ik} \right] = 0,$$

where  $A_{ik}$  and  $B_{ik}$  are rational numbers. Since  $1, \beta, ..., \beta^{deg(\beta)-1}$  are linearly independent over  $\mathbb{Q}$ , this list of equations is equivalent to the  $deg(\beta)$  equations

$$\sum_{i} b_{i} B_{ik} + \sum_{i} a_{i} A_{ik} = 0, \text{ for all } 0 \le k \le deg(\beta) - 1.$$
 (2)

After multiplying by a large constant to clear the denominators, we get  $deg(\beta)$  equations with integer coefficients. In total, our original l equations  $\partial_1^j P(r) = 0$  for j = 0, ..., l-1 are equivalent to  $deg(\beta)l$  integer linear equations in the coefficients of P. Since we have > 2D coefficients, we can find a non-trivial integer solution as long as  $D \ge (1/2)deg(\beta)l$ .

Our next task is to estimate the size of the solution. To do this, we need to estimate the heights of the coefficients  $A_{ik}$ ,  $B_{ik}$ . Also we get a much better estimate by taking D slightly larger than  $(1/2)deg(\beta)l$ , and for this reason we choose D to be the least integer  $\geq (1 + \epsilon)(1/2)deg(\beta)l$ . To estimate the heights of  $A_{ik}$ ,  $B_{ik}$ , we consider more carefully how to expand  $\beta^d$  in terms of  $1, \beta, ..., \beta^{d-1}$ .

**Lemma 2.2.** Suppose  $Q(\beta) = 0$ , where  $Q \in \mathbb{Z}[x]$  with degree  $deg(Q) = deg(\beta)$  and leading coefficient  $q_{deg(beta)}$ . Then for any  $d \geq 0$ , we can write

$$q_{deg(\beta)}^d \beta^d = \sum_{k=0}^{deg(\beta)-1} A_{kd} \beta^k,$$

where  $A_{kd} \in \mathbb{Z}$  and  $|A_{kd}| \leq [2|Q|]^d$ .

*Proof.* We have  $0 = Q(\beta) = \sum_{k=0}^{\deg(\beta)} q_k \beta^k$ . We do the proof by induction on d, starting with  $d = \deg(\beta)$ . For  $d = \deg(\beta)$ , the equation  $Q(\beta) = 0$  directly gives

$$q_{deg(beta)}^{deg(\beta)} \beta^{deg(\beta)} = \sum_{k=0}^{deg(\beta)-1} (-q_k) \beta^k. \tag{*}$$

If we multiply both sides by  $q_{deg(\beta)}^{deg(\beta)-1}$ , we get a good expansion for the case  $d = deg(\beta)$ . Now we proceed by induction. Suppose that  $q_{deg(\beta)}^d \beta^d = \sum_{k=0}^{deg(\beta)-1} A_{kd}\beta^k$ . Multiplying by  $q_{deg(\beta)}\beta$ , we get

$$q_{\deg(\beta)}^{\deg(\beta)+1}\beta^{\deg(\beta)+1} = \sum_{k=0}^{\deg(\beta)-1} A_{kd}q_{\deg(\beta)}\beta^{k+1} = \sum_{k=1}^{\deg(\beta)-1} A_{k-1,d}q_{\deg(\beta)}\beta^k + \sum_{k=0}^{\deg(\beta)-1} A_{\deg(\beta)-1,d}(-q_k)\beta^k.$$

Plugging in this lemma, we see that  $q_{deg(\beta)}^D A_{ik}$ ,  $q_{deg(\beta)}^D B_{ik}$  are integers of size  $\leq D[2|Q|]^D$ . The integer matrix that we are solving has coefficients of size  $\leq D[2|Q|]^D$ . It is a matrix with dimensions  $(2D+2) \times deg(\beta)l$ , and so it has operator norm  $\leq (2D+2)D[2|Q|]^D \leq C(\beta)^D$ .

Now applying Siegel's lemma, we see that we can find an integer solution P with |P| bounded by

$$C(\beta)^{D\frac{deg(\beta)l}{2D-deg(\beta)l}} \le C(\beta)^{D/\epsilon}.$$

Since  $D \leq C(\beta)l$ , we can redefine  $C(\beta)$  so that  $|P| \leq C(\beta)^{l/\epsilon}$ .

## 3. Summary

Suppose that  $\beta$  is an algebraic number, and that  $r_1, r_2$  are two very good rational approximations of  $\beta$ . We may suppose that  $||r_1||$  is very large and  $||r_2||$  is (much) larger. Say  $||r_2|| \sim ||r_1||^m$ .

We consider polynomials  $P \in \mathbb{Z}[x_1, x_2]$  of the simple form  $P(x_1, x_2) = P_1(x_1)x_2 + P_0(x_1)$ . We can arrange that  $\partial_1^j P(\beta, \beta) = 0$  for  $0 \le j \le m-1$  with  $|P| \le C(\beta)^m$ . On the other hand, if  $\partial_1^j P(r) = 0$  for  $0 \le j \le l-1$ , then we must have  $|P| \gtrsim ||r_1||^{l/2}$ . Since  $||r_1||$  is much larger than  $C(\beta)$ , it follows that l must be much smaller than m. This creates a certain tension.

As we will see, if r was too close to  $(\beta, \beta)$ , than P would have to vanish too much at r, giving a contradiction.

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### PROOF OF THUE'S THEOREM - PART III

## 1. Outline of the proof of Thue's theorem

**Theorem 1.1.** (Thue) If  $\beta$  is an irrational algebraic number, and  $\gamma > \frac{\deg(\beta)+2}{2}$ , then there are only finitely many integer solutions to the inequality

$$|\beta - \frac{p}{q}| \le |q|^{-\gamma}.$$

By using parameter counting, we constructed polynomials P with integer coefficients that vanish to high order at  $(\beta, \beta)$ . The degree of P and the size of P are controlled.

If  $r_1$ ,  $r_2$  are rational numbers with large height, then we proved that P cannot vanish to such a high order at  $r = (r_1, r_2)$ . For some j of controlled size, we have  $\partial_1^j P(r) \neq 0$ . Since P has integer coefficients, and r is rational,  $|\partial_1^j P(r)|$  is bounded below.

Since P vanishes to high order at  $(\beta, \beta)$ , we can use Taylor's theorem to bound  $|\partial_1^j P(r)|$  from above in terms of  $|\beta - r_1|$  and  $|\beta - r_2|$ . So we see that  $|\beta - r_1|$  or  $|\beta - r_2|$  needs to be large.

Here is the framework of the proof. We suppose that there are infinitely many rational solutions to the inequality  $|\beta - r| \leq ||r||^{-\gamma}$ . Let  $\epsilon > 0$  be a small parameter we will play with. We let  $r_1$  be a solution with very large height, and we let  $r_2$  be a solution with much larger height. Using these, we will prove that  $\gamma \leq \frac{\deg(\beta)+2}{2} + C(\beta)\epsilon$ .

## 2. The polynomials

For each integer  $m \geq 1$ , we proved that there exists a polynomial  $P = P_m \in \mathbb{Z}[x_1, x_2]$  with the following properties:

- (1) We have  $\partial_1^j P(\beta, \beta) = 0$  for j = 0, ..., m 1.
- (2) We have  $Deg_2P \leq 1$  and  $Deg_1P \leq (1+\epsilon)\frac{deg(\beta)}{2}m$ .
- (3) We have  $|P| \leq C(\beta, \epsilon)^m$ .

#### 3. The rational point

Suppose that  $r_1, r_2$  are good rational approximations to  $\beta$  in the sense that

$$\|\beta - r_i\| \leq \|r_1\|^{-\gamma}.$$

Also, we will suppose that  $||r_1||$  is sufficiently large in terms of  $\beta$ ,  $\epsilon$ , and that  $||r_2||$  is sufficiently large in terms of  $\beta$ ,  $\epsilon$ , and  $||r_1||$ .

If  $l \geq 2$  and  $\partial_1^j P(r) = 0$  for j = 0, ..., l - 1, then we proved the following estimate:

$$|P| \ge \min((2degP)^{-1}||r_1||^{\frac{l-1}{2}}, ||r_2||).$$

Given our bound for |P|, we get

$$C(\beta, \epsilon)^m \ge \min(\|r_1\|^{\frac{l-1}{2}}, \|r_2\|).$$

From now on, we only work with m small enough so that

$$C(\beta, \epsilon)^m < ||r_2||.$$
 Assumption

Therefore,  $||r_1||^{\frac{l-1}{2}} \leq C(\beta, \epsilon)^m$ . We assume that  $||r_1||$  is large enough so that  $||r_1||^{\epsilon} > C(\beta, \epsilon)$ , and this implies that  $l \leq \epsilon m$ . Therefore, there exists some  $j \leq \epsilon m$  so that  $\partial_j^j P(r) \neq 0$ .

Let  $\tilde{P} = (1/j!)\partial_1^j P$ . The polynomial  $\tilde{P}$  has integer coefficients, and  $|\tilde{P}| \leq 2^{degP}|P|$ . Therefore,  $\tilde{P}$  obeys essentially all the good properties of P above:

- (1) We have  $\partial_1^j \tilde{P}(\beta, \beta) = 0$  for  $j = 0, ..., (1 \epsilon)m 1$ .
- (2) We have  $Deg_2\tilde{P} \leq 1$  and  $Deg_1\tilde{P} \leq (1+\epsilon)\frac{deg(\beta)}{2}m$ .
- (3) We have  $|\tilde{P}| \leq C(\beta, \epsilon)^m$ .
- (4) We also have  $\tilde{P}(r) \neq 0$ .

Since  $\tilde{P}$  has integer coefficients, we can write  $\tilde{P}(r)$  as a fraction with a known denominator:  $q_1^{Deg_1\tilde{P}}q_2^{Deg_2\tilde{P}}$ . Therefore,

$$|\tilde{P}(r)| \ge ||r_1||^{-Deg_1\tilde{P}} ||r_2||^{-Deg_2\tilde{P}} \ge ||r_1||^{-(1+\epsilon)\frac{deg(\beta)}{2}m} ||r_2||^{-1}$$

We make some notation to help us focus on what's important. In our problem, terms like  $||r_1||^m$  or  $||r_2||$  are substantial, but terms like  $||r_1||^{\epsilon m}$  or  $||r_1||$  are minor in comparison. Therefore, we write  $A \lesssim B$  to mean

 $A \leq ||r_1||^{a\epsilon m} ||r_1||^b$ , for some constants a, b depending only on  $\beta$ .

Recall that  $||r_1||^{\epsilon}$  is bigger than  $C(\beta, \epsilon)$ , so  $C(\beta, \epsilon)^m \lesssim 1$ . Our main inequality for this section is

$$|\tilde{P}(r)| \gtrsim ||r_1||^{-\frac{\deg(\beta)}{2}m} ||r_2||^{-1}.$$
 (1)

# 4. Taylor's theorem estimates

We recall Taylor's theorem.

**Theorem 4.1.** If f is a smooth function on an interval, then f(x + h) can be approximated by its Taylor expansion around x:

$$f(x+h) = \sum_{j=0}^{m-1} (1/j!) \partial_j f(x) h^j + E,$$
where the error term E is bounded by
$$|E| \leq (1/m!) \sup_{y \in [x,x+h]} |\partial_m f(y)|.$$

In particular, if f vanishes to high order at x, then f(x+h) will be very close to f(x).

**Corollary 4.2.** If Q is a polynomial, and Q vanishes at x to order  $m \ge 1$ , and if  $|h| \le 1$ , then

$$|Q(x+h)| \le C(x)^{degQ}|Q|h^m.$$

*Proof.* We see that  $(1/m!)\partial^m Q$  is a polynomial with coefficients of size  $\leq 2^{degQ}|Q|$ . We evaluate it at a point y with  $|y| \leq |x| + 1$ . Each monomial has norm  $\leq 2^{degQ}|Q|(|x|+1)^{degQ}$ , and there are degQ monomials.

Let  $Q(x) = \tilde{P}(x, \beta)$ . The polynomial Q vanishes to high order  $(1 - \epsilon)m$  at  $x = \beta$ , and  $|Q| \leq C(\beta, \epsilon)^m$ .

From the corollary we see that

$$|\tilde{P}(r_1,\beta)| \le C(\beta,\epsilon)^m |\beta - r_1|^{(1-\epsilon)m}$$
.

On the other hand,  $\partial_2 \tilde{P}$  is bounded by  $C(\beta, \epsilon)^m$  in a unit disk around  $(\beta, \beta)$ , and so

$$|\tilde{P}(r_1, r_2) - \tilde{P}(r_1, \beta)| \le C(\beta, \epsilon)^m |\beta - r_2|.$$

Combining these, we see that

$$|\tilde{P}(r)| \lesssim |\beta - r_1|^{(1-\epsilon)m} + |\beta - r_2| \lesssim ||r_1||^{-\gamma m} + ||r_2||^{-\gamma}.$$
 (2)

#### 5. Putting it together

As long as  $||r_1||^{\epsilon} > C(\beta, \epsilon)$  and  $||r_2|| > C(\beta, \epsilon)^m$ , we have proven the following inequality:

$$||r_1||^{-\frac{\deg(\beta)}{2}m}||r_2||^{-1} \lesssim ||r_1||^{-\gamma m} + ||r_2||^{-\gamma}$$

Now we can choose m. As m increases, the right-hand side decreases until  $||r_1||^m \sim ||r_2||$ , and then the  $||r_2||^{-\gamma}$  term becomes dominant. Therefore, we choose m so that

$$||r_1||^m \le ||r_2|| \le ||r_1||^{m+1}$$
.

We see that  $||r_2|| \ge ||r_1||^m > C(\beta, \epsilon)^m$ , so the assumption about  $r_2$  and m above is satisfied. The inequality becomes

$$||r_1||^{-\frac{\deg(\beta)}{2}m-m} \lesssim ||r_1||^{-\gamma m}.$$

Multiplying through to make everything positive, we get

$$||r_1||^{\gamma m} \lesssim ||r_1||^{\frac{\deg(\beta)+2}{2}m}.$$

Unwinding the  $\lesssim$ , this actually means

$$||r_1||^{\gamma m} \le ||r_1||^{b+a\epsilon m + \frac{deg(\beta)+2}{2}m}.$$

(If we had been more explicit, we could have gotten specific values for a, b, but it doesn't matter much.)

Taking the logarithm to base  $||r_1||$  and dividing by m, we get

$$\gamma \le (b/m) + a\epsilon + \frac{deg(\beta) + 2}{2}.$$

If  $||r_2||$  is large enough compared to  $||r_1||$ , then  $(1/m) \leq \epsilon$ , and we have  $\gamma \leq (a+b)\epsilon + \frac{\deg(\beta)+2}{2}$ . Taking  $\epsilon \to 0$  finishes the proof.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## HOW COMBINATORICS AND ANALYSIS INTERACT

## 1. Loomis-Whitney Inequality

Let X be a set of unit cubes in the unit cubical lattice in  $\mathbb{R}^n$ , and let |X| be its volume. Let  $\Pi_j$  be the projection onto the  $x_j^{\perp}$  hyperplane. The motivating question is: if  $\Pi_j$  is small for all j, what can we say about |X|?

**Theorem 1.1** (Loomis-Whitney 50's). If  $|\Pi_i(X)| \leq A$ , then  $|X| \lesssim A^{\frac{n}{n-1}}$ .

**Remark.** The sharp constant in the  $\lesssim$  is 1. The original proof is by using H older's inequality repeatedly.

Define a *column* to be the set of cubes obtained by starting at any cube and taking all cubes along a line in the  $x_j$ -direction.

**Lemma 1.2** (Main lemma). If  $\sum |\Pi_j(X)| \leq B$ , then there exists a column of cubes with between 1 and  $B^{\frac{1}{n-1}}$  cubes of X.

*Proof.* Suppose not, so every column has  $> B^{\frac{1}{n-1}}$  cubes. This means that there are  $> B^{\frac{1}{n-1}}$  cubes in some  $x_1$ -line. Taking the  $x_2$ -lines through those, there are  $> B^{\frac{2}{n-1}}$  cubes in some  $x_1, x_2$ -plane, and so on. Repeating this n-1 times, we get > B cubes in the  $x_1, \ldots, x_{n-1}$ -plane, a contradiction.

Corollary 1.3. If  $\sum_{j} |\Pi_{j}(X)| \leq B$ , then  $|X| \leq B^{\frac{n}{n-1}}$ .

*Proof.* Let X' be X with its smallest column removed. Then  $\sum |\Pi_j(X')| \leq B - 1$ , so by induction we get  $|X'| \leq (B-1)^{\frac{n}{n-1}}$ , hence  $|X| \leq B^{\frac{1}{n-1}} + |X'|$ .

Note that Corollary 1.3 implies Theorem 1.1.

**Theorem 1.4** (more general Loomis-Whitney). If U is an open set in  $\mathbb{R}^n$  with  $|\Pi_i(U)| \leq A$ , then  $|U| \lesssim A^{\frac{n}{n-1}}$ .

*Proof.* Take  $U_{\varepsilon} \subset U$  be a union of  $\varepsilon$ -cubes in  $\varepsilon$ -lattice. Then  $|U_{\varepsilon}| \lesssim A^{\frac{n}{n-1}}$  and  $|U_{\varepsilon}| \to |U|$ .

Corollary 1.5 (Isoperimetric inequality). If U is a bounded open set in  $\mathbb{R}^n$ , then  $Vol_n(U) \lesssim Vol_{n-1}(\partial U)^{\frac{n}{n-1}}$ .

Date: November 28, 2012.

*Proof.* By projection onto translates of each  $x_j$ -hyperplane, we see that  $|\Pi_j(U)| \leq \operatorname{Vol}_{n-1}(\partial U)$ , so we may apply Theorem 1.4.

**Remark.** The fact that U was bounded was used to define the projection of U onto translates of each  $x_i$ -hyperplane.

#### 2. Sobolev Inequality

Let  $u \in C^1_{\text{comp}}(\mathbb{R}^n)$  satisfy  $\int |\nabla u| = 1$ . How big can u be? We would like the find the right notion of size for u that answers this question.

**Theorem 2.1** (Sobolev inequality). If  $u \in C^1_{comp}(\mathbb{R}^n)$ , then

$$||u||_{L^{\frac{n}{n-1}}} \lesssim ||\nabla u||_{L^1}.$$

Here, the  $L^p$ -norm  $||u||_{L^p}$  is given by

$$||u||_{L^p} = \left(\int |u|^p\right)^{1/p}$$

so that  $||h \cdot \chi_A||_p = h \cdot |A|^{1/p}$ . For some context about  $L^p$ -norms, for a function u, let  $S(h) := \{x \in \mathbb{R}^n \mid |u(x)| > h\}$ .

**Proposition 2.2.** If  $||u||_p \leq M$ , then  $|S(h)| \leq M^p h^{-p}$ .

*Proof.* Just estimate 
$$M^p = \int |u|^p \ge h^p |S(h)|$$
.

We now prove the Sobolev inequality. A first try is the following bound.

**Lemma 2.3.** If 
$$u \in C^1_{comp}(\mathbb{R}^n)$$
,  $|\Pi_j(S(h))| \leq h^{-1} \cdot ||\nabla u||_{L^1}$ .

*Proof.* For  $x \in S(h)$ , take a line  $\ell$  in the  $x_j$ -direction. It eventually reaches a point x' where u = 0, so  $\int_{\ell} |\nabla U| \ge h$  by the fundamental theorem of calculus. This means that

$$||\nabla u||_{L^1} \ge \int_{\Pi_j(S(h)) \times \mathbb{R}} |\nabla u| = \int_{\Pi_j(S(h))} \int_{\mathbb{R}} |\nabla u| dx_j dx_{\text{other}} \ge |\Pi_j(S(h))| \cdot h. \qquad \Box$$

If we apply Theorem 1.4 to the output of Lemma 2.3, we see that

$$|S(h)| \lesssim h^{-\frac{n}{n-1}} \cdot ||\nabla u||^{\frac{n}{n-1}},$$

which looks like the output of Proposition 2.2. So we would like to establish something like the converse in this case. For this, we require a more detailed analysis.

**Lemma 2.4** (Revised version of Lemma 2.3). Let  $S_k := \{x \in \mathbb{R}^n \mid 2^{k-1} \leq |u(x)| \leq 2^k\}$ . If  $u \in C^1_{comp}(\mathbb{R}^n)$ , then we have

$$|\Pi_j S_k| \lesssim 2^{-k} \int_{S_{k-1}} |\nabla u|.$$

*Proof.* For  $x \in S_k$ , draw a line  $\ell$  in the  $x_j$ -direction through x. There is a point x' on  $\ell$  with u(x') = 0. Between x and x', there is some region on  $\ell$  where |u| is between  $2^{k-2}$  and  $2^{k-1}$ . Then we see that along each such  $\ell$ , we have

$$\int_{S_{k-1}\cap\ell} |\nabla u| \ge \frac{1}{4} 2^k.$$

Summing this along all  $\ell$  perpendicular to a translate of the  $x_j$ -hyperplane yields the result.

Corollary 2.5. 
$$|S_k| \lesssim 2^{-k\frac{n}{n-1}} \left( \int_{S_{k-1}} |\nabla u| \right)^{\frac{n}{n-1}}$$
.

Proof. Put Lemma 2.4 into Theorem 1.4.

Proof of Theorem 2.1. Take the estimate

$$\int |u|^{\frac{n}{n-1}} \sim \sum_{k=-\infty}^{\infty} |S_k| 2^{k\frac{n}{n-1}} \lesssim \sum_k \left( \int_{S_{k-1}} |\nabla u| \right)^{\frac{n}{n-1}} \leq \left( \int_{\mathbb{R}^n} |\nabla u| \right)^{\frac{n}{n-1}},$$

where in the last step we move the sum inside the  $\frac{n}{n-1}$ -power.

**Remark.** The sharp constant in Theorem 2.1 is provided by a smooth approximation to a step function where the width of the region of smoothing is very small.

# 3. $L^p$ estimates for linear operators

If  $f, q: \mathbb{R}^n \to \mathbb{R}$  or  $\mathbb{C}$ , define the convolution to be

$$(f \star g)(x) = \int_{\mathbb{R}^n} f(y)g(x - y)dy.$$

We can explain this definition by the following story. Suppose there is a factory at 0 which generates a cloud of pollution centered at 0 described by g(-y). If the density of factories at x is f(x), then the final observed pollution is  $f \star g$ .

We would like to study linear operators like  $T_{\alpha}f := f \star |x|^{-\alpha}$ , which means explicitly that

$$T_{\alpha}f(x) = \int f(y)|x-y|^{-\alpha}dy.$$

We will take  $\alpha$  in the range  $0 < \alpha < n$ , so that if  $f \in C^0_{\text{comp}}$  then the integral converges for each x. Operators like these occur frequently in PDE. Another example is the initial value problem for the wave equation.

**Example.** Let us first see how  $T_{\alpha}$  behaves on some examples for f.

1.  $\chi_{B_1}$ , where  $B_r$  is the ball of radius r. We see that

$$|T_{\alpha}\chi_{B_1}(x)| \sim \begin{cases} 1 & |x| \leq 1\\ |x|^{-\alpha} & |x| > 1. \end{cases}$$

2.  $\chi_{B_r}$ . We see that

$$|T_{\alpha}\chi_{B_r}(x)| \sim \begin{cases} r^n \cdot r^{-\alpha} & |x| \le r \\ r^n \cdot |x|^{-\alpha} & |x| > r. \end{cases}$$

2.1  $\delta$ , the delta function. Morally, this is given by  $\lim_{n\to\infty} r^{-n}\chi_{B_r}$ .

A question we would like to ask about  $T_{\alpha}$  is the following. Fix  $\alpha$  and n. For which p, q is there an inequality

$$(1) ||T_{\alpha}f||_q \lesssim ||f||_p$$

for all choices of f?

In some sense, this measures how much bigger  $T_{\alpha}$  can make f. First, we determine the answer in Examples 1 and 2. For Example 1,  $||\chi_{B_1}||_p \sim 1$ , and

$$||T_{\alpha}\chi_{B_1}||_1^1 \sim \int_{\mathbb{R}^n} (1+|x|)^{-\alpha q} dx,$$

which is finite if and only if  $\alpha q > n$ . So (1) holds in Example 1 if and only if  $\alpha q > n$ . Let us assume this from now on.

For Example 2,  $||\chi_{B_r}||_p \sim r^{n/p}$ . For  $||T_\alpha \chi_{B_r}||_q$ , the value is given by two terms, one coming from the ball  $|x| \leq r$  and the outside tail. The condition  $\alpha q > n$  says that the contribution of the tail is finite, so we get the estimate

$$||T_{\alpha}\chi_{B_r}||_q \sim ||r^{n-\alpha}\chi_{B_r}||_q \sim r^{n-\alpha+n/q}$$

Thus, we conclude that (1) holds in Example 2 if and only if  $\alpha \cdot q > n$  and  $r^{n/p} \lesssim r^{n-\alpha+n/q}$  for all r > 0. The latter condition is equivalent to  $n/p = n - \alpha + n/q$ .

For a general linear operator T, we would like to ask whether

$$||Tf||_q \lesssim ||f||_p$$

under the conditions that  $\alpha \cdot q > n$  and  $n/p = n - \alpha + n/q$ . If the answer is yes, we conclude that the characteristic functions of balls are in some sense typical for the action of T; otherwise, we would like to understand which functions f this fails for.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## HARDY-LITTLEWOOD-SOBOLEV INEQUALITY

Consider a kernel  $K_{\alpha}(x) := |x|^{-\alpha}$  and convolution  $T_{\alpha}f := f * K_{\alpha}$ . Last time, we looked at how  $T_{\alpha}$  works when  $f = \chi_{B_r}$  is the characteristic function on a ball of radius r.

**Proposition 0.1.**  $||T_{\alpha}\chi_{B_r}||_q \lesssim ||\chi_{B_r}||_p$  if and only if  $\alpha q > n$  and  $n - \alpha + \frac{n}{q} = \frac{n}{p}$ . Or equivalently, p > 1 and  $\alpha = n(1 - \frac{1}{q} + \frac{1}{p})$ .

In fact, this result is true for general cases.

**Theorem 0.2.** (Hardy-Littlewood-Sobolev) If p > 1 and  $\alpha = n(1 - \frac{1}{q} + \frac{1}{p})$ , then  $||T_{\alpha}f||_q \lesssim ||f||_p$ .

Apart from our previous examples, the next simplest example would be  $f := \sum_{j} \chi_{B_j}$  where  $B_j$  are some balls. It is easy to treat nonoverlapping balls, but rather difficult in overlapping cases. So, it might be helpful to know about the geometry of overlapping balls.

#### 1. Ball doubling

**Lemma 1.1.** (Vitali Covering Lemma) If  $\{B_i\}_{i\in I}$  is a finite collection of balls, then there exist a subcollection  $J\subset I$  such that  $\{B_j\}_{j\in J}$  are disjoint but  $\bigcup_{i\in I} B_i\subset\bigcup_{j\in J} 3B_j$ .

What happens if I is infinite? It is no longer true for infinite I: consider  $\{B(0,r): r \in \mathbb{R}^+\}$ . Any two of them are overlapping, so any disjoint subcollection can contain only one ball. You cannot cover whole space by a bounded ball, so the theorem is false for this case. How can we fix it? If we loosen the conclusion to cover only a compact set  $K \subset \bigcup_{i \in I} B_i$ , then we can always find a disjoint subcollection  $J(K) \subset I$  such that  $K \subset \bigcup_{i \in J(K)} 3B_i$ .

From Vitali covering lemma, we get the following:

**Lemma 1.2.** (Ball doubling) If  $\{B_i\}_{i\in I}$  is a finite collection of balls, then  $|\bigcup 2B_i| \le 6^n |\bigcup B_i|$ .

*Proof.* From the proof of Vitali Covering Lemma, for each  $B_i$  we can find some  $j \in J$  such that  $B_i \subset 3B_j$ . So,  $2B_i \subset 6B_j$ . Hence  $|\bigcup 2B_i| \leq |\bigcup 6B_j| \leq 6^n \sum |B_j| = 6^n |\bigcup B_j|$ .

Is it sharp? It seems to be  $2^n$  instead of  $6^n$ , but I'm not sure and at least hard to prove. This coefficient is not so important for the proof be given later, so let's go over it.

### 2. HARDY-LITTLEWOOD MAXIMAL FUNCTION

Denote the average of f on A by  $\oint_A f := \frac{1}{\operatorname{Vol}A} \int_A f$ . The Hardy-Littlewood maximal function of f is defined to be  $Mf(x) := \sup_r \oint_{B(x,r)} |f|$ . Let  $S_g(h) := \{x \in \mathbb{R}^n : |g| > h\}$ . Then,

**Lemma 2.1.**  $|S_{Mf}(h)| \lesssim h^{-1} ||f||_1$ .

Proof. For each  $x \in S_{Mf}(h)$ , there exists r(x) such that  $\oint_{B(x,r(x))} |f| \ge h$ , so  $\oint_{B(x,r(x))} |f| \ge h$   $|f| \ge h$ , so  $f_{B(x,r(x))} |f| \ge h$ . These  $f_{B(x)}(x,r(x))$  cover  $f_{Mf}(x)$ , so by Vitali covering lemma, we can find disjoint  $f_{B}(x)$  whose multiple cover  $f_{Mf}(h)$ . Hence,

$$|S_{Mf}(h)| \lesssim \sum_{j} |B_{j}| \lesssim h^{-1} \oint_{\bigcup B_{j}} |f| \leq h^{-1} ||f||_{1}.$$

Now we can estimate the  $L_p$ -norm of Mf by that of f.

Proposition 2.2.  $||Mf||_p \lesssim ||f||_p$ .

One naive approach would be dividing the range and estimate in each range. Namely, let  $T_{Mf}(2^k) := \{x \in \mathbb{R}^n : 2^k < |Mf| \le 2^{k+1}\} \subset S_{Mf}(2^k)$  and we have

$$\int |Mf|^p \sim \sum_{k=-\infty}^{\infty} |T_{Mf}(2^k)| 2^{kp} \lesssim \sum_k 2^{-k} 2^{kp} ||f||_1,$$

but the summation in the righthand side diverges. We need a slight modification of the previous lemma.

**Lemma 2.3.**  $|S_{Mf}(h)| \lesssim h^{-1} \int_{S_f(h/2)} |f|$ .

Proof. In the previous proof, we found disjoint  $B_j$  which covering  $S_{Mf}(h)$  such that  $\int_{B_j} |f| \geq h|B_j|$ . However, we also have  $\int_{B_j \setminus S_f(h/2)} |f| \leq \frac{h}{2}|B_j|$ , so  $\int_{B_j \cap S_f(h/2)} |f| \geq \frac{h}{2}|B_j|$ . Do the same estimate with  $B_j \cap S_f(h/2)$  instead of  $B_j$  and get the desired result.

Now we can prove the proposition.

*Proof.* Use the same approach above with our modified lemma.

$$\int |Mf|^p \lesssim \sum_{k=-\infty}^{\infty} |S_{Mf}(2^k)| 2^{kp} \lesssim \sum_k 2^{k(p-1)} \int_{S_f(2^{k-1})} |f|.$$

By interchanging summation and integral, we have

$$\int |f| \sum_{2^{k-1} \le |f|} 2^{k(p-1)} \sim \int |f| \cdot |f|^{p-1} = ||f||_p^p.$$

So,  $||Mf||_p \lesssim ||f||_p$ .

#### 3. Proof of HLS Inequality

Step 1.  $T_{\alpha}f(x)$  can be written in terms of  $\oint_{B(x,r)} f$ .

### Lemma 3.1.

$$T_{\alpha}f(x) = \int_{0}^{\infty} r^{n-\alpha-1} \left( \oint_{B(x,r)} f \right) dr.$$

*Proof.* Just a computation.

Step 2. Upper bounds of  $\oint_{B(x,r)} f$ . One trivial upper bound is Mf(x) by definition. Also, we can get

$$\oint_{B(x,r)} f \lesssim r^{-n} \int_{B(x,r)} |f| \lesssim r^{-n} ||f||_p r^{n(p-1)/p} = r^{-n/p} ||f||_p$$

by Hölder. We would fail if we only use one of them. Rather, fix  $r_{crit}(x)$  and use Mf(x) for  $r \leq r_{crit}$ ,  $L^p$  bound for  $r \geq r_{crit}$ . This approximation always gives us  $|T_{\alpha}f(x)| \lesssim (Mf)^A ||f||_p^B$  for some A, B with A + B = 1.

Step 3.  $\int |T_{\alpha}f|^q \lesssim \|f\|_p^{Bq} \int (Mf)^{Aq} \lesssim \|f\|_p^{Bq} \|f\|_{Aq}^{Aq}$  as long as Aq > 1. If p = Aq, then we have  $\int |T_{\alpha}f|^q \lesssim \|f\|_p^q$ , so  $\|T_{\alpha}f\|_q \lesssim \|f\|_p$ . This case together with Aq > 1 is exactly the hypothesis condition in the theorem. Also, we already know that this condition is the only possible case, so we are done. You may calculate  $r_{crit}$ , A, B to check.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# OSCILLATING INTEGRALS AND THE KAKEYA PROBLEM

### 1. The ball multiplier in Fourier analysis

We give a little background in Fourier analysis. The Fourier transform in  $\mathbb{R}^n$  is defined by

$$\hat{f}(\omega) = \int_{\mathbb{R}^n} f(x)e^{-2\pi i\omega x} dx.$$

In this short background section, we will assume that f is continuous and compactly supported. With these assumptions, the integral above is clearly defined. A function can be recovered from its Fourier transform as follows:

**Proposition 1.1.** If f is a smooth compactly supported function, then

$$f(x) = \int_{\mathbb{R}^n} \hat{f}(\omega) e^{2\pi i \omega x} d\omega.$$

As long as f is  $C^{\infty}$  smooth,  $\hat{f}$  decays rapidly, and this integral is defined. If f is just continuous with compact support, then  $\hat{f}$  is a continuous function, but it may not be integrable. In this case, it requires thought to understand what the right-hand side should mean. Partly for this reason, Fourier analysts considered integrating just over a ball:

$$M_R f(x) := \int_{B^n(R)} \hat{f}(\omega) e^{2\pi i \omega x} d\omega.$$

If f is continuous with compact support, then  $M_R f$  is well defined for any finite R. It is natural to ask whether  $M_R f$  converges to f as  $R \to \infty$ . Here are some fundamental results about this question.

- At a particular point x,  $M_R f(x)$  may not converge at all. (19th century)
- The functions  $M_R f$  converge to f in  $L^2$  (in every dimension). (One of the motivations for defining  $L^2$  convergence in the early 20th century)
- If n = 1, then  $M_R f$  converges to f in  $L^p$  for every 1 . (Riesz, early 20th century.)

Question: For a given dimension n, for which p do we have  $M_R f \to f$  in  $L^p$  for all  $f \in C^0_{comp}$ ?

The operators  $M_R$  are all in a family, and if one gets a good understand of  $M_1$ , then by rescaling one can also get a good understanding of any  $M_R$ . By standard analysis tricks, this question is equivalent to the following:

Question: For a given dimension n, for which p do we have  $||M_1f||_p \lesssim ||f||_p$ ?

# 2. Oscillating kernels

Last time we considered the kernel  $K_{\alpha}(x) := |x|^{-\alpha}$ . Now we consider an oscillating version of this kernel.

$$\tilde{K}_{\alpha}(x) := [1 + |x|]^{-\alpha} \cos|x|.$$

The function  $\tilde{K}_{\alpha}(x)$  is still radial. Near the origin, it's bounded instead of having a sharp peak. Also, it oscillates with the radius, so that it has positive and negative parts. If one dropped a stone into a pond and looked at the ripples, the shape would be a little bit like  $\tilde{K}_{\alpha}$ , with a modest peak in the center, and then waves going outward and getting smaller the farther they are from the center.

We define  $\tilde{T}_{\alpha}f := f * \tilde{K}_{\alpha}$ .

The operator  $M_1$  turns out to be very similar to  $\tilde{T}_{\frac{n+1}{2}}$ . Although they are not exactly equal, all the arguments that we will make about  $\tilde{T}_{\frac{n+1}{2}}$  apply just as well to  $M_1$ . From now on, we'll just talk about  $\tilde{T}_{\alpha}$ .

Our main question is the following, what are all the  $L^p$  estimates obeyed by  $\tilde{T}_{\alpha}$ ? At first sight, this problem looks like a small variation on the Hardy-Littlewood-Sobolev problem - it's just a similar kernel with some oscillations added. Because of the oscillations, there are positive and negative terms in the integrals, and some

cancellation occurs. The key issue is to understand how much cancellation needs to

occur.

We will focus on estimates of the form  $||T_{\alpha}f||_p \lesssim ||f||_p$ , so that we have less parameters to keep track of.  $(L^p - L^q)$  estimates are interesting too, but all of the essential issues already appear in this main case.)

Example 1. We let  $f = \chi_{B_r}$  for some r. It's already somewhat complicated to estimate  $\tilde{T}_{\alpha}f$  because of the cancellation in the integral. But if f is < 1/100, then at most points x, there is no cancellation in the integral

$$\tilde{T}_{\alpha}f(x) = \int_{B(r)} [1 + |x - y|]^{-\alpha} \cos|x - y| dy.$$

The most interesting is to take r=1/100. In this case,  $\tilde{T}_{\alpha}f \sim \tilde{K}_{\alpha}$ . In this case, we have  $||f||_p \sim 1$ , and  $\int |\tilde{T}_{\alpha}f|^p \sim \int_{\mathbb{R}^n} (1+|x|)^{-\alpha p}$ . So  $||\tilde{T}_{\alpha}f||_p < \infty$  iff  $\alpha p > n$ .

Considering  $r \leq 1/100$  just gives the same information.

Example 2. (Focusing example) For large r, there is something better to do than  $\chi_{B_r}$ . Suppose that we want to make  $\tilde{T}_{\alpha}f(0)$  large. Let's write it out as an integral:

$$\tilde{T}_{\alpha}f(0) = \int_{\mathbb{D}^n} f(y)[1+|y|]^{-\alpha}\cos|y|dy.$$

If we choose f carefully, then all the contributions in the integral are positive, instead of cancelling each other. This motivates choosing  $f_2 = \chi_{B_r} sign(cos|y|)$ , for some large  $r \geq 1$ . We have  $||f_2||_p = r^{n/p}$ . We also have  $|\tilde{T}_{\alpha}f_2(0)| \sim r^{n-\alpha}$ . In fact, for all |x| < 1/100, we have  $|\tilde{T}_{\alpha}f_2(x)| \sim r^{n-\alpha}$ . Therefore,  $||\tilde{T}_{\alpha}f_2||_p \gtrsim r^{n-\alpha}$ . So  $||\tilde{T}_{\alpha}f_2||_p \lesssim ||f_2||_p$  iff  $n/p \geq n - \alpha$ .

In summary, we have the following proposition.

**Proposition 2.1.** If  $\|\tilde{T}_{\alpha}f\|_p \lesssim \|f\|_p$  for all the examples above, then

$$\frac{n}{\alpha} .$$

Exercise. Being a little more clever/careful in Example 2., we can get eliminate the upper endpoint. If  $\|\tilde{T}_{\alpha}f\|_p \lesssim \|f\|_p$  for all f, then

$$\frac{n}{\alpha} .$$

(If  $n/p = n - \alpha$ , we can consider  $f_3 = \chi_{B_r} \tilde{K}_{n-\alpha}$ . This rules out the endpoint, leaving only  $n/p > n - \alpha$ .)

If particular, if  $\alpha = (n+1)/2$ , then we have a bound on all examples provided that  $\frac{2n}{n+1} . This was the situation until the early 70's.$ 

#### 3. Examples shaped like tubes

There is another important example in the theory of these operators: an oscillating function supported on a long thin tube.

Let T be a cylinder of length L >> 1 and radius  $(1/1000)L^{1/2}$ . The cylinder may point in any direction. Let  $v_T$  be a unit vector parallel to the axis of the cylinder. Let  $f_T$  be the function

$$f_T(x) := \chi_T(x)e^{i(v_T \cdot x)}$$

We want to understand  $\tilde{T}_{\alpha}f_{T}$ . Let  $T^{+}$  denote the cylinder we get by translating T by  $2Lv_{T}$ . The most interesting part is the behavior of  $\tilde{T}_{\alpha}f_{T}$  on  $T^{+}$ . Consider a point x in  $T^{+}$ .

$$\tilde{T}_{\alpha}f_T(x) = \int_T |x - y|^{\alpha} \cos|x - y| e^{i(v_t \cdot y)} dy.$$

Now the key point is that the oscillations of  $e^{i(v_t \cdot y)}$  and the oscillations of  $\cos |x - y|$  are in sync on T. Let's consider the set where  $e^{iv_t \cdot y}$  is equal to 1 – this set is the set of peaks of the real part of the wave  $e^{iv_t \cdot y}$ . We have  $e^{iv_t \cdot y} = 1$  when  $v_t \cdot y = 2\pi n$ ,  $n \in \mathbb{Z}$ . This set is a union of parallel planes, perpendicular to the axis of T with spacing  $2\pi$  between them. The peaks of the wave  $\cos |x - y|$  occur at  $|x - y| = 2\pi n$ , on spheres around x with radius  $2\pi n$ . But inside of the tube T, each sphere looks almost like a plane. It's a good idea at this point to draw a picture of the level sets of  $v_t \cdot y$  and of |x - y| inside of T. Because of this, the two waves interfere constructively. Let's examine the situation more computationally now.

The vector x - y is nearly parallel to  $v_t$ . The  $v_t$  component of x - y is  $\sim L$ , and the perpendicular component is  $\leq (1/1000)L^{1/2}$ . By the Pythagorean theorem, we have

$$(v_t \cdot x - v_t \cdot y)^2 - 10^{-4}L \le |x - y|^2 \le (v_t \cdot x - v_t \cdot y)^2 + 10^{-6}L$$

Since  $|v_t \cdot x - v_t \cdot y| \ge L/4$ , we see that

$$|x - y| - |v_t \cdot x - v_t \cdot y| < 10^{-5}$$
.

Therefore, up to a small error, we have

$$\tilde{T}_{\alpha}f_T(x) = \int_T |x - y|^{\alpha} \cos(v_t \cdot x - v_t \cdot y) e^{i(v_t \cdot y)} dy + \text{ small error.}$$

Expanding  $\cos a = (1/2)(e^{ia} + e^{-ia})$ , we get

$$\tilde{T}_{\alpha} f_{T}(x) = (1/2) e^{iv_{t} \cdot x} \int_{T} |x - y|^{-\alpha} dy + (1/2) e^{-iv_{t} \cdot x} \int_{T} |x - y|^{-\alpha} e^{2iv_{t} \cdot y} dy + \text{ small error.}$$

The first integral is the main term. There's lots of cancellation in the second integral, so it's much smaller. The error term is bounded by  $\int_T |x-y|^{-\alpha} 10^{-5} dy$ , so it's much smaller than the main term.

it's much smaller than the main term. The volume of T is  $\sim L^{\frac{n+1}{2}}$ , and  $|x-y| \sim L$ , so the main term has size  $\sim L^{\frac{n+1}{2}-\alpha}$ .

**Proposition 3.1.** If  $f_T$  and  $T^+$  are defined as above, then for every  $x \in T^+$  we have

$$|\tilde{T}_{\alpha}f_T(x)| \gtrsim L^{\frac{n+1}{2}-\alpha}$$
.

Corollary 3.2. If  $\alpha < \frac{n+1}{2}$ , then there are no bounds of the form  $\|\tilde{T}_{\alpha}f\|_p \lesssim \|f\|_p$ .

*Proof.* Notice that  $T^+$  has the same size as T. The function  $f_T$  has size  $\sim 1$  and support on T. If  $\alpha < \frac{n+1}{2}$ , then the function  $\tilde{T}_{\alpha}f_T$  has size >> 1 on  $T^+$ . So  $\|\tilde{T}_{\alpha}f_T\|_p \sim L^{\frac{n+1}{2}-\alpha}\|f_T\|_p$ .

This type of example appears in a number of linear operators besides  $\tilde{T}_{\alpha}$ . There are similar examples connected to the wave equation. It takes some work to write them down precisely, but we can give some feel for it just in words. Imagine an airplane traveling at the speed of sound. The path of the airplane in space-time is like a long thin tube. The engine of the plane vibrates, making sound waves, and these sound waves travel at the same speed as the airplane. The airplane can feel dramatically stronger sound waves than it would have felt at a lower or higher speed. Even if the airplane turns off the engine, there will still be strong sound waves in the plane for some time. The action of the engine occurs on one tube in space time, and the resulting sound waves have large amplitude on a longer tube. Although the operator  $\tilde{T}_{\alpha}$  is not an accurate model for sound waves, the mathematical issues in understanding it are similar with those in the wave equation.

We now return to our operators  $\tilde{T}_{\alpha}$ . For  $\alpha \geq (n+1)/2$ , we have  $\|\tilde{T}_{\alpha}f_T\|_p \lesssim \|f_T\|_p$  for all p. In particular, the ball multiplier  $M_1$  is similar to  $\tilde{T}_{(n+1)/2}$ , and we have  $\|M_1f_T\|_p \sim \|f_T\|_p$  for all p as well. So this example does not give any new information about the ball multiplier. For all the examples we have considered so far, we have

$$||M_1 f||_p \lesssim ||f||_p$$
, for all  $\frac{2n}{n+1} .$ 

Until the early 70's, it was generally believed that these inequalities were true. The only case that was proven was p=2. In "The multiplier problem for the ball", Charles Fefferman proved that these inequalities are false for all  $p \neq 2$ . (The paper appeared in Ann. of Math. (2) 94 (1971), 330-336). These counterexamples are given by arranging many tubes in a remarkable pattern found by Besicovitch.

# 4. Sums of many tubes

Let us consider a function  $f = \sum_i f_{T_i}$  over many tubes  $T_i$ . Then we have  $\tilde{T}_{\alpha}f = \sum_i \tilde{T}_{\alpha}f_{T_i}$ . Schematic picture: draw some tubes  $T_i$  in blue, and  $T_i^+$  in red. For example,  $T_i$  may be disjoint and  $T_i^+$  may intersect.

In the 1920's, Besicovitch constructed an arrangement of tubes so that  $T_i$  are disjoint and  $T_i^+$  intersect a lot.

**Theorem 4.1.** (Besicovitch, 1920's) Fix a dimension  $n \ge 2$ . For any  $L \ge 1$ , there is a finite set of disjoint tubes  $T_i$  (with length L and radius  $\sim (1/1000)L^{1/2}$ ), with the property that

$$|\cup_i T_i^+| \lesssim (\log L)^{-1} |\cup_i T_i|.$$

We'll prove Besicovitch's theorem next class (or maybe something a touch weaker). The key point for the moment is that  $(\log L)^{-1}$  can be arbitrarily small.

Let  $f = \sum_i f_{T_i}$ , where the  $T_i$  are the tubes in Besicovitch's construction. How big is  $\tilde{T}_{(n+1)/2}f$ ? Suppose that x lies in A tubes  $T_i^+$ . We have a sum of A terms of size  $\sim 1$ , but these terms are complex numbers that may point in any direction. We would actually have to be quite lucky if the sum of A terms had size  $\sim A$ . The sum of A random numbers  $|z| \leq 1$  has size  $\sim A^{1/2}$ . So we should expect something more like

$$|\tilde{T}_{(n+1)/2}f(x)| \sim \left(\sum_{i} |\tilde{T}_{(n+1)/2}f_{T_{i}}(x)|^{2}\right)^{1/2}$$
 (\*).

In fact, if we define  $f_{ran} = \sum_{i} \pm f_{T_i}$  with random  $\pm$  signs, then (\*) is true with very high probability.

**Proposition 4.2.** If  $g_i$  are any functions, then with high probability,

$$\|\sum_{i} \pm g_i\|_p \sim \|(\sum_{i} |g_i|^2)^{1/2}\|_p.$$

We defer this – the probability argument is similar to one earlier in the course. With these tools in hand, we can understand  $||f_{ran}||_p$  and  $||\tilde{T}_{\alpha}f_{ran}||_p$ .

Corollary 4.3. If  $T_i$  is any set of tubes, and  $f_{ran} := \sum_i \pm f_{T_i}$ , then with high probability

$$||f_{ran}||_p \sim ||(\sum_i \chi_{T_i}^2)^{1/2}||_p \sim ||\sum_i \chi_{T_i}||_{p/2}^{1/2}.$$

In Besicovitch's example, the tubes  $T_i$  are disjoint, and so  $||f_{ran}||_p \sim |\cup T_i|^{1/p}$ .

Corollary 4.4. If  $T_i$  is any set of tubes of length L, and  $f_{ran} = \sum_i \pm f_{T_i}$ , then with high probability

$$\|\tilde{T}_{\alpha}f_{ran}\|_{p} \gtrsim L^{\frac{n+1}{2}-\alpha} \|\sum_{i} \chi_{T_{i}^{+}}\|_{p/2}^{1/2}.$$

In Besicovitch's example,  $\sum_i \chi_{T_i^+}$  is supported on a set of measure  $\lesssim (\log L)^{-1} | \cup_i T_i |$ , and so its average height is  $\gtrsim \log L$ . Therefore, for q > 1, its  $L^q$  norm is  $\gtrsim (\log L)^q (\log L)^{-1} | \cup_i T_i |$ , and we get

$$\|\tilde{T}_{\alpha}f_{ran}\|_{p} \gtrsim L^{\frac{n+1}{2}-\alpha}(\log L)^{\frac{p-2}{4}}|\cup_{i} T_{i}|^{1/p}.$$

We get

**Theorem 4.5.** (Fefferman 1971) If p > 2, then  $\tilde{T}_{(n+1)/2}$  is not bounded on  $L^p$ .

Exercise. The operator  $\tilde{T}_{(n+1)/2}$  is also not bounded on  $L^p$  for p < 2. To see this, choose  $T_i$  so that  $T_i^+$  are disjoint and  $|\cup_i T_i^+|$  is much larger than  $|\cup_i T_i|$ .

HLS problem: connected with how balls overlap in space BR problem: connected with how tubes overlap in space.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.S997 Notes

## 1 Friday, December 7, 2012

We defined  $\tilde{K}_{\alpha}(x) = (1+|x|)^{-\alpha} \cos|x|$  and  $\tilde{T}_{\alpha}f := f * \tilde{K}_{\alpha}$ . We study a tube T with length  $L \ge 1$  and diameter  $L^{1/2}/1000$ . Letting  $v_T$  be the unit vector along the tube, we defined  $f_T(x) = e^{iv_T \cdot x} \chi_T$ . We also defined  $T^+$  to be T shifted by twice its length in the direction of  $v_T$ ; that is,  $T^+ = T + 2Lv_T$ . We proved:

**Proposition.** 
$$\left| \tilde{T}_{\alpha} f_{T}(x) \right| \gtrsim L^{\frac{n+1}{2} - \alpha} \text{ on } T^{+}.$$

Corollary. If 
$$\alpha < \frac{n+1}{2}$$
, then  $\|\tilde{T}_{\alpha}f\|_{p} \lesssim \|f\|_{p}$  is false for all  $p$ .

We will now use these tubes to show a similar result for  $\alpha = \frac{n+1}{2}$ .

**Theorem** (Fefferman 71). 
$$\left\|\tilde{T}_{\frac{n+1}{2}}f\right\|_p \lesssim \|f\|_p$$
 is false for all  $p \neq 2$ .

When 
$$p=2$$
, one can prove using Fourier analysis that  $\left\|\tilde{T}_{\frac{n+1}{2}}f\right\|_2 \lesssim \|f\|_2$ .

*Proof.* We will prove Fefferman's result for p > 2. The idea is to look at many tubes  $T_i$ , and take  $f = \sum_i f_{T_i}$ . We wish to arrange disjoint tubes in such a way that their translates have large intersection. The idea for the case p < 2 is to start with the intersecting tubes and translate them so they are disjoint. An arrangement due to Besicovitch will be particularly useful:

**Theorem** (Besicovitch, 20s). For any  $L \geq 1$ , there exists a collection of tubes  $T_i$  (as above) such that the  $T_i$  are disjoint, but  $\left|\bigcup T_i^+\right| \leq \frac{1}{K} \left|\bigcup T_i\right|$ , and  $\sum \chi_{T_i^+} \sim K$  on a set of size  $\sim \frac{1}{K} \left|\bigcup T_i\right|$ , where  $K \gtrsim \frac{\log L}{\log \log L}$ .

We will prove Besicovitch's result later, but first we will use it to prove Fefferman's result.

Suppose x lies in K tubes  $T_i^+$ . Then  $T_{\frac{n+1}{2}}f(x)$  has about K contributions of size around 1. However, not all of these are necessarily positive; to get around this, we will randomly vary the sign of our function.

**Proposition.** If  $g_i$  are functions, take  $g_{ran} = \sum \pm g_i$  where the signs are taken randomly. Then for all  $1 \le p \le \infty$ ,  $\|g_{ran}\|_p \sim \left\|\left(\sum |g_i|^2\right)^{1/2}\right\|_p$  with high probability.

We won't prove this; the proof is similar to when we applied a Chernoff bound.

Take  $f_{ran} = \sum \pm f_{T_i}$ .  $|f_{ran}| = 1$  on  $\bigcup T_i$  since the  $T_i$  are disjoint. But  $\tilde{T}_{\frac{n+1}{2}} f_{ran} \sim K^{1/2}$  on a set of size  $\sim \frac{1}{K} |\bigcup T_i|$ . So taking the  $L_p$  norms,  $\int |f_{ran}|^p = |\bigcup T_i|$  and  $\int \left|\tilde{T}_{\frac{n+1}{2}} f_{ran}\right|^p \sim K^{\frac{p}{2}} K^{-1} |\bigcup T_i|$ . If p > 2,  $\frac{\|\tilde{T}_{\frac{n+1}{2}} f_{ran}\|_p}{\|f_{ran}\|_p}$  tends to infinity with K and therefore with L, as desired.

We will now prove Besicovitch's result in the two-dimensional case. The higher dimensional cases are similar. We will rescale so that L=1 and the diameter of the cylinders is  $N^{-1}$  (where N is an integer to be determined). We will define lines that will correspond to the centers of the tubes:  $\ell_j(x) = \frac{j}{N}x + H(j)$ 

(here  $\ell_j$  is a function form  $\mathbb{R}$  to  $\mathbb{R}$ , and so defines a line in the plane). Let  $R_j$  be the 1/N-neighborhood of  $[\ell_j(0), \ell_j(1)]$ , for  $j = 0, \ldots, n-1$ . These will be our tubes.

Take, for some integer A,  $N=A^A$ . We will work base A, so we may write  $\frac{j}{N}=\sum_{a=1}^A j(A)A^{-a}$ . Then define the heights  $H(j)=-\sum_{a=1}^A \frac{a}{A}j(a)A^{-a}$ . We will complete the proof and then present the geometric intuition. We will show that  $|\bigcup R_j|\leq \frac{10}{A}$ . Then  $A\log A=\log N$ , so  $A\gtrsim \frac{\log N}{\log\log N}$ . Since  $N\sim \sqrt{L}$  so  $A\gtrsim \frac{\log L}{\log\log L}$ .

**Lemma.** If j(A) = J(a) for a = 1, ..., b - 1, then  $|\ell_j(\frac{b}{A}) - \ell_J(\frac{b}{A})| \le 2A^{-b}$ .

*Proof.* We defined  $H(j) = -\sum_{a=1}^{A} \frac{a}{A} j(a) A^{-a}$ . Therefore,  $\ell_j(x) = \sum_{a=1}^{A} \left(x - \frac{a}{A}\right) j(a) A^{-a}$ . When we subtract  $\ell_j(x)$  and  $\ell_J(x)$ , the first b-1 terms cancel, as for those j(a) = J(a). Note the a=b terms are 0 since  $x = \frac{b}{A}$ .

The remaining terms are bounded by:

$$\sum_{a=b+1}^{A} \left| \frac{b-a}{A} A^{-a} j(a) \right| + \sum_{a=b+1}^{A} \left| \frac{b-a}{A} A^{-a} J(a) \right| \le \sum_{a=b+1}^{A} A^{-a} j(a) + \sum_{a=b+1}^{A} A^{-a} J(a) \le 2A^{-b}.$$

**Corollary.** If j(a) = J(a) for a = 1, ..., b - 1,  $|\ell_j(x) - \ell_J(x)| \le 4A^{-b}$  for  $x \in [\frac{b-1}{A}, \frac{b}{A}]$ .

*Proof.* They are within  $2A^{-b}$  at b/A, and their slope difference is at most  $A^{-(b-1)}$  over the interval of length  $A^{-1}$ , so there is a change of at most  $A^{-b}$ , giving the (slightly stronger than) desired bound.

**Corollary.**  $\bigcup R_j \cap ([\frac{b-1}{A}, \frac{b}{A}] \times \mathbb{R})$  is covered by  $A^{(b-1)}$  horizontal strips (really, parallelograms) of width  $6A^{-b}$ .

*Proof.* There are  $A^{b-1}$  choices for  $j(1), \ldots, j(b-1)$ . Then there is a strip within these of this width that covers all of the possible lines.

Corollary. The area of the  $R_j$  is at most  $10A^{-1}$ .

*Proof.* Just add up the area within each strip according to the last corollary.

To check that the  $R_j$  give the desired construction, we still need that their translates are disjoint and that most points are contained in many of them. We leave this as an exercise to the reader.

We are also interested in  $\tilde{T}_{\alpha}$  for  $\alpha > \frac{n+1}{2}$ . However, this remains open.

Conjecture (Bochner-Riesz). If 
$$\alpha > \frac{n+1}{2}$$
, then  $\left\| \tilde{T}_{\alpha} f \right\|_{p} \lesssim \|f\|_{p}$  for  $\frac{n}{\alpha} .$ 

One could try to apply an argument similar to Fefferman's to contradict this. In particular, Fefferman's argument shows that the Bochner-Riesz conjecture implies:

**Conjecture.** If  $T_i$  are tubes of length L as above,  $\epsilon > 0$ , the  $T_i$  disjoint, then  $|\bigcup T_i^+| \ge c_{\epsilon} L^{-\epsilon} |\bigcup T_i|$ .

## MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## THE KAKEYA PROBLEM

In this lecture, we will discuss Kakeya Conjecture and some known results about it.

**Definition** Suppose that  $T_i \subset \mathbb{R}^n$  are tubes of length N and radius 1.  $\{T_i\}$  is a Kakeya set of tubes if  $\{V(T_i)\}$  is  $\frac{1}{N}$ -separated and  $\frac{2}{N}$ -dense in  $S^{n-1}$ , where  $V(T_i)$  is the unit vector of direction of the tube  $T_i$ .

Our question is: how small can  $|\cup T_i|$  be?

Recall that last time we gave the "Besicovitch arrangement of tubes" where we managed to compress the volume of  $\cup T_i$  by a factor of  $\log N$ . We got that arrangement by translating the tubes in a certain way, without performing any rotation. We want to know whether there is a better compression.

**Kakeya Conjecture**(tube version). For any Kakeya set of tubes  $T_i \subset \mathbb{R}^n$ ,  $|\cup T_i| \ge C_{\epsilon} \cdot N^{n-\epsilon}$  ( $\forall \epsilon > 0$ ).

We also have:

**Kakeya Conjecture**(segment version). For any Kakeya set K(a set of points that contains a unit line segment in every direction) in  $\mathbb{R}^n$ ,  $\operatorname{H-dim}(K) \geqslant n - \epsilon$ , where  $\operatorname{H-dim}(K)$  is the Hausdorff dimension of K and  $\epsilon$  is any positive number.

Notice that the segment version will imply the tube version. The tube version has a combinatorial flavor since it involves how tubes can overlap each other.

## 1. The 2D case

**Proposition**. The Kakeya Conjecture(tube version) is true in dimension two.

Now we sketch the proof here. The flavor is similar to the finite field Kakeya problem.

We denote by  $\theta_i$  the angle between  $V(T_i)$  and the x-axis. Then the overlapping area of  $T_1$  and  $T_2$  can be bounded by  $\frac{1}{|\theta_1-\theta_2|}$ . Then we get

$$\int |\sum \chi_{T_i}|^2 = \sum \sum \int \chi_{T_i} \chi_{T_j} = \sum \sum |T_i \cap T_j| \lesssim |\log N| N^2$$

By Cauchy-Schwarz inequality, we have  $N^2 = \int (\sum \chi_{T_i}) \leqslant (\int |\sum \chi_{T_i}|^2)^{\frac{1}{2}} \cdot |\cup T_i|^{\frac{1}{2}}$ . Thus  $|\cup T_i| \gtrsim N^2 (\log N)^{-1}$ .

Conjecture( $L^p$  version).  $\int |\sum \chi_{T_i}|^p \lesssim N^{\epsilon}$  (what happens if all tubes are centered at zero) This will imply the Kakeya Conjecture(tube version) by a similar argument.

#### 2. Bush argument and hair brush argument

• Bush argument: We have  $|K| \gtrsim q^{\frac{n+1}{2}}$  for a Kakeya set  $K \subset \mathbb{F}_q^n$  and  $|\cup T_i| \gtrsim N^{\frac{n+1}{2}}$  for a Kakeya set of tubes  $T_i \subset \mathbb{R}^n$ 

We have already seen how Bush argument works in the finite field case. For the tube version the similar argument works too.

Suppose  $|\cup T_i|$  is small, then there must be a point that is covered by many tubes. Those tubes might have a large overlapping area around that point, but if we consider what happens in a distance of  $\frac{N}{10}$  from that point, then we see the volume of the bush is bigger than N· (the number of tubes in the bush)

• Hair Brush argument: We have  $|K| \gtrsim q^{\frac{n+2}{2}}$  for a Kakeya set  $K \subset \mathbb{F}_q^n$  and  $|\cup T_i| \gtrsim N^{\frac{n+2}{2}}$  for a Kakeya set of tubes  $T_i \subset \mathbb{R}^n$ 

In the finite field case, this argument goes like to choose the line that has the biggest number of intersection with other lines and consider all lines that intersect it. This will give us the bound. However it is much trickier to get the bound for the tube version: when we consider what happens in a distance of  $\frac{N}{10}$  from our chosen tube, it turns out that tubes that have small angle to the chosen tube might not even make it out that distance. It is possible, though not easy, to rule out such cases and get the desired bound as was shown by Thomas Wolff in the 90s.

In 3D, the Hair Brush argument gives  $| \cup T_i | \gtrsim N^{\frac{5}{2}}$ . It is surprisingly hard to improve this bound. Katz-Laba-Tao, under a minor assumption about K, improved the bound to something like  $N^{\frac{5}{2}+10^{-10}}$ . Being stuck at this point, Thomas Wolff proposed some toy problems:

- Finite field Kakeya problem. People think that passing from  $\mathbb{R}^n$  to  $\mathbb{F}_q^n$  might make the problem a little bit easier while still preserving some of the flavor, as is shown in the hair brush argument.
- Instead of considering tubes in different directions, we can take annuli with thickness  $\frac{1}{N}$  and radii between 1 and 2. In order to solve that, he used incidence geometry, stuff related to Szemerédi-Trotter theorem. That was cool because it brought a whole different set of techniques to this area, so people in harmonic analysis learned about this area of mathematics.

### 3. POLYNOMIAL METHOD FOR TUBE VERSION KAKEYA PROBLEM

Since we have already seen the elegant proof of finite field Kakeya problem using polynomial method, can we say anything about the tubes by using polynomial method?

Let us recall the main ideas we used when we solved the finite field Kakeya problem:

- (1) Look at the polynomial P that vanishes on K with smallest degree. The degree would be significantly smaller than q.
- (2) P must vanish at some other places, then we have contradiction.

Now let us see what happens for tubes. Suppose K is a Kakeya set of  $1 \times N$  tubes  $T_i \subset \mathbb{R}^n$ ,  $|K| = N^{n-\gamma}$ . Here are some ideas:

- Look at the polynomial P that vanishes at all core lines with smallest degree. But those lines can be all disjoint. Even if they are not, we can make a small perturbation to make them so.
- Look at the polynomial P that vanishes on  $\partial T_i$ . Then P=0 on the infinite surfaces. But the degree of P would be very big.
- Instead of vanishing, P is just small on  $\cup T_i$ , with some normalization.
- Z(P) bisects each tube. If it does it by cutting tubes at their mid-points, then there is not much information. We would like it to cut tubes along their core lines, but it seems that by requiring so we are putting infinitely many conditions on our polynomial.
- Z(P) bisects each lattice cubes with size  $\frac{1}{100}$  that overlaps our tubes. The polynomial ham sandwich theorem allows us to find one with degree  $\lesssim N^{1-\frac{\gamma}{n}}$ . Now our question is: does such a polynomial necessarily bisect some other cubes?

We will see what we should do next in the last class on Wednesday.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### THE MULTILINEAR KAKEYA INEQUALITY

## 1. The discussion from last time, heuristics and memories

Suppose that  $\{T_i\}$  is a Kakeya set of tubes in  $\mathbb{R}^n$ . Each tube has radius 1 and length N, and there are  $\sim N^{n-1}$  tubes. Suppose that  $|\cup T_i| \sim N^{n-\gamma}$ .

The number of unit cubes from the unit cube lattice that intersect  $\cup T_i$  is  $\sim N^{n-\gamma}$ . We use the polynomial ham sandwich theorem to choose a polynomial P so that Z(P) bisects each of these unit cubes. The degree of Z(P) is  $\lesssim N^{1-\gamma/n}$ . What does such a polynomial tell us? Let Q(K) be this set of cubes.

Consider one of the tubes,  $T_i$ . Let l be a line parallel to the axis of  $T_i$ , a randomly chosen parallel line in the tube  $T_i$ . For almost every choice of l, we have  $|l \cap Z(P)| \le deg(P) \lesssim N^{1-\gamma/n}$ . On the other hand, the tube  $T_i$  contains  $\sim N$  cubes of Q(K), and Z(P) bisects each of them. Let  $Q(T_i)$  be this list of cubes. They are disjoint, so we get

$$Average_{q \in Q(T_i), l} |l \cap Z(P) \cap q| \lesssim N^{-1} deg(P) \lesssim N^{-\gamma/n}$$
.

For a typical cube q, we know that Z(P) bisects q, and yet  $Average_l|Z(P) \cap q| \lesssim N^{-\gamma/n}$  is much smaller than 1. This is only possible if the surface  $Z(P) \cap q$  is approximately parallel to the tube  $T_i$ . We can make a revised picture of the surface Z(P) in the tube  $T_i$ .

So the geometry of the surface Z(P) is connected with the geometry of the tubes  $T_i$ . If we try to imitate Dvir's proof of the finite field Nikodym or Kakeya conjectures, we are led to the following question. Extend each tube  $T_i$  a further length  $\sim N$ , and let q' be a unit cube in the extension. Is it true that Z(P) approximately bisects q'? This type of question looks difficult, and it may be unlikely. The surface Z(P) is approximately tangent to the tube  $T_i$  inside of  $T_i$ , but it's hard to know whether Z(P) will bend sharply as soon as it leaves  $T_i$  and come nowhere near to q'.

I spent a while trying to force Z(P) to hit q', and it was pretty frustrating. I would charge down one of the tubes  $T_i$ , trying to pin Z(P) and carry it down to q', and Z(P) would stay with me for a while and then swing out of the way, while I went charging harmlessly by...

However, the structure that we observed above does say something interesting about Kakeya sets. We noticed that for a typical cube  $q \subset T_i$ , the surface Z(P) is approximately tangent to  $T_i$ . But there are many different tubes  $T_j$  containing q. With the method above, we can argue that  $T_j$  is approximately tangent to Z(P) for

most of the tubes. In fact, there must be a hyperplane  $\pi(q)$ , and the tubes  $T_j$  must usually be almost tangent to  $\pi(q)$ . This is a somewhat surprising structure, called planiness.

Planiness was first discovered by Katz, Laba, and Tao, in the paper "An improved bound on the Minkowski dimension of Besicovitch sets in  $\mathbb{R}^3$ ." (Ann. of Math. (2) 152 (2000), no. 2, 383-446.) Planiness was one of the observations/tools that allowed them to prove that a Kakeya set of tubes in  $\mathbb{R}^3$  (with mild additional hypotheses) has volume at least  $N^{2.5+\epsilon}$ . Later, Bennett, Carbery, and Tao proved stronger and more general planiness estimates in the paper "On the multilinear restriction and Kakeya conjectures" in Acta Math. 196 (2006), no. 2, 261-302. We will come to their work below.

If we had a hypothetical Kakeya set of tubes, a typical cube would lie in many tubes  $T_j$ . Without any experience, we might guess that the different tubes  $T_j \supset q$  would point in a bush of directions that was pretty dense on the unit sphere. Suprisingly, they need to concentrate near to a plane. Another way to say this is that they don't form a whole lot of joints.

During the course, we met many theorems about the incidence patterns of lines in space. Each of these questions can be adapted to a question about long thin tubes instead of lines. Usually the adapted question is wide open. But for the joints problem, the adapted question has a nice answer based on the ideas we have just been discussing.

#### 2. The generalized Loomis-Whitney inequality

We prove here an analogue of the joints theorem with long thin tubes instead of perfect lines.

**Theorem 2.1.** (Bennett-Carbery-Tao, Guth) Suppose that  $T_{j,a}$  are cylinders in  $\mathbb{R}^n$  for  $1 \leq j \leq n$  and  $1 \leq a \leq A$ . Each cylinder has radius 1 and infinite length. The axis of a cylinder  $T_{j,a}$  makes an angle of  $< (100n)^{-1}$  with the  $x_j$ -axis.

Let I be the points which lie in one cylinder for each value of j = 1...n. In equations  $I := \bigcap_{j=1}^{n} (\bigcup_{a=1}^{A} T_{j,a})$ .

Then the volume of I is  $\lesssim A^{\frac{n}{n-1}}$ .

Remarks. If the tubes  $T_{j,a}$  are parallel to the  $x_j$ -axis, then this estimate follows from the Loomis-Whitney inequality. We see that the projection of I to any coordinate hyperplane lies in A unit balls, and then Loomis-Whitney gives  $|I| \lesssim A^{\frac{n}{n-1}}$ . The case of axis-parallel cylinders is basically equivalent to the Loomis-Whitney inequality. The problem here is to see that the inequality remains true if we are allowed to tilt the tubes a few degrees.

History. BCT proved a tiny bit weaker estimate using monotonicity formulas for the heat equation. G proved this estimate using the polynomial method. This

theorem can be thought of as a version of joints for nearly-orthogonal tubes. It implies, in particular, the joints theorem for nearly orthogonal lines.

The proof involves the idea of the directed volume of a surface. Suppose S is a smooth hypersurface in  $\mathbb{R}^n$  with normal vector N. If v is a unit vector, we define the directed volume of S perpendicular to V by the formula

$$V_S(v) := \int_S |N \cdot v| dvol_S.$$

Notice that if the tangent plane of S is perpendicular to v, we have  $|N \cdot v| = 1$ , and if the tangent plane contains v, we have  $|N \cdot v| = 0$ . For example, we consider the directed volume of the unit circle in the direction v = (0,1). The directed volume of an arc of the upper semi-circle in direction v is exactly the change in the x-coordinate over the arc. Therefore, the directed volume of the whole upper semi circle is 2, and the directed volume of the whole circle is 4.

The computation for the circle generalizes as follows. Let  $\pi$  be the orthogonal projection from  $\mathbb{R}^n$  to  $v^{\perp} \subset \mathbb{R}^n$ .

**Lemma 2.2.** 
$$V_S(v) = \int_{v^{\perp}} |S \cap \pi^{-1}(y)| dvol(y)$$
.

As a corollary, we can immediately estimate the directed volume of a degree d variety in a cylinder T.

**Lemma 2.3.** (Cylinder estimate) Let T be an infinite cylinder in  $\mathbb{R}^{\times}$  of radius r. Let v be a unit vector parallel to the axis of T. Let Z(P) be the vanishing set of a polynomial P.

Then 
$$V_{Z(P)\cap T}(v) \lesssim r^{n-1}deg(P)$$
.

Proof. Let  $\pi$  be the projection from T to the cross-section  $v^{\perp} \cap T$ . This cross-section is just an (n-1)-dimensional ball of radius r. For almost every y in this ball,  $|\pi^{-1}(y) \cap Z(P)| \leq deg(P)$ . By the last lemma,  $V_{Z(P)\cap T}(v)$  is bounded by deg(P) times the volume of the cross-section, which is  $\sim r^{n-1}$ .

**Lemma 2.4.** If S is a hypersurface in  $\mathbb{R}^n$ , and  $v_1, ..., v_n$  are unit vectors and the angle from  $v_j$  to the  $x_j$ -axis is  $\leq (100n)^{-1}$ , then  $Vol_{n-1}S \leq 2\sum_j V_S(v_j)$ .

*Proof.* At a given point of S with normal vector N, we have to prove that  $\sum_{j} |N \cdot v_j| \ge 1/2$ . If  $e_j$  are the coordinate vectors, then it's straightforward to check that  $\sum_{j} |N \cdot v_j| \ge 1$  for any unit vector N. The vectors  $v_j$  are very close to  $e_j$ , and so the error has size  $\le \sum_{j} |e_j - v_j| \le (1/100)$ .

Now we can do the proof of the theorem.

*Proof.* Consider the unit cubical lattice. Let  $Q_1, ..., Q_V$  be all the unit cubes in the lattice which intersect the set I. We will prove  $V \leq A^{\frac{n}{n-1}}$ .

Let P be a non-zero polynomial so that Z(P) bisects each cube  $Q_1, ..., Q_V$  and  $deg P \lesssim V^{1/n}$ . This bisection requires a certain amount of area, therefore:

$$Vol_{n-1}Z(P) \cap Q_i \gtrsim 1.$$

Let  $T_j(Q_i)$  be a tube from our list, in direction j, which intersects  $Q_i$ . Let  $v_{j,i}$  be the direction of this tube. The directions  $v_{1,i}, ..., v_{n,i}$  are nearly orthonormal, and so

$$\sum_{j=1}^{n} V_{Z(P) \cap Q_i}(v_{j,i}) \gtrsim Vol_{n-1}Z(P) \cap Q_i \gtrsim 1.$$

For each cube, choose one direction j so that  $V_{Z(P)\cap Q_i}v_{j,i} \gtrsim 1$ , and assign the cube  $Q_i$  to the tube  $T_j(Q_i)$ . We have V cubes and nA tubes, so one of the tubes has  $\gtrsim V/A$  cubes assigned to it. Let T be this tube, and let v be its direction. We have  $\gtrsim V/A$  cubes  $Q_i$  obeying the following conditions:

- The cube  $Q_i$  intersects T.
- $V_{Z(P)\cap Q_i}(v) \gtrsim 1$ .

Let  $\tilde{T}$  be a wider cylinder with radius 2n and with the same central axis as T. All of the cubes  $Q_i$  lie in  $\tilde{T}$ . Therefore, we have

$$V/A \lesssim V_{Z(P)\cap \tilde{T}}(v) \lesssim V^{1/n}$$
.

The last inequality is by the cylinder estimate.

Rearranging we get  $V \lesssim A^{\frac{n}{n-1}}$ .

#### 3. Multilinear Kakeya

The strongest version of the Kakeya conjecture is the  $L^p$  version. If  $T_i$  are a Kakeya set of tubes of radius 1 and length N, the  $L^p$  Kakeya conjecture says that for each  $\epsilon > 0$ ,

$$\int_{\mathbb{R}^n} |\sum_{i} \chi_{T_i}|^{\frac{n}{n-1}} \le C_{\epsilon} N^{\epsilon} N^n. \tag{1}$$

Remarks: If we arrange the tubes in a disjoint way, the left hand side is  $\sim N^n$ . If we arrange them all centered at the origin, then the left hand side is  $\sim (\log N)N^n$ . If true, this conjecture gives essentially sharp bounds for  $\|\sum_i \chi_{T_i}\|_p$  for every p. It implies that the union of tubes has volume at least  $c_{\epsilon}N^{n-\epsilon}$  for any  $\epsilon > 0$ .

This conjecture is still wide open. The multilinear Kakeya conjecture allows us to control a positive fraction of all the terms - in a certain sense. First we rewrite the left hand side of (1).

$$\int |\sum_{i} \chi_{T_{i}}|^{\frac{n}{n-1}} = \int |\sum_{i} \chi_{T_{i}}|^{\frac{1}{n-1}} \cdot \dots \cdot |\sum_{i} \chi_{T_{i}}|^{\frac{1}{n-1}}$$

On the right hand side we have a product of n identical copies of  $|\sum_i \chi_{T_i}|^{\frac{1}{n-1}}$ . Now we edit the formula, keeping only a constant fraction of the terms in each copy of  $|\sum_i \chi_{T_i}|^{\frac{1}{n-1}}$ . Let I(j) be the subset of tubes  $T_i$  where the angle between  $v(T_i)$  and the  $x_j$  axis is  $\leq (100n)^{-1}$ . For each j, the number of such tubes is  $\sim N^{n-1}$  - they form a positive fraction of all of the tubes.

**Theorem 3.1.** (Bennett-Carbery-Tao) For any  $\epsilon > 0$ , there exists a constant  $C_{\epsilon}$  so that for any Kakeya set of tubes,

$$\int \prod_{j=1}^{n} \left| \sum_{i \in I(j)} \chi_{T_i} \right|^{\frac{1}{n-1}} \le C_{\epsilon} N^{\epsilon} N^n.$$

(In this inequality, the  $N^{\epsilon}$  factor can actually be removed, see my paper "On the endpoint case of the Bennett-Carbery-Tao multilinear Kakeya inequality". But this takes a lot of extra work.)

This inequality is a generalization of the last theorem. We explain how they are related and we sketch the extra steps needed to prove the theorem. For any integers  $\mu_1, ..., \mu_n \geq 0$ , consider the set of points:

$$I(\mu) := \{ x \in \mathbb{R}^n | 2^{\mu_j} \le | \sum_{i \in I(j)} \chi_{T_i} | < 2^{\mu_j + 1} \text{ for all } j. \}$$

The left hand side is

$$\sim \sum_{\mu} |I(\mu)| \prod_{j} 2^{\mu_j/(n-1)}.$$

Therefore, the theorem follows from the following lemma:

**Lemma 3.2.** For each  $\mu$  as above,  $|I(\mu)| \lesssim N^n \prod_i 2^{-\mu_j/(n-1)}$ .

The lemma shows that each term in the sum above has size  $\lesssim N^n$ , and the number of terms is  $\lesssim (\log N)^n$ , and so we get a bound for the total of  $\lesssim N^n(\log N)^n$ , which proves the theorem.

If  $\mu = 0$ , we have I(0) contained in the n-fold intersection set I defined above, and the inequality follows from the Theorem in the last section. The other values of  $\mu$  are fairly similar.

Let us randomly choose  $I'(j) \subset I(j)$ , including each tube with probability  $2^{-\mu_j}$ . Let I' be the points lying in one tube  $T_i$ ,  $i \in I'(j)$  for each j. A point of  $I(\mu)$  lies

in I' with probability  $\gtrsim 1$ . With high probability, the size of I'(j) is  $\sim N^{n-1}2^{-\mu_j}$ . Therefore, our bound for  $I(\mu)$  follows from the following lemma.

**Lemma 3.3.** Let  $T_{j,a}$   $a = 1...A_j$  be cylinders of radius 1 nearly parallel to the  $x_j$  axis. Then the volume of the set of points lying in at least one tube of each direction  $is \lesssim \prod_{j=1}^n A_j^{\frac{1}{n-1}}$ .

If all the  $A_j$  happen to be equal, this lemma is exactly the theorem from the last section.

The case of unequal  $A_j$  requires an extra refinement in the proof. We cut each cube  $Q_i$  into many smaller pieces, and we choose P to bisect each smaller piece. The smaller pieces are arranged into a grid, cut more finely in the directions j where  $A_j$  is small and more coarsely in the directions where  $A_j$  is large. Details in the exercises...

(More details. Take a cube  $Q_i$ . Pick tubes  $T_j(Q_i)$ . Change coordinates so that the vectors  $v(T_j(Q_i))$  become exactly orthogonal. In these coordinates,  $Q_i$  is not quite a cube, but contains a slightly smaller cube  $\tilde{Q}_i$ . Chop  $\tilde{Q}_i$  into a grid, where the  $j^{th}$  direction is cut subdivided into  $\prod_{j'\neq j} A_{j'}$ . Choose Z(P) to bisect each of these pieces. ...)

#### 4. Sharp turns of algebraic varieties?

So far, the polynomial method has not led to any progress on the Kakeya problem. There are major difficulties in applying the methods we have seen to long thin tubes instead of perfect lines.

In the proof of finite field Kakeya or Nikodym, we use parameter counting to find a polynomial that vanishes in some places, and then we argue that the polynomial also must vanish somewhere else. This step plays a key role in most of the proofs we have seen in this course. It's hard to see whether something like this can work in the setting of tubes.

Suppose as in the first section that K is the union of a Kakeya set of  $1 \times N$  tubes with surprisingly small volume, and that P is a polynomial so that Z(P) bisects each cube of the unit lattice that intersects K. Pick a tube T from the Kakeya set, and imagine extending it to twice its length, and let q be a unit cube in this extension. Is there any hope that Z(P) also roughly bisects q? We know that Z(P) bisects all the cubes in T, and we've also seen that in most of these cubes Z(P) is roughly parallel to T. If Z(P) keeps going in the direction of its tangent plane, it will come reasonably close to q (although it's still not clear it will really hit q). But it's not at all clear whether Z(P) will continue in the direction of its tangent plane. Perhaps Z(P) will curve dramatically and go nowhere near q.

It might be helpful to understand better how many sharp bends there can be in a degree d algebraic surface. Here is a toy problem that gets at some of these issues.

Let P be a polynomial in two variables. Let  $Pos(P) := \{x \in \mathbb{R}^2 | P(x) > 0\}$ . For a given degree d, how closely can Pos(P) look like the square  $[-1,1]^2$ ? Recall that the Hausdorff distance from Pos(P) to  $[-1,1]^2$  is  $< \epsilon$  if  $[-1,1]^2$  lies in the  $\epsilon$ -neighborhood of Pos(P) and Pos(P) lies in the  $\epsilon$ -neighborhood of the square. Let  $\epsilon(d)$  be the infimum over all degree d polynomials P of  $dist_{Haus}(Pos(P), [-1,1]^2)$ . Can we describe the order of magnitude of  $\epsilon(d)$ ?

Very little is known about this. We know that  $\epsilon(d) > 0$  for each d. The reason is that  $dist_{Haus}(Pos(P), [-1, 1]^2)$  varies lower semi-continuously as P moves in  $V(d) \setminus \{0\}$ . Multiplying P by a positive constant does not change Pos(P), and so we can restrict attention to polynomials in the unit sphere of V(d). By compactness the infimum is attained. But if  $dist_{Haus}(Pos(P), [-1, 1]^2)$  were zero, we would have P = 0 on the boundary of the square. Then P would vanish on the line x = 1, and (x - 1) would factor out of P. Write P as  $(1 - x)^a P_1(x, y)$ , where (1 - x) does not divide  $P_1$ . The polynomial  $P_1$  vanishes at only finitely many points of the line x = 1. If a is even, then we see that  $P_1$  needs to vanish on the side of the square where x = 1, and then 1 - x divides  $P_1$ , and we get a contradiction. If a is odd, then we see that  $P_1$  needs to vanish on the part of the line x = 1 where |y| > 1. This still implies that 1 - x divides  $P_1$ , and we get a contradiction.

If d is even, a nice example is the polynomial  $P_d = 1 - x^d - y^d$ . The set  $Pos(P_d)$  is the unit ball in the  $L^d$  norm. As  $d \to \infty$ , it approaches the square, which is the unit ball in the  $L^\infty$  norm. For every even d,  $Pos(P_d) \subset [-1,1]^2$ , and  $P_d > 0$  on the square  $[-(1/2)^{1/d}, (1/2)^{1/d}]$ . Now  $1 - (1/2)^{1/d} \sim 1/d$ , and so  $dist_{Haus}(Pos(P_d), [-1,1]^2) \sim 1/d$ . Hence  $\epsilon(d) \lesssim 1/d$ . It seems plausible that  $P_d$  is near-optimal and that  $\epsilon(d) \gtrsim 1/d$ .

The hard problem is to give quantitative lower bounds on  $\epsilon(d)$ . I don't know of any explicit lower bound in the literature. I worked on the problem, and I had a plan for a lower bound of the form  $e^{-e^d}$ ...

I think the moral issue is to give quantitative bounds on how sharply a degree d curve can make a certain type of turn. It's important to keep in mind the following example. The zero set of the hyperbola  $xy = \epsilon$  makes a very sharp turn near the origin, which looks something like the corner of a square. But the hyperbola has two branches, and so instead of being positive on approximately one quartant, it is positive on two opposite quartants, and its positive set does not really look like the neighborhood of a corner of a square. An algebraic curve can make an arbitrarily sharp turn if it looks locally like a hyperbola with two branches, but it is harder for it to make a sharp turn with only one branch.

I might have gone on too long about this toy problem. A solution to this problem would not directly lead to any bounds on Kakeya. Trying to go further with the polynomial method and tubes, this type of estimate seems to come up. In general, it

might be helpful to have more quantitative estimates about the geometry of degree d algebraic surfaces.

# MIT OpenCourseWare http://ocw.mit.edu

18.S997 The Polynomial Method Fall 2012

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
