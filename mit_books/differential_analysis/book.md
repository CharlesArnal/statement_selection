# LECTURE NOTES FOR 18.155, FALL 2004

#### RICHARD B. MELROSE

### Contents

| Introduction |                                     | 1   |
|--------------|-------------------------------------|-----|
| 1.           | Continuous functions                | 2   |
| 2.           | Measures and $\sigma$ -algebras     | 10  |
| 3.           | Measureability of functions         | 16  |
| 4.           | Integration                         | 19  |
| 5.           | Hilbert space                       | 30  |
| 6.           | Test functions                      | 34  |
| 7.           | Tempered distributions              | 42  |
| 8.           | Convolution and density             | 47  |
| 9.           | Fourier inversion                   | 58  |
| 10.          | Sobolev embedding                   | 63  |
| 11.          | Differential operators.             | 67  |
| 12.          | Cone support and wavefront set      | 83  |
| 13.          | Homogeneous distributions           | 96  |
| 14.          | Wave equation                       | 97  |
| 15.          | Operators and kernels               | 98  |
| 16.          | Spectral theorem                    | 99  |
| 17.          | Problems                            | 103 |
| 18.          | Solutions to (some of) the problems | 130 |
| References   |                                     | 136 |

### Introduction

These notes are for the course the graduate analysis course (18.155) at MIT in Fall 2004. They are based on earlier notes for similar courses in 1997, 2001 and 2002. In giving the lectures I may cut some corners!

I wish to particularly thank Austin Frakt for many comments on, and corrections to, an earlier version of these notes. Others who made helpful comments or noted errors include Philip Dorrell, ....

#### 1. Continuous functions

A the beginning I want to remind you of things I think you already know and then go on to show the direction the course will be taking. Let me first try to set the context.

One basic notion I assume you are reasonably familiar with is that of a *metric space* ([5] p.9). This consists of a set, X, and a distance function

$$d: X \times X = X^2 \longrightarrow [0, \infty)$$
,

satisfying the following three axioms:

i) 
$$d(x,y) = 0 \Leftrightarrow x = y$$
, (and  $d(x,y) \ge 0$ )

$$(1.1) ii) d(x,y) = d(y,x) \forall x, y \in X$$

$$iii)$$
  $d(x,y) \le d(x,z) + d(z,y) \ \forall \ x,y,z \in X.$ 

The basic theory of metric spaces deals with properties of subsets (open, closed, compact, connected), sequences (convergent, Cauchy) and maps (continuous) and the relationship between these notions. Let me just remind you of one such result.

**Proposition 1.1.** A map  $f: X \to Y$  between metric spaces is continuous if and only if one of the three following equivalent conditions holds

- (1)  $f^{-1}(O) \subset X$  is open  $\forall O \subset Y$  open.
- (2)  $f^{-1}(C) \subset X$  is closed  $\forall C \subset Y$  closed.
- (3)  $\lim_{n\to\infty} f(x_n) = f(x)$  in Y if  $x_n \to x$  in X.

The basic example of a metric space is Euclidean space. Real n-dimensional Euclidean space,  $\mathbb{R}^n$ , is the set of ordered n-tuples of real numbers

$$x = (x_1, \dots, x_n) \in \mathbb{R}^n, x_j \in \mathbb{R}, j = 1, \dots, n.$$

It is also the basic example of a vector (or linear) space with the operations

$$x + y = (x_1 + y_1, x_2 + y_2, \dots, x_n + y_n)$$
  
 $cx = (cx_1, \dots, cx_n).$ 

The metric is usually taken to be given by the Euclidean metric

$$|x| = (x_1^2 + \dots + x_n^2)^{1/2} = (\sum_{j=1}^n x_j^2)^{1/2},$$

in the sense that

$$d(x,y) = |x - y|.$$

Let us abstract this immediately to the notion of a normed vector space, or normed space. This is a vector space V (over  $\mathbb{R}$  or  $\mathbb{C}$ ) equipped with a *norm*, which is to say a function

$$\| \ \| : V \longrightarrow [0, \infty)$$

satisfying

(1.2) 
$$i) ||v|| = 0 \iff v = 0,$$
$$ii) ||cv|| = |c| ||v|| \forall c \in \mathbb{K},$$
$$iii) ||v + w|| \le ||v|| + ||w||.$$

This means that (V, d), d(v, w) = ||v - w|| is a vector space; I am also using  $\mathbb{K}$  to denote either  $\mathbb{R}$  or  $\mathbb{C}$  as is appropriate.

The case of a finite dimensional normed space is not very interesting because, apart from the dimension, they are all "the same". We shall say (in general) that two norms  $\| \bullet \|_1$  and  $\| \bullet \|_2$  on V are equivalent of there exists C > 0 such that

$$\frac{1}{C} \|v\|_1 \le \|v\|_2 \le C \|v\|_1 \,\, \forall \,\, v \in V \,.$$

**Proposition 1.2.** Any two norms on a finite dimensional vector space are equivalent.

So, we are mainly interested in the infinite dimensional case. I will start the course, in a slightly unorthodox manner, by concentrating on one such normed space (really one class). Let X be a metric space. The case of a continuous function,  $f: X \to \mathbb{R}$  (or  $\mathbb{C}$ ) is a special case of Proposition 1.1 above. We then define

$$C(X) = \{f : X \to \mathbb{R}, f \text{ bounded and continuous}\}.$$

In fact the same notation is generally used for the space of complexvalued functions. If we want to distinguish between these two possibilities we can use the more pedantic notation  $C(X;\mathbb{R})$  and  $C(X;\mathbb{C})$ . Now, the 'obvious' norm on this linear space is the supremum (or 'uniform') norm

$$||f||_{\infty} = \sup_{x \in X} |f(x)|.$$

Here X is an arbitrary metric space. For the moment X is supposed to be a "physical" space, something like  $\mathbb{R}^n$ . Corresponding to the finite-dimensionality of  $\mathbb{R}^n$  we often assume (or demand) that X is *locally compact*. This just means that every point has a compact neighborhood, i.e., is in the interior of a compact set. Whether locally

compact or not we can consider

$$(1.3) \quad \mathcal{C}_0(X) = \left\{ f \in \mathcal{C}(X); \forall \ \epsilon > 0 \ \exists \ K \in Xs.t. \sup_{x \notin K} |f(x)| \le \epsilon \right\}.$$

Here the notation  $K \subseteq X$  means 'K is a compact subset of X'.

If V is a normed linear space we are particularly interested in the continuous linear functionals on V. Here 'functional' just means function but V is allowed to be 'large' (not like  $\mathbb{R}^n$ ) so 'functional' is used for historical reasons.

**Proposition 1.3.** The following are equivalent conditions on a linear functional  $u: V \longrightarrow \mathbb{R}$  on a normed space V.

- (1) u is continuous.
- (2) u is continuous at 0.
- (3)  $\{u(f) \in \mathbb{R} : f \in V, ||f|| \le 1\}$  is bounded. (4)  $\exists C \text{ s.t. } |u(f)| \le C||f|| \forall f \in V.$

*Proof.* (1)  $\Longrightarrow$  (2) by definition. Then (2) implies that  $u^{-1}(-1,1)$  is a neighborhood of  $0 \in V$ , so for some  $\epsilon > 0$ ,  $u(\{f \in V; ||f|| < \epsilon\}) \subset$ (-1,1). By linearity of  $u, u(\{f \in V; ||f|| < 1\}) \subset (-\frac{1}{\epsilon}, \frac{1}{\epsilon})$  is bounded, so  $(2) \Longrightarrow (3)$ . Then (3) implies that

$$|u(f)| \le C \ \forall \ f \in V, ||f|| \le 1$$

for some C. Again using linearity of u, if  $f \neq 0$ ,

$$|u(f)| \le ||f||u\left(\frac{f}{||f||}\right) \le C||f||,$$

giving (4). Finally, assuming (4),

$$|u(f) - u(g)| = |u(f - g)| \le C||f - g||$$

shows that u is continuous at any point  $q \in V$ .

In view of this identification, continuous linear functionals are often said to be bounded. One of the important ideas that we shall exploit later is that of 'duality'. In particular this suggests that it is a good idea to examine the totality of bounded linear functionals on V. The dual space is

$$V' = V^* = \{u : V \longrightarrow \mathbb{K}, \text{ linear and bounded}\}.$$

This is also a normed linear space where the linear operations are

(1.4) 
$$(u+v)(f) = u(f) + v(f)$$
  $\forall f \in V.$ 

The natural norm on V' is

$$||u|| = \sup_{\|f\| \le 1} |u(f)|.$$

This is just the 'best constant' in the boundedness estimate,

$$||u|| = \inf \{C; |u(f)| \le C||f|| \ \forall \ f \subset V\}$$
.

One of the basic questions I wish to pursue in the first part of the course is: What is the dual of  $C_0(X)$  for a locally compact metric space X? The answer is given by Riesz' representation theorem, in terms of (Borel) measures.

Let me give you a vague picture of 'regularity of functions' which is what this course is about, even though I have not introduced most of these spaces yet. Smooth functions (and small spaces) are towards the top. Duality flips up and down and as we shall see  $L^2$ , the space of Lebesgue square-integrable functions, is generally 'in the middle'. What I will discuss first is the right side of the diagramme, where we have the space of continuous functions on  $\mathbb{R}^n$  which vanish at infinity and its dual space,  $M_{\text{fin}}(\mathbb{R}^n)$ , the space of finite Borel measures. There are many other spaces that you may encounter, here I only include test functions, Schwartz functions, Sobolev spaces and their duals; k is a general positive integer.

I have set the goal of understanding the dual space  $M_{\text{fin}}(\mathbb{R}^n)$  of  $\mathcal{C}_0(X)$ , where X is a locally compact metric space. This will force me to go through the elements of measure theory and Lebesgue integration. It does require a little forcing!

The basic case of interest is  $\mathbb{R}^n$ . Then an obvious example of a continuous linear functional on  $\mathcal{C}_0(\mathbb{R}^n)$  is given by Riemann integration,

for instance over the unit cube  $[0,1]^n$ :

$$u(f) = \int_{[0,1]^n} f(x) dx$$
.

In some sense we must show that *all* continuous linear functionals on  $C_0(X)$  are given by integration. However, we have to interpret integration somewhat widely since there are also *evaluation functionals*. If  $z \in X$  consider the Dirac delta

$$\delta_z(f) = f(z)$$
.

This is also called a *point mass* of z. So we need a theory of measure and integration wide enough to include both of these cases.

One special feature of  $C_0(X)$ , compared to general normed spaces, is that there is a notion of positivity for its elements. Thus  $f \geq 0$  just means  $f(x) \geq 0 \ \forall \ x \in X$ .

**Lemma 1.4.** Each  $f \in C_0(X)$  can be decomposed uniquely as the difference of its positive and negative parts

$$(1.6) f = f_{+} - f_{-}, f_{\pm} \in \mathcal{C}_{0}(X), f_{\pm}(x) \leq |f(x)| \ \forall \ x \in X.$$

*Proof.* Simply define

$$f_{\pm}(x) = \begin{cases} \pm f(x) & \text{if } \pm f(x) \ge 0\\ 0 & \text{if } \pm f(x) < 0 \end{cases}$$

for the same sign throughout. Then (1.6) holds. Observe that  $f_+$  is continuous at each  $y \in X$  since, with U an appropriate neighborhood of y, in each case

$$f(y) > 0 \Longrightarrow f(x) > 0 \text{ for } x \in U \Longrightarrow f_{+} = f \text{ in } U$$
  
 $f(y) < 0 \Longrightarrow f(x) < 0 \text{ for } x \in U \Longrightarrow f_{+} = 0 \text{ in } U$   
 $f(y) = 0 \Longrightarrow \text{ given } \epsilon > 0 \exists U \text{ s.t. } |f(x)| < \epsilon \text{ in } U$   
 $\Longrightarrow |f_{+}(x)| < \epsilon \text{ in } U$ .

Thus  $f_- = f - f_+ \in \mathcal{C}_0(X)$ , since both  $f_+$  and  $f_-$  vanish at infinity.  $\square$ 

We can similarly split elements of the dual space into positive and negative parts although it is a little bit more delicate. We say that  $u \in (\mathcal{C}_0(X))'$  is positive if

$$(1.7) u(f) \ge 0 \ \forall \ 0 \le f \in \mathcal{C}_0(X).$$

For a general (real)  $u \in (\mathcal{C}_0(X))'$  and for each  $0 \leq f \in \mathcal{C}_0(X)$  set

$$(1.8) \quad u_{+}(f) = \sup \{ u(g) \, ; \, g \in \mathcal{C}_{0}(X) \, , \, 0 \le g(x) \le f(x) \, \forall \, x \in X \} \, .$$

This is certainly finite since  $u(g) \leq C \|g\|_{\infty} \leq C \|f\|_{\infty}$ . Moreover, if  $0 < c \in \mathbb{R}$  then  $u_+(cf) = cu_+(f)$  by inspection. Suppose  $0 \leq f_i \in \mathcal{C}_0(X)$  for i = 1, 2. Then given  $\epsilon > 0$  there exist  $g_i \in \mathcal{C}_0(X)$  with  $0 \leq g_i(x) \leq f_i(x)$  and

$$u_+(f_i) \le u(g_i) + \epsilon$$
.

It follows that  $0 \le g(x) \le f_1(x) + f_2(x)$  if  $g = g_1 + g_2$  so

$$u_{+}(f_1 + f_2) \ge u(g) = u(g_1) + u(g_2) \ge u_{+}(f_1) + u_{+}(f_2) - 2\epsilon$$
.

Thus

$$u_{+}(f_1 + f_2) \ge u_{+}(f_1) + u_{+}(f_2).$$

Conversely, if  $0 \le g(x) \le f_1(x) + f_2(x)$  set  $g_1(x) = \min(g, f_1) \in \mathcal{C}_0(X)$  and  $g_2 = g - g_1$ . Then  $0 \le g_i \le f_i$  and  $u_+(f_1) + u_+(f_2) \ge u(g_1) + u(g_2) = u(g)$ . Taking the supremum over  $g, u_+(f_1 + f_2) \le u_+(f_1) + u_+(f_2)$ , so we find

$$(1.9) u_+(f_1 + f_2) = u_+(f_1) + u_+(f_2).$$

Having shown this effective linearity on the positive functions we can obtain a linear functional by setting

$$(1.10) u_+(f) = u_+(f_+) - u_+(f_-) \ \forall \ f \in \mathcal{C}_0(X) .$$

Note that (1.9) shows that  $u_+(f) = u_+(f_1) - u_+(f_2)$  for any decomposition of  $f = f_1 - f_2$  with  $f_i \in \mathcal{C}_0(X)$ , both positive. [Since  $f_1 + f_- = f_2 + f_+$  so  $u_+(f_1) + u_+(f_-) = u_+(f_2) + u_+(f_+)$ .] Moreover,

$$|u_{+}(f)| \le \max(u_{+}(f_{+}), u(f_{-})) \le ||u|| ||f||_{\infty}$$
  
 $\implies ||u_{+}|| \le ||u||.$ 

The functional

$$u_{-} = u_{+} - u$$

is also positive, since  $u_+(f) \ge u(f)$  for all  $0 \le f \in \mathcal{C}_0(x)$ . Thus we have proved

**Lemma 1.5.** Any element  $u \in (\mathcal{C}_0(X))'$  can be decomposed,

$$u = u_+ - u_-$$

into the difference of positive elements with

$$||u_{+}||, ||u_{-}|| \leq ||u||.$$

The idea behind the definition of  $u_+$  is that u itself is, more or less, "integration against a function" (even though we do *not* know how to interpret this yet). In defining  $u_+$  from u we are effectively throwing away the negative part of that 'function.' The next step is to show that a positive functional corresponds to a 'measure' meaning a function

measuring the size of sets. To define this we really want to evaluate u on the characteristic function of a set

$$\chi_E(x) = \begin{cases} 1 & \text{if } x \in E \\ 0 & \text{if } x \notin E \end{cases}.$$

The problem is that  $\chi_E$  is not continuous. Instead we use an idea similar to (1.8).

If  $0 \le u \in (\mathcal{C}_0(X))'$  and  $U \subset X$  is open, set<sup>1</sup>

(1.11) 
$$\mu(U) = \sup \{ u(f); 0 \le f(x) \le 1, f \in \mathcal{C}_0(X), \sup f(f) \in U \}$$
.

Here the support of f, supp(f), is the *closure* of the set of points where  $f(x) \neq 0$ . Thus supp(f) is always closed, in (1.11) we only admit f if its support is a compact subset of U. The reason for this is that, only then do we 'really know' that  $f \in \mathcal{C}_0(X)$ .

Suppose we try to measure general sets in this way. We can do this by defining

(1.12) 
$$\mu^*(E) = \inf \{ \mu(U) \, ; \, U \supset E \, , \, U \text{ open} \} .$$

Already with  $\mu$  it may happen that  $\mu(U) = \infty$ , so we think of

$$(1.13)$$

as defined on the *power set* of X and taking values in the extended positive real numbers.

**Definition 1.6.** A positive extended function,  $\mu^*$ , defined on the power set of X is called an outer measure if  $\mu^*(\emptyset) = 0$ ,  $\mu^*(A) \leq \mu^*(B)$  whenever  $A \subset B$  and

(1.14) 
$$\mu^*(\bigcup_j A_j) \le \sum_j \mu(A_j) \ \forall \ \{A_j\}_{j=1}^{\infty} \subset \mathcal{P}(X).$$

**Lemma 1.7.** If u is a positive continuous linear functional on  $C_0(X)$  then  $\mu^*$ , defined by (1.11), (1.12) is an outer measure.

To prove this we need to find enough continuous functions. I have relegated the proof of the following result to Problem 2.

**Lemma 1.8.** Suppose  $U_i$ , i = 1, ..., N is a finite collection of open sets in a locally compact metric space and  $K \subseteq \bigcup_{i=1}^{N} U_i$  is a compact subset, then there exist continuous functions  $f_i \in C(X)$  with  $0 \le f_i \le 1$ , supp $(f_i) \subseteq U_i$  and

(1.15) 
$$\sum_{i} f_{i} = 1 \text{ in a neighborhood of } K.$$

<sup>&</sup>lt;sup>1</sup>See [5] starting p.42 or [1] starting p.206.

Proof of Lemma 1.7. We have to prove (1.14). Suppose first that the  $A_i$  are open, then so is  $A = \bigcup_i A_i$ . If  $f \in C(X)$  and  $\operatorname{supp}(f) \subseteq A$  then  $\operatorname{supp}(f)$  is covered by a finite union of the  $A_i$ s. Applying Lemma 1.8 we can find  $f_i$ 's, all but a finite number identically zero, so  $\operatorname{supp}(f_i) \subseteq A_i$  and  $\sum_i f_i = 1$  in a neighborhood of  $\operatorname{supp}(f)$ .

Since  $f = \sum_{i} f_{i} f$  we conclude that

$$u(f) = \sum_{i} u(f_i f) \Longrightarrow \mu^*(A) \le \sum_{i} \mu^*(A_i)$$

since  $0 \le f_i f \le 1$  and supp $(f_i f) \in A_i$ .

Thus (1.14) holds when the  $A_i$  are open. In the general case if  $A_i \subset B_i$  with the  $B_i$  open then, from the definition,

$$\mu^*(\bigcup_i A_i) \le \mu^*(\bigcup_i B_i) \le \sum_i \mu^*(B_i).$$

Taking the infimum over the  $B_i$  gives (1.14) in general.

### 2. Measures and $\sigma$ -algebras

An outer measure such as  $\mu^*$  is a rather crude object since, even if the  $A_i$  are disjoint, there is generally strict inequality in (1.14). It turns out to be unreasonable to expect equality in (1.14), for disjoint unions, for a function defined on all subsets of X. We therefore restrict attention to smaller collections of subsets.

**Definition 2.1.** A collection of subsets  $\mathcal{M}$  of a set X is a  $\sigma$ -algebra if

- (1)  $\phi, X \in \mathcal{M}$
- (2)  $E \in \mathcal{M} \Longrightarrow E^C = X \backslash E \in \mathcal{M}$
- (3)  $\{E_i\}_{i=1}^{\infty} \subset \mathcal{M} \Longrightarrow \bigcup_{i=1}^{\infty} E_i \in \mathcal{M}.$

For a general outer measure  $\mu^*$  we define the notion of  $\mu^*$ -measurability of a set.

**Definition 2.2.** A set  $E \subset X$  is  $\mu^*$ -measurable (for an outer measure  $\mu^*$  on X) if

(2.1) 
$$\mu^*(A) = \mu^*(A \cap E) + \mu^*(A \cap E^{\complement}) \ \forall \ A \subset X.$$

**Proposition 2.3.** The collection of  $\mu^*$ -measurable sets for any outer measure is a  $\sigma$ -algebra.

*Proof.* Suppose E is  $\mu^*$ -measurable, then  $E^C$  is  $\mu^*$ -measurable by the symmetry of (2.1).

Suppose A, E and F are any three sets. Then

$$A \cap (E \cup F) = (A \cap E \cap F) \cup (A \cap E \cap F^C) \cup (A \cap E^C \cap F)$$
$$A \cap (E \cup F)^C = A \cap E^C \cap F^C.$$

From the subadditivity of  $\mu^*$ 

$$\mu^{*}(A \cap (E \cup F)) + \mu^{*}(A \cap (E \cup F)^{C})$$

$$\leq \mu^{*}(A \cap E \cap F) + \mu^{*}(A \cap E \cup F^{C})$$

$$+ \mu^{*}(A \cap E^{C} \cap F) + \mu^{*}(A \cap E^{C} \cap F^{C}).$$

Now, if E and F are  $\mu^*$ -measurable then applying the definition twice, for any A,

$$\mu^{*}(A) = \mu^{*}(A \cap E \cap F) + \mu^{*}(A \cap E \cap F^{C}) + \mu^{*}(A \cap E^{C} \cap F) + \mu^{*}(A \cap E^{C} \cap F^{C})$$
$$\geq \mu^{*}(A \cap (E \cup F)) + \mu^{*}(A \cap (E \cup F)^{C}).$$

The reverse inequality follows from the subadditivity of  $\mu^*$ , so  $E \cup F$  is also  $\mu^*$ -measurable.

If  $\{E_i\}_{i=1}^{\infty}$  is a sequence of disjoint  $\mu^*$ -measurable sets, set  $F_n = \bigcup_{i=1}^n E_i$  and  $F = \bigcup_{i=1}^{\infty} E_i$ . Then for any A,

$$\mu^*(A \cap F_n) = \mu^*(A \cap F_n \cap E_n) + \mu^*(A \cap F_n \cap E_n^C)$$
  
=  $\mu^*(A \cap E_n) + \mu^*(A \cap F_{n-1})$ .

Iterating this shows that

$$\mu^*(A \cap F_n) = \sum_{i=1}^n \mu^*(A \cap E_j).$$

From the  $\mu^*$ -measurability of  $F_n$  and the subadditivity of  $\mu^*$ ,

$$\mu^*(A) = \mu^*(A \cap F_n) + \mu^*(A \cap F_n^C)$$
  
 
$$\geq \sum_{j=1}^n \mu^*(A \cap E_j) + \mu^*(A \cap F^C).$$

Taking the limit as  $n \to \infty$  and using subadditivity,

(2.2) 
$$\mu^*(A) \ge \sum_{j=1}^{\infty} \mu^*(A \cap E_j) + \mu^*(A \cap F^C)$$
$$\ge \mu^*(A \cap F) + \mu^*(A \cap F^C) \ge \mu^*(A)$$

proves that inequalities are equalities, so F is also  $\mu^*$ -measurable. In general, for *any* countable union of  $\mu^*$ -measurable sets,

$$\bigcup_{j=1}^{\infty} A_j = \bigcup_{j=1}^{\infty} \widetilde{A}_j,$$

$$\widetilde{A}_j = A_j \setminus \bigcup_{i=1}^{j-1} A_i = A_j \cap \left(\bigcup_{i=1}^{j-1} A_i\right)^C$$

is  $\mu^*$ -measurable since the  $\widetilde{A}_j$  are disjoint.

A measure (sometimes called a positive measure) is an extended function defined on the elements of a  $\sigma$ -algebra  $\mathcal{M}$ :

$$\mu: \mathcal{M} \to [0, \infty]$$

such that

$$\mu(\emptyset) = 0 \text{ and }$$

(2.4) 
$$\mu\left(\bigcup_{i=1}^{\infty} A_i\right) = \sum_{i=1}^{\infty} \mu(A_i)$$
 if  $\{A_i\}_{i=1}^{\infty} \subset \mathcal{M} \text{ and } A_i \cap A_j = \phi \ i \neq j.$ 

The elements of  $\mathcal{M}$  with measure zero, i.e.,  $E \in \mathcal{M}$ ,  $\mu(E) = 0$ , are supposed to be 'ignorable'. The measure  $\mu$  is said to be *complete* if

(2.5) 
$$E \subset X \text{ and } \exists F \in \mathcal{M}, \mu(F) = 0, E \subset F \Rightarrow E \in \mathcal{M}.$$

See Problem 4.

The first part of the following important result due to Caratheodory was shown above.

**Theorem 2.4.** If  $\mu^*$  is an outer measure on X then the collection of  $\mu^*$ -measurable subsets of X is a  $\sigma$ -algebra and  $\mu^*$  restricted to  $\mathcal{M}$  is a complete measure.

*Proof.* We have already shown that the collection of  $\mu^*$ -measurable subsets of X is a  $\sigma$ -algebra. To see the second part, observe that taking A = F in (2.2) gives

$$\mu^*(F) = \sum_{j} \mu^*(E_j) \text{ if } F = \bigcup_{j=1}^{\infty} E_j$$

and the  $E_i$  are disjoint elements of  $\mathcal{M}$ . This is (2.4).

Similarly if  $\mu^*(E) = 0$  and  $F \subset E$  then  $\mu^*(F) = 0$ . Thus it is enough to show that for any subset  $E \subset X$ ,  $\mu^*(E) = 0$  implies  $E \in \mathcal{M}$ . For any  $A \subset X$ , using the fact that  $\mu^*(A \cap E) = 0$ , and the 'increasing' property of  $\mu^*$ 

$$\mu^*(A) \le \mu^*(A \cap E) + \mu^*(A \cap E^C)$$
  
=  $\mu^*(A \cap E^C) \le \mu^*(A)$ 

shows that these must always be equalities, so  $E \in \mathcal{M}$  (i.e., is  $\mu^*$ -measurable).

Going back to our primary concern, recall that we constructed the outer measure  $\mu^*$  from  $0 \le u \in (\mathcal{C}_0(X))'$  using (1.11) and (1.12). For the measure whose existence follows from Caratheodory's theorem to be much use we need

**Proposition 2.5.** If  $0 \le u \in (\mathcal{C}_0(X))'$ , for X a locally compact metric space, then each open subset of X is  $\mu^*$ -measurable for the outer measure defined by (1.11) and (1.12) and  $\mu$  in (1.11) is its measure.

*Proof.* Let  $U \subset X$  be open. We only need to prove (2.1) for all  $A \subset X$  with  $\mu^*(A) < \infty$ .<sup>2</sup>

 $<sup>^2</sup>$ Why?

Suppose first that  $A \subset X$  is open and  $\mu^*(A) < \infty$ . Then  $A \cap U$  is open, so given  $\epsilon > 0$  there exists  $f \in C(X)$  supp $(f) \in A \cap U$  with  $0 \le f \le 1$  and

$$\mu^*(A \cap U) = \mu(A \cap U) \le u(f) + \epsilon.$$

Now,  $A \setminus \text{supp}(f)$  is also open, so we can find  $g \in C(X)$ ,  $0 \le g \le 1$ ,  $\text{supp}(g) \subseteq A \setminus \text{supp}(f)$  with

$$\mu^*(A \setminus \text{supp}(f)) = \mu(A \setminus \text{supp}(f)) \le u(g) + \epsilon.$$

Since

$$\begin{split} A \backslash \operatorname{supp}(f) \supset A \cap U^C, \ 0 &\leq f + g \leq 1, \ \operatorname{supp}(f + g) \Subset A, \\ \mu(A) &\geq u(f + g) = u(f) + u(g) \\ &> \mu^*(A \cap U) + \mu^*(A \cap U^C) - 2\epsilon \\ &\geq \mu^*(A) - 2\epsilon \end{split}$$

using subadditivity of  $\mu^*$ . Letting  $\epsilon \downarrow 0$  we conclude that

$$\mu^*(A) \le \mu^*(A \cap U) + \mu^*(A \cap U^C) \le \mu^*(A) = \mu(A)$$
.

This gives (2.1) when A is open.

In general, if  $E \subset X$  and  $\mu^*(E) < \infty$  then given  $\epsilon > 0$  there exists  $A \subset X$  open with  $\mu^*(E) > \mu^*(A) - \epsilon$ . Thus,

$$\mu^*(E) \ge \mu^*(A \cap U) + \mu^*(A \cap U^C) - \epsilon$$
$$\ge \mu^*(E \cap U) + \mu^*(E \cap U^C) - \epsilon$$
$$\ge \mu^*(E) - \epsilon.$$

This shows that (2.1) always holds, so U is  $\mu^*$ -measurable if it is open. We have already observed that  $\mu(U) = \mu^*(U)$  if U is open.

Thus we have shown that the  $\sigma$ -algebra given by Caratheodory's theorem contains all open sets. You showed in Problem 3 that the intersection of any collection of  $\sigma$ -algebras on a given set is a  $\sigma$ -algebra. Since  $\mathcal{P}(X)$  is always a  $\sigma$ -algebra it follows that for *any* collection  $\mathcal{E} \subset \mathcal{P}(X)$  there is always a smallest  $\sigma$ -algebra containing  $\mathcal{E}$ , namely

$$\mathcal{M}_{\mathcal{E}} = \bigcap \{ \mathcal{M} \supset \mathcal{E} ; \mathcal{M} \text{ is a } \sigma\text{-algebra }, \mathcal{M} \subset \mathcal{P}(X) \}$$
.

The elements of the smallest  $\sigma$ -algebra containing the *open sets* are called 'Borel sets'. A measure defined on the  $\sigma$ -algebra of all Borel sets is called a *Borel measure*. This we have shown:

**Proposition 2.6.** The measure defined by (1.11), (1.12) from  $0 \le u \in (\mathcal{C}_0(X))'$  by Caratheodory's theorem is a Borel measure.

*Proof.* This is what Proposition 2.5 says! See how easy proofs are.  $\square$ 

We can even continue in the same vein. A Borel measure is said to be outer regular on  $E \subset X$  if

(2.6) 
$$\mu(E) = \inf \{ \mu(U) ; U \supset E, U \text{ open} \}.$$

Thus the measure constructed in Proposition 2.5 is outer regular on all Borel sets! A Borel measure is  $inner\ regular$  on E if

(2.7) 
$$\mu(E) = \sup \{ \mu(K) ; K \subset E, K \text{ compact} \}.$$

Here we need to know that compact sets are Borel measurable. This is Problem 5.

**Definition 2.7.** A Radon measure (on a metric space) is a Borel measure which is outer regular on all Borel sets, inner regular on open sets and finite on compact sets.

**Proposition 2.8.** The measure defined by (1.11), (1.12) from  $0 \le u \in (\mathcal{C}_0(X))'$  using Caratheodory's theorem is a Radon measure.

*Proof.* Suppose  $K \subset X$  is compact. Let  $\chi_K$  be the characteristic function of K,  $\chi_K = 1$  on K,  $\chi_K = 0$  on  $K^C$ . Suppose  $f \in \mathcal{C}_0(X)$ , supp $(f) \in X$  and  $f \geq \chi_K$ . Set

$$U_{\epsilon} = \{ x \in X ; f(x) > 1 - \epsilon \}$$

where  $\epsilon > 0$  is small. Thus  $U_{\epsilon}$  is open, by the continuity of f and contains K. Moreover, we can choose  $g \in C(X)$ ,  $\operatorname{supp}(g) \subseteq U_{\epsilon}$ ,  $0 \le g \le 1$  with g = 1 near<sup>3</sup> K. Thus,  $g \le (1 - \epsilon)^{-1} f$  and hence

$$\mu^*(K) \le u(g) = (1 - \epsilon)^{-1} u(f)$$
.

Letting  $\epsilon \downarrow 0$ , and using the measurability of K,

$$\mu(K) \le u(f)$$
  
  $\Rightarrow \mu(K) = \inf \{ u(f) ; f \in C(X), \operatorname{supp}(f) \subseteq X, f \ge \chi_K \}.$ 

In particular this implies that  $\mu(K) < \infty$  if  $K \subseteq X$ , but is also proves (2.7).

Let me now review a little of what we have done. We used the positive functional u to define an outer measure  $\mu^*$ , hence a measure  $\mu$  and then checked the properties of the latter.

This is a pretty nice scheme; getting ahead of myself a little, let me suggest that we try it on something else.

<sup>&</sup>lt;sup>3</sup>Meaning in a neighborhood of K.

Let us say that  $Q \subset \mathbb{R}^n$  is 'rectangular' if it is a product of finite intervals (open, closed or half-open)

(2.8) 
$$Q = \prod_{i=1}^{n} (\operatorname{or}[a_i, b_i] \operatorname{or}) \ a_i \le b_i$$

we all agree on its standard volume:

(2.9) 
$$v(Q) = \prod_{i=1}^{n} (b_i - a_i) \in [0, \infty).$$

Clearly if we have two such sets,  $Q_1 \subset Q_2$ , then  $v(Q_1) \leq v(Q_2)$ . Let us try to define an outer measure on subsets of  $\mathbb{R}^n$  by

(2.10) 
$$v^*(A) = \inf \left\{ \sum_{i=1}^{\infty} v(Q_i); A \subset \bigcup_{i=1}^{\infty} Q_i, Q_i \text{ rectangular} \right\}.$$

We want to show that (2.10) does define an outer measure. This is pretty easy; certainly  $v(\emptyset) = 0$ . Similarly if  $\{A_i\}_{i=1}^{\infty}$  are (disjoint) sets and  $\{Q_{ij}\}_{i=1}^{\infty}$  is a covering of  $A_i$  by open rectangles then all the  $Q_{ij}$  together cover  $A = \bigcup_i A_i$  and

$$v^*(A) \le \sum_{i} \sum_{j} v(Q_{ij})$$
  
$$\Rightarrow v^*(A) \le \sum_{i} v^*(A_i).$$

So we have an outer measure. We also want

**Lemma 2.9.** If Q is rectangular then  $v^*(Q) = v(Q)$ .

Assuming this, the measure defined from  $v^*$  using Caratheodory's theorem is called Lebesgue measure.

**Proposition 2.10.** Lebesgue measure is a Borel measure.

To prove this we just need to show that (open) rectangular sets are  $v^*$ -measurable.

#### 3. Measureability of functions

Suppose that  $\mathcal{M}$  is a  $\sigma$ -algebra on a set  $X^4$  and  $\mathcal{N}$  is a  $\sigma$ -algebra on another set Y. A map  $f: X \to Y$  is said to be *measurable* with respect to these given  $\sigma$ -algebras on X and Y if

$$(3.1) f^{-1}(E) \in \mathcal{M} \ \forall \ E \in \mathcal{N}.$$

Notice how similar this is to one of the characterizations of continuity for maps between metric spaces in terms of open sets. Indeed this analogy yields a useful result.

**Lemma 3.1.** If  $G \subset \mathcal{N}$  generates  $\mathcal{N}$ , in the sense that

(3.2) 
$$\mathcal{N} = \bigcap \{ \mathcal{N}'; \mathcal{N}' \supset G, \ \mathcal{N}' \ a \ \sigma\text{-algebra} \}$$

then  $f: X \longrightarrow Y$  is measurable iff  $f^{-1}(A) \in \mathcal{M}$  for all  $A \in G$ .

*Proof.* The main point to note here is that  $f^{-1}$  as a map on power sets, is very well behaved for any map. That is if  $f: X \to Y$  then  $f^{-1}: \mathcal{P}(Y) \to \mathcal{P}(X)$  satisfies:

(3.3) 
$$f^{-1}(E^{C}) = (f^{-1}(E))^{C}$$

$$f^{-1}\left(\bigcup_{j=1}^{\infty} E_{j}\right) = \bigcup_{j=1}^{\infty} f^{-1}(E_{j})$$

$$f^{-1}\left(\bigcap_{j=1}^{\infty} E_{j}\right) = \bigcap_{j=1}^{\infty} f^{-1}(E_{j})$$

$$f^{-1}(\phi) = \phi, \ f^{-1}(Y) = X.$$

Putting these things together one sees that if  $\mathcal{M}$  is any  $\sigma$ -algebra on X then

(3.4) 
$$f_*(\mathcal{M}) = \left\{ E \subset Y; f^{-1}(E) \in \mathcal{M} \right\}$$

is always a  $\sigma$ -algebra on Y.

In particular if  $f^{-1}(A) \in \mathcal{M}$  for all  $A \in G \subset \mathcal{N}$  then  $f_*(\mathcal{M})$  is a  $\sigma$ -algebra containing G, hence containing  $\mathcal{N}$  by the generating condition. Thus  $f^{-1}(E) \in \mathcal{M}$  for all  $E \in \mathcal{N}$  so f is measurable.

**Proposition 3.2.** Any continuous map  $f: X \to Y$  between metric spaces is measurable with respect to the Borel  $\sigma$ -algebras on X and Y.

<sup>&</sup>lt;sup>4</sup>Then X, or if you want to be pedantic  $(X, \mathcal{M})$ , is often said to be a measure space or even a measurable space.

*Proof.* The continuity of f shows that  $f^{-1}(E) \subset X$  is open if  $E \subset Y$  is open. By definition, the open sets generate the Borel  $\sigma$ -algebra on Y so the preceding Lemma shows that f is Borel measurable i.e.,

$$f^{-1}(\mathcal{B}(Y)) \subset \mathcal{B}(X)$$
.

We are mainly interested in functions on X. If  $\mathcal{M}$  is a  $\sigma$ -algebra on X then  $f: X \to \mathbb{R}$  is measurable if it is measurable with respect to the Borel  $\sigma$ -algebra on  $\mathbb{R}$  and  $\mathcal{M}$  on X. More generally, for an extended function  $f: X \to [-\infty, \infty]$  we take as the 'Borel'  $\sigma$ -algebra in  $[-\infty, \infty]$  the smallest  $\sigma$ -algebra containing all open subsets of  $\mathbb{R}$  and all sets  $(a, \infty]$  and  $[-\infty, b)$ ; in fact it is generated by the sets  $(a, \infty]$ . (See Problem 6.)

Our main task is to define the integral of a measurable function: we start with *simple functions*. Observe that the characteristic function of a set

$$\chi_E = \left\{ \begin{array}{ll} 1 & x \in E \\ 0 & x \notin E \end{array} \right.$$

is measurable if and only if  $E \in \mathcal{M}$ . More generally a simple function,

$$(3.5) f = \sum_{i=1}^{N} a_i \chi_{E_i}, \ a_i \in \mathbb{R}$$

is measurable if the  $E_i$  are measurable. The presentation, (3.5), of a simple function is not unique. We can make it so, getting the minimal presentation, by insisting that all the  $a_i$  are non-zero and

$$E_i = \{ x \in E ; f(x) = a_i \}$$

then f in (3.5) is measurable iff all the  $E_i$  are measurable.

The Lebesgue integral is based on approximation of functions by simple functions, so it is important to show that this is possible.

**Proposition 3.3.** For any non-negative  $\mu$ -measurable extended function  $f: X \longrightarrow [0, \infty]$  there is an increasing sequence  $f_n$  of simple measurable functions such that  $\lim_{n\to\infty} f_n(x) = f(x)$  for each  $x \in X$  and this limit is uniform on any measurable set on which f is finite.

*Proof.* Folland [1] page 45 has a nice proof. For each integer n > 0 and  $0 \le k \le 2^{2n} - 1$ , set

$$E_{n,k} = \{x \in X; 2^{-n}k \le f(x) < 2^{-n}(k+1)\},$$
  
$$E'_n = \{x \in X; f(x) \ge 2^n\}.$$

These are measurable sets. On increasing n by one, the interval in the definition of  $E_{n,k}$  is divided into two. It follows that the sequence of simple functions

(3.6) 
$$f_n = \sum_{k} 2^{-n} k \chi_{E_{k,n}} + 2^n \chi_{E'_n}$$

is increasing and has limit f and that this limit is uniform on any measurable set where f is finite.  $\Box$ 

### 4. Integration

The  $(\mu)$ -integral of a non-negative simple function is by definition

(4.1) 
$$\int_{Y} f \, d\mu = \sum_{i} a_{i} \mu(Y \cap E_{i}), Y \in \mathcal{M}.$$

Here the convention is that if  $\mu(Y \cap E_i) = \infty$  but  $a_i = 0$  then  $a_i \cdot \mu(Y \cap E_i) = 0$ . Clearly this integral takes values in  $[0, \infty]$ . More significantly, if  $c \geq 0$  is a constant and f and g are two non-negative ( $\mu$ -measurable) simple functions then

(4.2) 
$$\int_{Y} cf d\mu = c \int_{Y} f d\mu$$

$$\int_{Y} (f+g) d\mu = \int_{Y} f d\mu + \int_{Y} g d\mu$$

$$0 \le f \le g \Rightarrow \int_{Y} f d\mu \le \int_{Y} g d\mu.$$

(See [1] Proposition 2.13 on page 48.)

To see this, observe that (4.1) holds for any presentation (3.5) of f with all  $a_i \geq 0$ . Indeed, by restriction to  $E_i$  and division by  $a_i$  (which can be assumed non-zero) it is enough to consider the special case

$$\chi_E = \sum_j b_j \chi_{F_j}.$$

The  $F_j$  can always be written as the union of a finite number, N', of disjoint measurable sets,  $F_j = \bigcup_{l \in S_j} G_l$  where j = 1, ..., N and  $S_j \subset \{1, ..., N'\}$ . Thus

$$\sum_{j} b_j \mu(F_j) = \sum_{j} b_j \sum_{l \in S_j} \mu(G_l) = \mu(E)$$

since  $\sum_{\{j;l\in S_j\}} b_j = 1$  for each j.

From this all the statements follow easily.

**Definition 4.1.** For a non-negative  $\mu$ -measurable extended function  $f: X \longrightarrow [0, \infty]$  the integral (with respect to  $\mu$ ) over any measurable set  $E \subset X$  is

$$(4.3) \quad \int_{E} f d\mu = \sup \{ \int_{E} h d\mu; \ 0 \le h \le f, \ h \ simple \ and \ measurable. \}$$

By taking suprema,  $\int_E f d\mu$  has the first and last properties in (4.2). It also has the middle property, but this is less obvious. To see this, we shall prove the basic 'Monotone convergence theorem' (of Lebesgue). Before doing so however, note what the vanishing of the integral means.

**Lemma 4.2.** If  $f: X \longrightarrow [0, \infty]$  is measurable then  $\int_E f d\mu = 0$  for a measurable set E if and only if

$$(4.4) \{x \in E; f(x) > 0\} \text{ has measure zero.}$$

*Proof.* If (4.4) holds, then any positive simple function bounded above by f must also vanish outside a set of measure zero, so its integral must be zero and hence  $\int_E f d\mu = 0$ . Conversely, observe that the set in (4.4) can be written as

$$E_n = \bigcup_n \{x \in E; f(x) > 1/n\}.$$

Since these sets increase with n, if (4.4) does not hold then one of these must have positive measure. In that case the simple function  $n^{-1}\chi_{E_n}$  has positive integral so  $\int_E f d\mu > 0$ .

Notice the fundamental difference in approach here between Riemann and Lebesgue integrals. The Lebesgue integral, (4.3), uses approximation by functions constant on possibly quite nasty measurable sets, not just intervals as in the Riemann lower and upper integrals.

**Theorem 4.3** (Monotone Convergence). Let  $f_n$  be an increasing sequence of non-negative measurable (extended) functions, then  $f(x) = \lim_{n\to\infty} f_n(x)$  is measurable and

$$(4.5) \qquad \int_{E} f d\mu = \lim_{n \to \infty} \int_{E} f_n d\mu$$

for any measurable set  $E \subset X$ .

*Proof.* To see that f is measurable, observe that

(4.6) 
$$f^{-1}(a, \infty] = \bigcup_{n} f_n^{-1}(a, \infty].$$

Since the sets  $(a, \infty]$  generate the Borel  $\sigma$ -algebra this shows that f is measurable.

So we proceed to prove the main part of the proposition, which is (4.5). Rudin has quite a nice proof of this, [5] page 21. Here I paraphrase it. We can easily see from (4.1) that

$$\alpha = \sup \int_{E} f_n d\mu = \lim_{n \to \infty} \int_{E} f_n d\mu \le \int_{E} f d\mu.$$

Given a simple measurable function g with  $0 \le g \le f$  and 0 < c < 1 consider the sets  $E_n = \{x \in E; f_n(x) \ge cg(x)\}$ . These are measurable and increase with n. Moreover  $E = \bigcup_n E_n$ . It follows that

(4.7) 
$$\int_{E} f_n d\mu \ge \int_{E_n} f_n d\mu \ge c \int_{E_n} g d\mu = \sum_{i} a_i \mu(E_n \cap F_i)$$

in terms of the natural presentation of  $g = \sum_i a_i \chi_{F_i}$ . Now, the fact that the  $E_n$  are measurable and increase to E shows that

$$\mu(E_n \cap F_i) \to \mu(E \cap F_i)$$

as  $n \to \infty$ . Thus the right side of (4.7) tends to  $c \int_E g d\mu$  as  $n \to \infty$ . Hence  $\alpha \ge c \int_E g d\mu$  for all 0 < c < 1. Taking the supremum over c and then over all such g shows that

$$\alpha = \lim_{n \to \infty} \int_E f_n d\mu \ge \sup \int_E g d\mu = \int_E f d\mu.$$

They must therefore be equal.

Now for instance the additivity in (4.1) for  $f \geq 0$  and  $g \geq 0$  any measurable functions follows from Proposition 3.3. Thus if  $f \geq 0$  is measurable and  $f_n$  is an approximating sequence as in the Proposition then  $\int_E f d\mu = \lim_{n\to\infty} \int_E f_n d\mu$ . So if f and g are two non-negative measurable functions then  $f_n(x) + g_n(x) \uparrow f + g(x)$  which shows not only that f + g is measurable by also that

$$\int_{E} (f+g)d\mu = \int_{E} f d\mu + \int_{E} g d\mu.$$

As with the definition of  $u_+$  long ago, this allows us to extend the definition of the integral to any *integrable* function.

**Definition 4.4.** A measurable extended function  $f: X \longrightarrow [-\infty, \infty]$  is said to be integrable on E if its positive and negative parts both have finite integrals over E, and then

$$\int_{E} f d\mu = \int_{E} f_{+} d\mu - \int_{E} f_{-} d\mu.$$

Notice if f is  $\mu$ -integrable then so is |f|. One of the objects we wish to study is the space of integrable functions. The fact that the integral of |f| can vanish encourages us to look at what at first seems a much more complicated object. Namely we consider an equivalence relation between integrable functions

(4.8) 
$$f_1 \equiv f_2 \iff \mu(\{x \in X; f_1(x) \neq f_2(x)\}) = 0.$$

That is we identify two such functions if they are equal 'off a set of measure zero.' Clearly if  $f_1 \equiv f_2$  in this sense then

$$\int_{X} |f_1| d\mu = \int_{X} |f_2| d\mu = 0, \ \int_{X} f_1 d\mu = \int_{X} f_2 d\mu.$$

A necessary condition for a measurable function  $f \geq 0$  to be integrable is

$$\mu\{x \in X; f(x) = \infty\} = 0.$$

Let E be the (necessarily measureable) set where  $f = \infty$ . Indeed, if this does not have measure zero, then the sequence of simple functions  $n\chi_E \leq f$  has integral tending to infinity. It follows that each equivalence class under (4.8) has a representative which is an honest function, i.e. which is finite everywhere. Namely if f is one representative then

$$f'(x) = \begin{cases} f(x) & x \notin E \\ 0 & x \in E \end{cases}$$

is also a representative.

We shall denote by  $L^1(X, \mu)$  the space consisting of such equivalence classes of integrable functions. This is a normed linear space as I ask you to show in Problem 11.

The monotone convergence theorem often occurrs in the slightly disguised form of Fatou's Lemma.

**Lemma 4.5** (Fatou). If  $f_k$  is a sequence of non-negative integrable functions then

$$\int \liminf_{n \to \infty} f_n \, d\mu \le \liminf_{n \to \infty} \int f_n \, d\mu \, .$$

*Proof.* Set  $F_k(x) = \inf_{n \geq k} f_n(x)$ . Thus  $F_k$  is an increasing sequence of non-negative functions with limiting function  $\liminf_{n \to \infty} f_n$  and  $F_k(x) \leq f_n(x) \forall n \geq k$ . By the monotone convergence theorem

$$\int \liminf_{n \to \infty} f_n \, d\mu = \lim_{k \to \infty} \int F_k(x) \, d\mu \le \liminf_{n \to \infty} \int f_n \, d\mu.$$

We further extend the integral to complex-valued functions, just saying that

$$f:X\to\mathbb{C}$$

is integrable if its real and imaginary parts are both integrable. Then, by definition,

$$\int_{E} f d\mu = \int_{E} \operatorname{Re} f d\mu + i \int_{E} \operatorname{Im} f d\mu$$

for any  $E \subset X$  measurable. It follows that if f is integrable then so is |f|. Furthermore

$$\left| \int_{E} f \, d\mu \right| \le \int_{E} |f| \, d\mu \, .$$

This is obvious if  $\int_E f d\mu = 0$ , and if not then

$$\int_{E} f \, d\mu = Re^{i\theta} \, R > 0 \,, \, \theta \subset [0, 2\pi) \,.$$

Then

$$\begin{split} \left| \int_E f \, d\mu \right| &= e^{-i\theta} \int_E f \, d\mu \\ &= \int_E e^{-i\theta} f \, d\mu \\ &= \int_E \mathbb{R} e(e^{-i\theta} f) \, d\mu \\ &\leq \int_E \left| \mathbb{R} e(e^{-i\theta} f) \right| \, d\mu \\ &\leq \int_E \left| e^{-i\theta} f \right| \, d\mu = \int_E |f| \, d\mu \, . \end{split}$$

The other important convergence result for integrals is Lebesgue's *Dominated convergence theorem*.

**Theorem 4.6.** If  $f_n$  is a sequence of integrable functions,  $f_k \to f$  a.e.<sup>5</sup> and  $|f_n| \le g$  for some integrable g then f is integrable and

$$\int f d\mu = \lim_{n \to \infty} \int f_n d\mu.$$

*Proof.* First we can make the sequence  $f_n(x)$  converge by changing all the  $f_n(x)$ 's to zero on a set of measure zero outside which they converge. This does not change the conclusions. Moreover, it suffices to suppose that the  $f_n$  are real-valued. Then consider

$$h_k = q - f_k > 0$$
.

Now,  $\liminf_{k\to\infty} h_k = g - f$  by the convergence of  $f_n$ ; in particular f is integrable. By monotone convergence and Fatou's lemma

$$\int (g-f)d\mu = \int \liminf_{k \to \infty} h_k \, d\mu \le \liminf_{k \to \infty} \int (g-f_k) \, d\mu$$
$$= \int g \, d\mu - \limsup_{k \to \infty} \int f_k \, d\mu.$$

Similarly, if  $H_k = g + f_k$  then

$$\int (g+f)d\mu = \int \liminf_{k \to \infty} H_k \, d\mu \le \int g \, d\mu + \liminf_{k \to \infty} \int f_k \, d\mu.$$

It follows that

$$\limsup_{k \to \infty} \int f_k \, d\mu \le \int f \, d\mu \le \liminf_{k \to \infty} \int f_k \, d\mu.$$

 $<sup>{}^{5}\</sup>mathrm{Means}$  on the complement of a set of measure zero.

Thus in fact

$$\int f_k \, d\mu \to \int f \, d\mu \, .$$

Having proved Lebesgue's theorem of dominated convergence, let me use it to show something important. As before, let  $\mu$  be a positive measure on X. We have defined  $L^1(X,\mu)$ ; let me consider the more general space  $L^p(X,\mu)$ . A measurable function

$$f:X\to\mathbb{C}$$

is said to be ' $L^p$ ', for  $1 \le p < \infty$ , if  $|f|^p$  is integrable<sup>6</sup>, i.e.,

$$\int_{Y} |f|^p d\mu < \infty.$$

As before we consider equivalence classes of such functions under the equivalence relation

$$(4.9) f \sim g \Leftrightarrow \mu \left\{ x; (f-g)(x) \neq 0 \right\} = 0.$$

We denote by  $L^p(X,\mu)$  the space of such equivalence classes. It is a linear space and the function

(4.10) 
$$||f||_p = \left( \int_X |f|^p \ d\mu \right)^{1/p}$$

is a norm (we always assume  $1 \le p < \infty$ , sometimes p = 1 is excluded but later  $p = \infty$  is allowed). It is straightforward to check everything except the triangle inequality. For this we start with

**Lemma 4.7.** If  $a \ge 0$ ,  $b \ge 0$  and  $0 < \gamma < 1$  then

$$(4.11) a^{\gamma}b^{1-\gamma} \le \gamma a + (1-\gamma)b$$

with equality only when a = b.

*Proof.* If b = 0 this is easy. So assume b > 0 and divide by b. Taking t = a/b we must show

$$(4.12) t^{\gamma} < \gamma t + 1 - \gamma, \ 0 < t, \ 0 < \gamma < 1.$$

The function  $f(t) = t^{\gamma} - \gamma t$  is differentiable for t > 0 with derivative  $\gamma t^{\gamma-1} - \gamma$ , which is positive for t < 1 and negative for t > 1. Thus  $f(t) \leq f(1)$  with equality only for t = 1. Since  $f(1) = 1 - \gamma$ , this is (4.12), proving the lemma.

We use this to prove Hölder's inequality

<sup>&</sup>lt;sup>6</sup>Check that  $|f|^p$  is automatically measurable.

**Lemma 4.8.** If f and g are measurable then

$$\left| \int fg d\mu \right| \le \|f\|_p \|g\|_q$$

for any  $1 , with <math>\frac{1}{p} + \frac{1}{q} = 1$ .

*Proof.* If  $||f||_p = 0$  or  $||g||_q = 0$  the result is trivial, as it is if either is infinite. Thus consider

$$a = \left| \frac{f(x)}{\|f\|_p} \right|^p, \ b = \left| \frac{g(x)}{\|g\|_q} \right|^q$$

and apply (4.11) with  $\gamma = \frac{1}{n}$ . This gives

$$\frac{|f(x)g(x)|}{\|f\|_p \|g\|_q} \le \frac{|f(x)|^p}{p\|f\|_p^p} + \frac{|g(x)|^q}{q\|g\|_q^q}.$$

Integrating over X we find

$$\frac{1}{\|f\|_p \|g\|_q} \int_X |f(x)g(x)| \ d\mu$$

$$\leq \frac{1}{p} + \frac{1}{q} = 1.$$

Since  $\left| \int_X fg \, d\mu \right| \leq \int_X |fg| \, d\mu$  this implies (4.13).

The final inequality we need is *Minkowski's* inequality.

**Proposition 4.9.** If  $1 and <math>f, g \in L^p(X, \mu)$  then

$$(4.14) ||f+g||_p \le ||f||_p + ||g||_p.$$

*Proof.* The case p=1 you have already done. It is also obvious if f+g=0 a.e.. If not we can write

$$|f+g|^p \le (|f|+|g|)|f+g|^{p-1}$$

and apply Hölder's inequality, to the right side, expanded out,

$$\int |f+g|^p \ d\mu \le (\|f\|_p + \|g\|_p) \ , \left(\int |f+g|^{q(p-1)} \ d\mu\right)^{1/q} \ .$$
 Since  $q(p-1)=p$  and  $1-\frac{1}{q}=1/p$  this is just (4.14).  $\square$ 

So, now we know that  $L^p(X, \mu)$  is a normed space for  $1 \leq p < \infty$ . In particular it is a metric space. One important additional property that a metric space may have is *completeness*, meaning that every Cauchy sequence is convergent.

**Definition 4.10.** A normed space in which the underlying metric space is complete is called a Banach space.

**Theorem 4.11.** For any measure space  $(X, M, \mu)$  the spaces  $L^p(X, \mu)$ ,  $1 \le p < \infty$ , are Banach spaces.

*Proof.* We need to show that a given Cauchy sequence  $\{f_n\}$  converges in  $L^p(X,\mu)$ . It suffices to show that it has a convergent subsequence. By the Cauchy property, for each  $k \exists n = n(k)$  s.t.

$$(4.15) ||f_n - f_\ell||_p \le 2^{-k} \ \forall \ \ell \ge n.$$

Consider the sequence

$$g_1 = f_1, g_k = f_{n(k)} - f_{n(k-1)}, k > 1.$$

By (4.15),  $||g_k||_p \leq 2^{-k}$ , for k > 1, so the series  $\sum_k ||g_k||_p$  converges, say to  $B < \infty$ . Now set

$$h_n(x) = \sum_{k=1}^n |g_k(x)|, n \ge 1, h(x) = \sum_{k=1}^\infty g_k(x).$$

Then by the monotone convergence theorem

$$\int_X h^p d\mu = \lim_{n \to \infty} \int_X |h_n|^p d\mu \le B^p,$$

where we have also used Minkowski's inequality. Thus  $h \in L^p(X, \mu)$ , so the series

$$f(x) = \sum_{k=1}^{\infty} g_k(x)$$

converges (absolutely) almost everywhere. Since

$$|f(x)|^p = \lim_{n \to \infty} \left| \sum_{k=1}^n g_k \right|^p \le h^p$$

with  $h^p \in L'(X, \mu)$ , the dominated convergence theorem applies and shows that  $f \in L^p(X, \mu)$ . Furthermore,

$$\sum_{k=1}^{\ell} g_k(x) = f_{n(\ell)}(x) \text{ and } |f(x) - f_{n(\ell)}(x)|^p \le (2h(x))^p$$

so again by the dominated convergence theorem,

$$\int_X |f(x) - f_{n(\ell)}(x)|^p \to 0.$$

Thus the subsequence  $f_{n(\ell)} \to f$  in  $L^p(X,\mu)$ , proving its completeness.

Next I want to return to our starting point and discuss the Riesz representation theorem. There are two important results in measure theory that I have not covered — I will get you to do most of them in the problems — namely the Hahn decomposition theorem and the Radon-Nikodym theorem. For the moment we can do without the latter, but I will use the former.

So, consider a locally compact metric space, X. By a Borel measure on X, or a signed Borel measure, we shall mean a function on Borel sets

$$\mu: \mathcal{B}(X) \to \mathbb{R}$$

which is given as the difference of two finite positive Borel measures

(4.16) 
$$\mu(E) = \mu_1(E) - \mu_2(E).$$

Similarly we shall say that  $\mu$  is Radon, or a signed Radon measure, if it *can be written* as such a difference, with both  $\mu_1$  and  $\mu_2$  finite Radon measures. See the problems below for a discussion of this point.

Let  $M_{\text{fin}}(X)$  denote the set of finite Radon measures on X. This is a normed space with

(4.17) 
$$\|\mu\|_1 = \inf(\mu_1(X) + \mu_2(X))$$

with the infimum over all Radon decompositions (4.16). Each signed Radon measure defines a continuous linear functional on  $C_0(X)$ :

(4.18) 
$$\int \cdot d\mu : \mathcal{C}_0(X) \ni f \longmapsto \int_X f \cdot d\mu.$$

**Theorem 4.12** (Riesz representation.). If X is a locally compact metric space then every continuous linear functional on  $C_0(X)$  is given by a unique finite Radon measure on X through (4.18).

Thus the dual space of  $C_0(X)$  is  $M_{fin}(X)$  – at least this is how such a result is usually interpreted

$$(4.19) (C_0(X))' = M_{fin}(X),$$

see the remarks following the proof.

*Proof.* We have done half of this already. Let me remind you of the steps.

We started with  $u \in (\mathcal{C}_0(X))'$  and showed that  $u = u_+ - u_-$  where  $u_{\pm}$  are positive continuous linear functionals; this is Lemma 1.5. Then we showed that  $u \geq 0$  defines a finite positive Radon measure  $\mu$ . Here  $\mu$  is defined by (1.11) on open sets and  $\mu(E) = \mu^*(E)$  is given by (1.12)

on general Borel sets. It is finite because

(4.20) 
$$\mu(X) = \sup \{ u(f) ; 0 \le f \le 1, \text{ supp } f \in X, f \in C(X) \}$$
  
  $\le ||u||.$ 

From Proposition 2.8 we conclude that  $\mu$  is a Radon measure. Since this argument applies to  $u_{\pm}$  we get two positive finite Radon measures  $\mu_{\pm}$  and hence a signed Radon measure

$$(4.21) \mu = \mu_{+} - \mu_{-} \in M_{\text{fin}}(X).$$

In the problems you are supposed to prove the Hahn decomposition theorem, in particular in Problem 14 I ask you to show that (4.21) is the Hahn decomposition of  $\mu$  — this means that there is a Borel set  $E \subset X$  such that  $\mu_{-}(E) = 0$ ,  $\mu_{+}(X \setminus E) = 0$ .

What we have defined is a linear map

$$(4.22) (\mathcal{C}_0(X))' \to M(X), \ u \longmapsto \mu.$$

We want to show that this is an isomorphism, i.e., it is 1-1 and onto. We first show that it is 1-1. That is, suppose  $\mu=0$ . Given the uniqueness of the Hahn decomposition this implies that  $\mu_+=\mu_-=0$ . So we can suppose that  $u \geq 0$  and  $\mu=\mu_+=0$  and we have to show that u=0; this is obvious since

(4.23) 
$$\mu(X) = \sup \{ u(f); \text{ supp } u \in X, \ 0 \le f \le 1 \ f \in C(X) \} = 0$$
$$\Rightarrow u(f) = 0 \text{ for all such } f.$$

If  $0 \le f \in C(X)$  and supp  $f \in X$  then  $f' = f/\|f\|_{\infty}$  is of this type so u(f) = 0 for every  $0 \le f \in C(X)$  of compact support. From the decomposition of continuous functions into positive and negative parts it follows that u(f) = 0 for every f of compact support. Now, if  $f \in \mathcal{C}_o(X)$ , then given  $n \in \mathbb{N}$  there exists  $K \in X$  such that |f| < 1/n on  $X \setminus K$ . As you showed in the problems, there exists  $\chi \in \mathcal{C}(X)$  with supp $(\chi) \in X$  and  $\chi = 1$  on K. Thus if  $f_n = \chi f$  then supp $(f_n) \in X$  and  $\|f - f_n\| = \sup(|f - f_n| < 1/n$ . This shows that  $\mathcal{C}_0(X)$  is the closure of the subspace of continuous functions of compact support so by the assumed continuity of u, u = 0.

So it remains to show that *every* finite Radon measure on X arises from (4.22). We do this by starting from  $\mu$  and constructing u. Again we use the Hahn decomposition of  $\mu$ , as in  $(4.21)^7$ . Thus we assume  $\mu \geq 0$  and construct u. It is obvious what we want, namely

(4.24) 
$$u(f) = \int_{X} f \, d\mu \,, \ f \in \mathcal{C}_{c}(X) \,.$$

<sup>&</sup>lt;sup>7</sup>Actually we can just take any decomposition (4.21) into a difference of positive Radon measures.

Here we need to recall from Proposition 3.2 that continuous functions on X, a locally compact metric space, are (Borel) measurable. Furthermore, we know that there is an increasing sequence of simple functions with limit f, so

$$\left| \int_{X} f \, d\mu \right| \le \mu(X) \cdot \|f\|_{\infty} \,.$$

This shows that u in (4.24) is continuous and that its norm  $||u|| \le \mu(X)$ . In fact

$$(4.26) ||u|| = \mu(X).$$

Indeed, the inner regularity of  $\mu$  implies that there is a compact set  $K \subseteq X$  with  $\mu(K) \ge \mu(X) - \frac{1}{n}$ ; then there is  $f \in \mathcal{C}_c(X)$  with  $0 \le f \le 1$  and f = 1 on K. It follows that  $\mu(f) \ge \mu(K) \ge \mu(X) - \frac{1}{n}$ , for any n. This proves (4.26).

We still have to show that if u is defined by (4.24), with  $\mu$  a finite positive Radon measure, then the measure  $\tilde{\mu}$  defined from u via (4.24) is precisely  $\mu$  itself.

This is easy provided we keep things clear. Starting from  $\mu \geq 0$  a finite Radon measure, define u by (4.24) and, for  $U \subset X$  open

$$(4.27) \quad \tilde{\mu}(U) = \sup \left\{ \int_X f d\mu, \ 0 \le f \le 1, \ f \in C(X), \ \operatorname{supp}(f) \in U \right\}.$$

By the properties of the integral,  $\tilde{\mu}(U) \leq \mu(U)$ . Conversely if  $K \in U$  there exists an element  $f \in \mathcal{C}_c(X)$ ,  $0 \leq f \leq 1$ , f = 1 on K and  $\operatorname{supp}(f) \subset U$ . Then we know that

(4.28) 
$$\tilde{\mu}(U) \ge \int_{X} f d\mu \ge \mu(K).$$

By the inner regularity of  $\mu$ , we can choose  $K \subseteq U$  such that  $\mu(K) \ge \mu(U) - \epsilon$ , given  $\epsilon > 0$ . Thus  $\tilde{\mu}(U) = \mu(U)$ .

This proves the Riesz representation theorem, modulo the decomposition of the measure - which I will do in class if the demand is there! In my view this is quite enough measure theory.  $\Box$ 

Notice that we have in fact proved something stronger than the statement of the theorem. Namely we have shown that under the correspondence  $u \longleftrightarrow \mu$ ,

$$||u|| = |\mu|(X) =: ||\mu||_1.$$

Thus the map is an *isometry*.

# 5. Hilbert space

We have shown that  $L^p(X, \mu)$  is a Banach space – a complete normed space. I shall next discuss the class of Hilbert spaces, a special class of Banach spaces, of which  $L^2(X, \mu)$  is a standard example, in which the norm arises from an inner product, just as it does in Euclidean space.

An inner product on a vector space V over  $\mathbb{C}$  (one can do the real case too, not much changes) is a *sesquilinear* form

$$V \times V \to \mathbb{C}$$

written (u, v), if  $u, v \in V$ . The 'sesqui-' part is just linearity in the first variable

$$(5.1) (a_1u_1 + a_2u_2, v) = a_1(u_1, v) + a_2(u_2, v),$$

anti-linearly in the second

$$(5.2) (u, a_1v_1 + a_2v_2) = \overline{a}_1(u, v_1) + \overline{a}_2(u, v_2)$$

and the conjugacy condition

$$(5.3) (u,v) = \overline{(v,u)}.$$

Notice that (5.2) follows from (5.1) and (5.3). If we assume in addition the positivity condition<sup>8</sup>

$$(5.4)$$
  $(u, u) > 0, (u, u) = 0 \Rightarrow u = 0,$ 

then

$$||u|| = (u, u)^{1/2}$$

is a norm on V, as we shall see.

Suppose that  $u, v \in V$  have ||u|| = ||v|| = 1. Then  $(u, v) = e^{i\theta} |(u, v)|$  for some  $\theta \in \mathbb{R}$ . By choice of  $\theta$ ,  $e^{-i\theta}(u, v) = |(u, v)|$  is real, so expanding out using linearity for  $s \in \mathbb{R}$ ,

$$0 \le (e^{-i\theta}u - sv, e^{-i\theta}u - sv)$$
  
=  $||u||^2 - 2s \operatorname{Re} e^{-i\theta}(u, v) + s^2||v||^2 = 1 - 2s|(u, v)| + s^2.$ 

The minimum of this occurs when s = |(u, v)| and this is negative unless  $|(u, v)| \le 1$ . Using linearity, and checking the trivial cases u = or v = 0 shows that

$$(5.6) |(u,v)| \le ||u|| \, ||v||, \, \forall \, u,v \in V.$$

This is called Schwarz' inequality.

<sup>&</sup>lt;sup>8</sup>Notice that (u, u) is real by (5.3).

<sup>&</sup>lt;sup>9</sup>No 't' in this Schwarz.

Using Schwarz' inequality

$$||u + v||^2 = ||u||^2 + (u, v) + (v, u) + ||v||^2$$

$$\leq (||u|| + ||v||)^2$$

$$\implies ||u + v|| \leq ||u|| + ||v|| \, \forall \, u, v \in V$$

which is the triangle inequality.

**Definition 5.1.** A Hilbert space is a vector space V with an inner product satisfying (5.1) - (5.4) which is complete as a normed space (i.e., is a Banach space).

Thus we have already shown  $L^2(X,\mu)$  to be a Hilbert space for any positive measure  $\mu$ . The inner product is

(5.7) 
$$(f,g) = \int_X f\overline{g} \,d\mu \,,$$

since then (5.3) gives  $||f||_2$ .

Another important identity valid in any inner product spaces is the parallelogram law:

$$(5.8) ||u+v||^2 + ||u-v||^2 = 2||u||^2 + 2||v||^2.$$

This can be used to prove the basic 'existence theorem' in Hilbert space theory.

**Lemma 5.2.** Let  $C \subset H$ , in a Hilbert space, be closed and convex (i.e.,  $su + (1 - s)v \in C$  if  $u, v \in C$  and 0 < s < 1). Then C contains a unique element of smallest norm.

*Proof.* We can certainly choose a sequence  $u_n \in C$  such that

$$||u_n|| \to \delta = \inf\{||v||; v \in C\}$$
.

By the parallelogram law.

$$||u_n - u_m||^2 = 2||u_n||^2 + 2||u_m||^2 - ||u_n + u_m||^2$$
  

$$\leq 2(||u_n||^2 + ||u_m||^2) - 4\delta^2$$

where we use the fact that  $(u_n + u_m)/2 \in C$  so must have norm at least  $\delta$ . Thus  $\{u_n\}$  is a Cauchy sequence, hence convergent by the assumed completeness of H. Thus  $\lim u_n = u \in C$  (since it is assumed closed) and by the triangle inequality

$$|||u_n|| - ||u||| \le ||u_n - u|| \to 0$$

So  $||u|| = \delta$ . Uniqueness of u follows again from the parallelogram law which shows that if  $||u'|| = \delta$  then

$$||u - u'|| \le 2\delta^2 - 4||(u + u')/2||^2 \le 0$$
.

The fundamental fact about a Hilbert space is that each element  $v \in H$  defines a continuous linear functional by

$$H \ni u \longmapsto (u, v) \in \mathbb{C}$$

and conversely *every* continuous linear functional arises this way. This is also called the Riesz representation theorem.

**Proposition 5.3.** If  $L: H \to \mathbb{C}$  is a continuous linear functional on a Hilbert space then this is a unique element  $v \in H$  such that

$$(5.9) Lu = (u, v) \ \forall \ u \in H,$$

*Proof.* Consider the linear space

$$M = \{ u \in H : Lu = 0 \}$$

the null space of L, a continuous linear functional on H. By the assumed continuity, M is closed. We can suppose that L is *not* identically zero (since then v = 0 in (5.9)). Thus there exists  $w \notin M$ . Consider

$$w + M = \{v \in H : v = w + u, u \in M\}$$
.

This is a closed convex subset of H. Applying Lemma 5.2 it has a unique smallest element,  $v \in w + M$ . Since v minimizes the norm on w + M,

$$||v + su||^2 = ||v||^2 + 2\operatorname{Re}(su, v) + ||s||^2 ||u||^2$$

is stationary at s = 0. Thus  $Re(u, v) = 0 \ \forall \ u \in M$ , and the same argument with s replaced by is shows that  $(v, u) = 0 \ \forall \ u \in M$ .

Now  $v \in w + M$ , so  $Lv = Lw \neq 0$ . Consider the element  $w' = w/Lw \in H$ . Since Lw' = 1, for any  $u \in H$ 

$$L(u - (Lu)w') = Lu - Lu = 0.$$

It follows that  $u - (Lu)w' \in M$  so if  $w'' = w' / ||w'||^2$ 

$$(u, w'') = ((Lu)w', w'') = Lu \frac{(w', w')}{\|w'\|^2} = Lu.$$

The uniqueness of v follows from the positivity of the norm.  $\square$ 

Corollary 5.4. For any positive measure  $\mu$ , any continuous linear functional

$$L:L^2(X,\mu)\to\mathbb{C}$$

is of the form

$$Lf = \int_X f\overline{g} \, d\mu \,, \ g \in L^2(X,\mu) \,.$$

Notice the apparent power of 'abstract reasoning' here! Although we seem to have constructed g out of nowhere, its existence follows from the *completeness* of  $L^2(X,\mu)$ , but it is very convenient to express the argument abstractly for a general Hilbert space.

### 6. Test functions

So far we have largely been dealing with integration. One thing we have seen is that, by considering dual spaces, we can think of functions as functionals. Let me briefly review this idea.

Consider the unit ball in  $\mathbb{R}^n$ ,

$$\overline{\mathbb{B}}^n = \{ x \in \mathbb{R}^n \, ; \, |x| \le 1 \} \ .$$

I take the *closed* unit ball because I want to deal with a compact metric space. We have dealt with several Banach spaces of functions on  $\overline{\mathbb{B}^n}$ , for example

$$C(\overline{\mathbb{B}^n}) = \left\{ u : \overline{\mathbb{B}^n} \to \mathbb{C} \; ; \; u \text{ continuous} \right\}$$
$$L^2(\overline{\mathbb{B}^n}) = \left\{ u : \overline{\mathbb{B}^n} \to \mathbb{C} ; \text{Borel measurable with } \int |u|^2 \; dx < \infty \right\}.$$

Here, as always below, dx is Lebesgue measure and functions are identified if they are equal almost everywhere.

Since  $\overline{\mathbb{B}^n}$  is compact we have a natural inclusion

(6.1) 
$$C(\overline{\mathbb{B}^n}) \hookrightarrow L^2(\overline{\mathbb{B}^n})$$
.

This is also a topological inclusion, i.e., is a bounded linear map, since

$$(6.2) ||u||_{L^2} \le C||u||_{\infty}$$

where  $C^2$  is the volume of the unit ball.

In general if we have such a set up then

**Lemma 6.1.** If  $V \hookrightarrow U$  is a subspace with a stronger norm,

$$\|\varphi\|_U \le C\|\varphi\|_V \ \forall \ \varphi \in V$$

then restriction gives a continuous linear map

(6.3) 
$$U' \to V', \ U' \ni L \longmapsto \tilde{L} = L|_{V} \in V', \ \|\tilde{L}\|_{V'} \le C\|L\|_{U'}.$$

If V is dense in U then the map (6.3) is injective.

*Proof.* By definition of the dual norm

$$\|\tilde{L}\|_{V'} = \sup \left\{ \left| \tilde{L}(v) \right| \; ; \; \|v\|_{V} \le 1 \; , \; v \in V \right\}$$

$$\le \sup \left\{ \left| \tilde{L}(v) \right| \; ; \; \|v\|_{U} \le C \; , \; v \in V \right\}$$

$$\le \sup \left\{ |L(u)| \; ; \; \|u\|_{U} \le C \; , \; u \in U \right\}$$

$$= C\|L\|_{U'} \; .$$

If  $V \subset U$  is dense then the vanishing of  $L: U \to \mathbb{C}$  on V implies its vanishing on U.

Going back to the particular case (6.1) we do indeed get a continuous map between the dual spaces

$$L^2(\overline{\mathbb{B}^n}) \cong (L^2(\overline{\mathbb{B}^n}))' \to (C(\overline{\mathbb{B}^n}))' = M(\overline{\mathbb{B}^n}).$$

Here we use the Riesz representation theorem and duality for Hilbert spaces. The map use here is supposed to be *linear* not antilinear, i.e.,

(6.4) 
$$L^{2}(\overline{\mathbb{B}^{n}}) \ni g \longmapsto \int g \, dx \in (C(\overline{\mathbb{B}^{n}}))'.$$

So the idea is to make the space of 'test functions' as small as reasonably possible, while still retaining *density* in reasonable spaces.

Recall that a function  $u: \mathbb{R}^n \to \mathbb{C}$  is differentiable at  $\overline{x} \in \mathbb{R}^n$  if there exists  $a \in \mathbb{C}^n$  such that

$$(6.5) |u(x) - u(\overline{x}) - a \cdot (x - \overline{x})| = o(|x - \overline{x}|).$$

The 'little oh' notation here means that given  $\epsilon > 0$  there exists  $\delta > 0$  s.t.

$$|x - \overline{x}| < \delta \Rightarrow |u(x) - u(\overline{x}) - a(x - \overline{x})| < \epsilon |x - \overline{x}|$$
.

The coefficients of  $a = (a_1, \ldots, a_n)$  are the partial derivations of u at  $\overline{x}$ .

$$a_i = \frac{\partial u}{\partial x_i}(\overline{x})$$

since

(6.6) 
$$a_i = \lim_{t \to 0} \frac{u(\overline{x} + te_i) - u(\overline{x})}{t},$$

 $e_i = (0, ..., 1, 0, ..., 0)$  being the *i*th basis vector. The function u is said to be *continuously differentiable* on  $\mathbb{R}^n$  if it is differentiable at *each* point  $\overline{x} \in \mathbb{R}^n$  and each of the n partial derivatives are continuous,

(6.7) 
$$\frac{\partial u}{\partial x_j} : \mathbb{R}^n \to \mathbb{C}.$$

**Definition 6.2.** Let  $C_0^1(\mathbb{R}^n)$  be the subspace of  $C_0(\mathbb{R}^n) = C_0^0(\mathbb{R}^n)$  such that each element  $u \in C_0^1(\mathbb{R}^n)$  is continuously differentiable and  $\frac{\partial u}{\partial x_j} \in C_0(\mathbb{R}^n)$ ,  $j = 1, \ldots, n$ .

Proposition 6.3. The function

$$||u||_{\mathcal{C}^1} = ||u||_{\infty} + \sum_{i=1}^n ||\frac{\partial u}{\partial x_1}||_{\infty}$$

is a norm on  $C_0^1(\mathbb{R}^n)$  with respect to which it is a Banach space.

*Proof.* That  $\| \|_{\mathcal{C}^1}$  is a norm follows from the properties of  $\| \|_{\infty}$ . Namely  $\| u \|_{\mathcal{C}^1} = 0$  certainly implies u = 0,  $\| au \|_{\mathcal{C}^1} = |a| \| u \|_{\mathcal{C}^1}$  and the triangle inequality follows from the same inequality for  $\| \|_{\infty}$ .

Similarly, the main part of the completeness of  $C_0^1(\mathbb{R}^n)$  follows from the completeness of  $C_0^0(\mathbb{R}^n)$ . If  $\{u_n\}$  is a Cauchy sequence in  $C_0^1(\mathbb{R}^n)$  then  $u_n$  and the  $\frac{\partial u_n}{\partial x_j}$  are Cauchy in  $C_0^0(\mathbb{R}^n)$ . It follows that there are limits of these sequences,

$$u_n \to v$$
,  $\frac{\partial u_n}{\partial x_i} \to v_j \in \mathcal{C}_0^0(\mathbb{R}^n)$ .

However we do have to check that v is continuously differentiable and that  $\frac{\partial v}{\partial x_j} = v_j$ .

One way to do this is to use the Fundamental Theorem of Calculus in each variable. Thus

$$u_n(\overline{x} + te_i) = \int_0^t \frac{\partial u_n}{\partial x_i}(\overline{x} + se_i) \, ds + u_n(\overline{x}) \, .$$

As  $n \to \infty$  all terms converge and so, by the continuity of the integral,

$$u(\overline{x} + te_i) = \int_0^t v_j(\overline{x} + se_i) ds + u(\overline{x}).$$

This shows that the limit in (6.6) exists, so  $v_i(\overline{x})$  is the partial derivation of u with respect to  $x_i$ . It remains only to show that u is indeed differentiable at each point and I leave this to you in Problem 17.

So, almost by definition, we have an example of Lemma 6.1,

$$C_0^1(\mathbb{R}^n) \hookrightarrow C_0^0(\mathbb{R}^n).$$

It is in fact dense but I will not bother showing this (yet). So we know that

$$(\mathcal{C}_0^0(\mathbb{R}^n))' \to (\mathcal{C}_0^1(\mathbb{R}^n))'$$

and we expect it to be injective. Thus there are *more* functionals on  $\mathcal{C}_0^1(\mathbb{R}^n)$  including things that are 'more singular than measures'.

An example is related to the Dirac delta

$$\delta(\overline{x})(u) = u(\overline{x}), \ u \in \mathcal{C}_0^0(\mathbb{R}^n),$$

namely

$$C_0^1(\mathbb{R}^n) \ni u \longmapsto \frac{\partial u}{\partial x_i}(\overline{x}) \in \mathbb{C}.$$

This is clearly a continuous linear functional which it is only just to denote  $\frac{\partial}{\partial x_i}\delta(\overline{x})$ .

Of course, why stop at one derivative?

**Definition 6.4.** The space  $C_0^k(\mathbb{R}^n) \subset C_0^1(\mathbb{R}^n)$   $k \geq 1$  is defined inductively by requiring that

$$\frac{\partial u}{\partial x_j} \in \mathcal{C}_0^{k-1}(\mathbb{R}^n), \ j = 1, \dots, n.$$

The norm on  $C_0^k(\mathbb{R}^n)$  is taken to be

(6.8) 
$$||u||_{\mathcal{C}^k} = ||u||_{\mathcal{C}^{k-1}} + \sum_{j=1}^n ||\frac{\partial u}{\partial x_j}||_{\mathcal{C}^{k-1}}.$$

These are all Banach spaces, since if  $\{u_n\}$  is Cauchy in  $\mathcal{C}_0^k(\mathbb{R}^n)$ , it is Cauchy and hence convergent in  $\mathcal{C}_0^{k-1}(\mathbb{R}^n)$ , as is  $\partial u_n/\partial x_j$ ,  $j=1,\ldots,n-1$ . Furthermore the limits of the  $\partial u_n/\partial x_j$  are the derivatives of the limits by Proposition 6.3.

This gives us a sequence of spaces getting 'smoother and smoother'

$$C_0^0(\mathbb{R}^n) \supset C_0^1(\mathbb{R}^n) \supset \cdots \supset C_0^k(\mathbb{R}^n) \supset \cdots$$

with norms getting larger and larger. The duals can also be expected to get larger and larger as k increases.

As well as looking at functions getting smoother and smoother, we need to think about 'infinity', since  $\mathbb{R}^n$  is not compact. Observe that an element  $g \in L^1(\mathbb{R}^n)$  (with respect to Lebesgue measure by default) defines a functional on  $C_0^0(\mathbb{R}^n)$  — and hence all the  $C_0^k(\mathbb{R}^n)$ s. However a function such as the constant function 1 is not integrable on  $\mathbb{R}^n$ . Since we certainly want to talk about this, and polynomials, we consider a second condition of smallness at infinity. Let us set

(6.9) 
$$\langle x \rangle = (1 + |x|^2)^{1/2}$$

a function which is the size of |x| for |x| large, but has the virtue of being smooth<sup>10</sup>

**Definition 6.5.** For any 
$$k, l \in \mathbb{N} = \{1, 2, \dots\}$$
 set

$$\langle x \rangle^{-l} \mathcal{C}_0^k(\mathbb{R}^n) = \left\{ u \in \mathcal{C}_0^k(\mathbb{R}^n) ; u = \langle x \rangle^{-l} v, \ v \in \mathcal{C}_0^k(\mathbb{R}^n) \right\},$$
with norm,  $\|u\|_{k,l} = \|v\|_{\mathcal{C}_0^k}, \ v = \langle x \rangle^l u.$ 

Notice that the lack time is at a small at

Notice that the definition just says that  $u = \langle x \rangle^{-l} v$ , with  $v \in \mathcal{C}_0^k(\mathbb{R}^n)$ . It follows immediately that  $\langle x \rangle^{-l} \mathcal{C}_0^k(\mathbb{R}^n)$  is a Banach space with this norm.

**Definition 6.6.** Schwartz' space<sup>11</sup> of test functions on  $\mathbb{R}^n$  is

$$\mathcal{S}(\mathbb{R}^n) = \left\{ u : \mathbb{R}^n \to \mathbb{C}; u \in \langle x \rangle^{-l} \mathcal{C}_0^k(\mathbb{R}^n) \text{ for all } k \text{ and } l \in \mathbb{N} \right\}.$$

<sup>&</sup>lt;sup>10</sup>See Problem 18.

<sup>&</sup>lt;sup>11</sup>Laurent Schwartz – this one with a 't'.

It is not immediately apparent that this space is non-empty (well 0 is in there but...); that

$$\exp(-|x|^2) \in \mathcal{S}(\mathbb{R}^n)$$

is Problem 19. There are lots of other functions in there as we shall see.

Schwartz' idea is that the dual of  $\mathcal{S}(\mathbb{R}^n)$  should contain all the 'interesting' objects, at least those of 'polynomial growth'. The problem is that we do *not* have a good norm on  $\mathcal{S}(\mathbb{R}^n)$ . Rather we have a *lot* of them. Observe that

$$\langle x \rangle^{-l} \mathcal{C}_0^k(\mathbb{R}^n) \subset \langle x \rangle^{-l'} \mathcal{C}_0^{k'}(\mathbb{R}^n) \text{ if } l \geq l' \text{ and } k \geq k'.$$

Thus we see that as a linear space

(6.10) 
$$\mathcal{S}(\mathbb{R}^n) = \bigcap_k \langle x \rangle^{-k} \mathcal{C}_0^k(\mathbb{R}^n).$$

Since these spaces are getting smaller, we have a countably infinite number of norms. For this reason  $\mathcal{S}(\mathbb{R}^n)$  is called a *countably normed* space.

Proposition 6.7. For  $u \in \mathcal{S}(\mathbb{R}^n)$ , set

(6.11) 
$$||u||_{(k)} = ||\langle x \rangle^k u||_{\mathcal{C}^k}$$

and define

(6.12) 
$$d(u,v) = \sum_{k=0}^{\infty} 2^{-k} \frac{\|u - v\|_{(k)}}{1 + \|u - v\|_{(k)}},$$

then d is a distance function in  $\mathcal{S}(\mathbb{R}^n)$  with respect to which it is a complete metric space.

*Proof.* The series in (6.12) certainly converges, since

$$\frac{\|u - v\|_{(k)}}{1 + \|u - v\|_{(k)}} \le 1.$$

The first two conditions on a metric are clear,

$$d(u,v) = 0 \Rightarrow ||u - v||_{\mathcal{C}_0} = 0 \Rightarrow u = v,$$

and symmetry is immediate. The triangle inequality is perhaps more mysterious!

Certainly it is enough to show that

(6.13) 
$$\tilde{d}(u,v) = \frac{\|u - v\|}{1 + \|u - v\|}$$

is a metric on any normed space, since then we may sum over k. Thus we consider

$$\frac{\|u-v\|}{1+\|u-v\|} + \frac{\|v-w\|}{1+\|v-w\|}$$

$$= \frac{\|u-v\|(1+\|v-w\|)+\|v-w\|(1+\|u-v\|)}{(1+\|u-v\|)(1+\|v-w\|)}.$$

Comparing this to  $\tilde{d}(v, w)$  we must show that

$$(1 + ||u - v||)(1 + ||v - w||)||u - w||$$

$$< (||u - v||(1 + ||v - w||) + ||v - w||(1 + ||u - v||))(1 + ||u - w||).$$

Starting from the LHS and using the triangle inequality,

LHS 
$$\leq \|u - w\| + (\|u - v\| + \|v - w\| + \|u - v\| \|v - w\|) \|u - w\|$$
  
 $\leq (\|u - v\| + \|v - w\| + \|u - v\| \|v - w\|) (1 + \|u - w\|)$   
 $\leq \text{RHS}.$ 

Thus, d is a metric.

Suppose  $u_n$  is a Cauchy sequence. Thus,  $d(u_n, u_m) \to 0$  as  $n, m \to \infty$ . In particular, given

$$\epsilon > 0 \exists N \text{ s.t. } n, m > N \text{ implies}$$
  
$$d(u_n, u_m) < \epsilon 2^{-k} \forall n, m > N.$$

The terms in (6.12) are all positive, so this implies

$$\frac{\|u_n - u_m\|_{(k)}}{1 + \|u_n - u_m\|_{(k)}} < \epsilon \ \forall \ n, m > N.$$

If  $\epsilon < 1/2$  this in turn implies that

$$||u_n - u_m||_{(k)} < 2\epsilon$$

so the sequence is Cauchy in  $\langle x \rangle^{-k} \mathcal{C}_0^k(\mathbb{R}^n)$  for each k. From the completeness of these spaces it follows that  $u_n \to u$  in  $\langle x \rangle^{-k} \mathcal{C}_0^k(\mathbb{R}^n)_j$  for each k. Given  $\epsilon > 0$  choose k so large that  $2^{-k} < \epsilon/2$ . Then  $\exists N$  s.t. n > N

$$\Rightarrow ||u - u_n||_{(j)} < \epsilon/2 \ n > N, \ j \le k.$$

Hence

$$d(u_n, u) = \sum_{j \le k} 2^{-j} \frac{\|u - u_n\|_{(j)}}{1 + \|u - u_n\|_{(j)}}$$
$$+ \sum_{j > k} 2^{-j} \frac{\|u - u_n\|_{(j)}}{1 + \|u - u_n\|_{(j)}}$$
$$\le \epsilon/4 + 2^{-k} < \epsilon.$$

This 
$$u_n \to u$$
 in  $\mathcal{S}(\mathbb{R}^n)$ .

As well as the Schwartz space,  $\mathcal{S}(\mathbb{R}^n)$ , of functions of rapid decrease with all derivatives, there is a smaller 'standard' space of test functions, namely

(6.14) 
$$\mathcal{C}_{c}^{\infty}(\mathbb{R}^{n}) = \{ u \in \mathcal{S}(\mathbb{R}^{n}); \operatorname{supp}(u) \in \mathbb{R}^{n} \},$$

the space of smooth functions of compact support. Again, it is not quite obvious that this has any non-trivial elements, but it does as we shall see. If we fix a compact subset of  $\mathbb{R}^n$  and look at functions with support in that set, for instance the closed ball of radius R > 0, then we get a closed subspace of  $\mathcal{S}(\mathbb{R}^n)$ , hence a complete metric space. One 'problem' with  $\mathcal{C}_c^{\infty}(\mathbb{R}^n)$  is that it does not have a complete metric topology which restricts to this topology on the subsets. Rather we must use an *inductive limit* procedure to get a decent topology.

Just to show that this is not really hard, I will discuss it briefly here, but it is not used in the sequel. In particular I will not do this in the lectures themselves. By definition our space  $C_c^{\infty}(\mathbb{R}^n)$  (denoted traditionally as  $\mathcal{D}(\mathbb{R}^n)$ ) is a countable union of subspaces (6.15)

$$\dot{\mathcal{C}}_c^{\infty}(\mathbb{R}^n) = \bigcup_{n \in \mathbb{N}} \dot{\mathcal{C}}_c^{\infty}(B(n)), \ \dot{\mathcal{C}}_c^{\infty}(B(n)) = \{ u \in \mathcal{S}(\mathbb{R}^n); u = 0 \text{ in } |x| > n \}.$$

Consider

(6.16)

$$\mathcal{T} = \{ U \subset \mathcal{C}_c^{\infty}(\mathbb{R}^n); U \cap \dot{\mathcal{C}}_c^{\infty}(B(n)) \text{ is open in } \dot{\mathcal{C}}^{\infty}(B(n)) \text{ for each } n \}.$$

This is a topology on  $C_c^{\infty}(\mathbb{R}^n)$  – contains the empty set and the whole space and is closed under finite intersections and arbitrary unions – simply because the same is true for the open sets in  $\dot{C}^{\infty}(B(n))$  for each n. This is in fact the inductive limit topology. One obvious question is:- what does it mean for a linear functional  $u: C_c^{\infty}(\mathbb{R}^n) \longrightarrow \mathbb{C}$  to be continuous? This just means that  $u^{-1}(O)$  is open for each open set in  $\mathbb{C}$ . Directly from the definition this in turn means that  $u^{-1}(O) \cap \dot{C}^{\infty}(B(n))$ 

should be open in  $\dot{\mathcal{C}}^{\infty}(B(n))$  for each n. This however just means that, restricted to each of these subspaces u is continuous. If you now go forwards to Lemma 7.3 you can see what this means; see Problem 74.

Of course there is a lot more to be said about these spaces; you can find plenty of it in the references.

### 7. Tempered distributions

A good first reference for distributions is [2], [4] gives a more exhaustive treatment.

The complete metric topology on  $\mathcal{S}(\mathbb{R}^n)$  is described above. Next I want to try to convice you that elements of its dual space  $\mathcal{S}'(\mathbb{R}^n)$ , have enough of the properties of functions that we can work with them as 'generalized functions'.

First let me develop some notation. A differentiable function  $\varphi: \mathbb{R}^n \to \mathbb{C}$  has partial derivatives which we have denoted  $\partial \varphi/\partial x_j: \mathbb{R}^n \to \mathbb{C}$ . For reasons that will become clear later, we put a  $\sqrt{-1}$  into the definition and write

(7.1) 
$$D_j \varphi = \frac{1}{i} \frac{\partial \varphi}{\partial x_j}.$$

We say  $\varphi$  is once continuously differentiable if each of these  $D_j\varphi$  is continuous. Then we defined k times continuous differentiability inductively by saying that  $\varphi$  and the  $D_j\varphi$  are (k-1)-times continuously differentiable. For k=2 this means that

$$D_j D_k \varphi$$
 are continuous for  $j, k = 1, \dots, n$ .

Now, recall that, if continuous, these second derivatives are symmetric:

$$(7.2) D_i D_k \varphi = D_k D_i \varphi .$$

This means we can use a compact notation for higher derivatives. Put  $\mathbb{N}_0 = \{0, 1, \ldots\}$ ; we call an element  $\alpha \in \mathbb{N}_0^n$  a 'multi-index' and if  $\varphi$  is at least k times continuously differentiable, we set<sup>12</sup>

(7.3) 
$$D^{\alpha}\varphi = \frac{1}{i^{|\alpha|}} \frac{\partial^{\alpha_1}}{\partial x_1} \cdots \frac{\partial^{\alpha_n}}{\partial x_n} \varphi$$
 whenever  $|\alpha| = \alpha_1 + \alpha_2 + \cdots + \alpha_n \le k$ .

Now we have defined the spaces.

(7.4) 
$$\mathcal{C}_0^k(\mathbb{R}^n) = \left\{ \varphi : \mathbb{R}^n \to \mathbb{C} ; D^{\alpha} \varphi \in \mathcal{C}_0^0(\mathbb{R}^n) \ \forall \ |\alpha| \le k \right\}.$$

Notice the convention is that  $D^{\alpha}\varphi$  is asserted to exist if it is required to be continuous! Using  $\langle x \rangle = (1 + |x|^2)$  we defined

(7.5) 
$$\langle x \rangle^{-k} \mathcal{C}_0^k(\mathbb{R}^n) = \left\{ \varphi : \mathbb{R}^n \to \mathbb{C} \; ; \; \langle x \rangle^k \varphi \in \mathcal{C}_0^k(\mathbb{R}^n) \right\} \; ,$$

and then our space of test functions is

$$\mathcal{S}(\mathbb{R}^n) = \bigcap_{k} \langle x \rangle^{-k} \mathcal{C}_0^k(\mathbb{R}^n) \,.$$

 $<sup>^{12}</sup>$  Periodically there is the possibility of confusion between the two meanings of  $|\alpha|$  but it seldom arises.

Thus,

(7.6) 
$$\varphi \in \mathcal{S}(\mathbb{R}^n) \Leftrightarrow D^{\alpha}(\langle x \rangle^k \varphi) \in \mathcal{C}_0^0(\mathbb{R}^n) \ \forall \ |\alpha| \le k \text{ and all } k.$$

**Lemma 7.1.** The condition  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  can be written

$$\langle x \rangle^k D^\alpha \varphi \in \mathcal{C}_0^0(\mathbb{R}^n) \ \forall \ |\alpha| \le k, \ \forall \ k.$$

*Proof.* We first check that

$$\varphi \in \mathcal{C}_0^0(\mathbb{R}^n), \ D_j(\langle x \rangle \varphi) \in \mathcal{C}_0^0(\mathbb{R}^n), \ j = 1, \cdots, n$$
  
$$\Leftrightarrow \varphi \in \mathcal{C}_0^0(\mathbb{R}^n), \ \langle x \rangle D_j \varphi \in \mathcal{C}_0^0(\mathbb{R}^n), \ j = 1, \cdots, n.$$

Since

$$D_i \langle x \rangle \varphi = \langle x \rangle D_i \varphi + (D_i \langle x \rangle) \varphi$$

and  $D_j\langle x\rangle = \frac{1}{i}x_j\langle x\rangle^{-1}$  is a bounded continuous function, this is clear. Then consider the same thing for a larger k:

(7.7) 
$$D^{\alpha} \langle x \rangle^{p} \varphi \in \mathcal{C}_{0}^{0}(\mathbb{R}^{n}) \ \forall \ |\alpha| = p, \ 0 \leq p \leq k$$
$$\Leftrightarrow \langle x \rangle^{p} D^{\alpha} \varphi \in \mathcal{C}_{0}^{0}(\mathbb{R}^{n}) \ \forall \ |\alpha| = p, \ 0 \leq p \leq k.$$

I leave you to check this as Problem 7.1.

Corollary 7.2. For any  $k \in \mathbb{N}$  the norms

$$\|\langle x \rangle^k \varphi\|_{\mathcal{C}^k}$$
 and  $\sum_{\substack{|\alpha| \leq k, \\ |\beta| \leq k}} \|x^{\alpha} D_x^{\beta} \varphi\|_{\infty}$ 

are equivalent.

*Proof.* Any reasonable proof of (7.2) shows that the norms

$$\|\langle x \rangle^k \varphi\|_{\mathcal{C}^k}$$
 and  $\sum_{|\beta| \le k} \|\langle x \rangle^k D^\beta \varphi\|_{\infty}$ 

are equivalent. Since there are positive constants such that

$$C_1\left(1+\sum_{|\alpha|\leq k}|x^{\alpha}|\right)\leq \langle x\rangle^k\leq C_2\left(1+\sum_{|\alpha|\leq k}|x^{\alpha}|\right)$$

the equivalent of the norms follows.

**Proposition 7.3.** A linear functional  $u : \mathcal{S}(\mathbb{R}^n) \to \mathbb{C}$  is continuous if and only if there exist C, k such that

$$|u(\varphi)| \le C \sum_{\substack{|\alpha| \le k, \\ |\beta| \le k}} \sup_{\mathbb{R}^n} |x^{\alpha} D_x^{\beta} \varphi|.$$

*Proof.* This is just the equivalence of the norms, since we showed that  $u \in \mathcal{S}'(\mathbb{R}^n)$  if and only if

$$|u(\varphi)| \le C ||\langle x \rangle^k \varphi||_{\mathcal{C}^k}$$

for some k.

### Lemma 7.4. A linear map

$$T: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n)$$

is continuous if and only if for each k there exist C and j such that if  $|\alpha| \le k$  and  $|\beta| \le k$ 

$$(7.8) \quad \sup \left| x^{\alpha} D^{\beta} T \varphi \right| \leq C \sum_{|\alpha'| \leq j, |\beta'| \leq j} \sup_{\mathbb{R}^n} \left| x^{\alpha'} D^{\beta'} \varphi \right| \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

*Proof.* This is Problem 7.2.

All this messing about with norms shows that

$$x_i: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n) \text{ and } D_i: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n)$$

are continuous.

So now we have some idea of what  $u \in \mathcal{S}'(\mathbb{R}^n)$  means. Let's notice that  $u \in \mathcal{S}'(\mathbb{R}^n)$  implies

$$(7.9) x_j u \in \mathcal{S}'(\mathbb{R}^n) \ \forall \ j = 1, \cdots, n$$

$$(7.10) D_j u \in \mathcal{S}'(\mathbb{R}^n) \ \forall \ j = 1, \cdots, n$$

(7.11) 
$$\varphi u \in \mathcal{S}'(\mathbb{R}^n) \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n)$$

where we have to *define* these things in a reasonable way. Remember that  $u \in \mathcal{S}'(\mathbb{R}^n)$  is "supposed" to be like an integral against a "generalized function"

(7.12) 
$$u(\psi) = \int_{\mathbb{R}^n} u(x)\psi(x) \, dx \, \forall \, \psi \in \mathcal{S}(\mathbb{R}^n).$$

Since it would be true if u were a function we define

(7.13) 
$$x_j u(\psi) = u(x_j \psi) \ \forall \ \psi \in \mathcal{S}(\mathbb{R}^n).$$

Then we check that  $x_i u \in \mathcal{S}'(\mathbb{R}^n)$ :

$$|x_{j}u(\psi)| = |u(x_{j}\psi)|$$

$$\leq C \sum_{|\alpha| \leq k, |\beta| \leq k} \sup_{\mathbb{R}^{n}} |x^{\alpha}D^{\beta}(x_{j}\psi)|$$

$$\leq C' \sum_{|\alpha| \leq k+1, |\beta| \leq k} \sup_{\mathbb{R}^n} |x^{\alpha} D^{\beta} \psi|.$$

Similarly we can define the partial *derivatives* by using the standard integration by parts formula

(7.14) 
$$\int_{\mathbb{R}^n} (D_j u)(x) \varphi(x) dx = -\int_{\mathbb{R}^n} u(x) (D_j \varphi(x)) dx$$

if  $u \in \mathcal{C}_0^1(\mathbb{R}^n)$ . Thus if  $u \in \mathcal{S}'(\mathbb{R}^n)$  again we define

$$D_j u(\psi) = -u(D_j \psi) \ \forall \ \psi \in \mathcal{S}(\mathbb{R}^n).$$

Then it is clear that  $D_i u \in \mathcal{S}'(\mathbb{R}^n)$ .

Iterating these definition we find that  $D^{\alpha}$ , for any multi-index  $\alpha$ , defines a linear map

$$(7.15) D^{\alpha}: \mathcal{S}'(\mathbb{R}^n) \to \mathcal{S}'(\mathbb{R}^n).$$

In general a linear differential operator with constant coefficients is a sum of such "monomials". For example Laplace's operator is

$$\Delta = -\frac{\partial^2}{\partial x_1^2} - \frac{\partial^2}{\partial x_2^2} - \dots - \frac{\partial^2}{\partial x_n^2} = D_1^2 + D_2^2 + \dots + D_n^2.$$

We will be interested in trying to solve differential equations such as

$$\Delta u = f \in \mathcal{S}'(\mathbb{R}^n)$$
.

We can also multiply  $u \in \mathcal{S}'(\mathbb{R}^n)$  by  $\varphi \in \mathcal{S}(\mathbb{R}^n)$ , simply defining

(7.16) 
$$\varphi u(\psi) = u(\varphi \psi) \ \forall \ \psi \in \mathcal{S}(\mathbb{R}^n).$$

For this to make sense it suffices to check that

(7.17) 
$$\sum_{\substack{|\alpha| \le k, \\ |\beta| < k}} \sup_{\mathbb{R}^n} \left| x^{\alpha} D^{\beta}(\varphi \psi) \right| \le C \sum_{\substack{|\alpha| \le k, \\ |\beta| < k}} \sup_{\mathbb{R}^n} \left| x^{\alpha} D^{\beta} \psi \right|.$$

This follows easily from Leibniz' formula.

Now, to start thinking of  $u \in \mathcal{S}'(\mathbb{R}^n)$  as a generalized function we first define its *support*. Recall that

$$(7.18) \qquad \sup \{ (\psi) = \operatorname{clos} \{ x \in \mathbb{R}^n; \psi(x) \neq 0 \} .$$

We can write this in another 'weak' way which is easier to generalize. Namely

$$(7.19) p \notin \operatorname{supp}(u) \Leftrightarrow \exists \varphi \in \mathcal{S}(\mathbb{R}^n), \ \varphi(p) \neq 0, \ \varphi u = 0.$$

In fact this definition makes sense for any  $u \in \mathcal{S}'(\mathbb{R}^n)$ .

**Lemma 7.5.** The set supp(u) defined by (7.19) is a closed subset of  $\mathbb{R}^n$  and reduces to (7.18) if  $u \in \mathcal{S}(\mathbb{R}^n)$ .

*Proof.* The set defined by (7.19) is closed, since

(7.20) 
$$\operatorname{supp}(u)^{\complement} = \{ p \in \mathbb{R}^n; \ \exists \ \varphi \in \mathcal{S}(\mathbb{R}^n), \ \varphi(p) \neq 0, \ \varphi u = 0 \}$$

is clearly open — the same  $\varphi$  works for nearby points. If  $\psi \in \mathcal{S}(\mathbb{R}^n)$  we define  $u_{\psi} \in \mathcal{S}'(\mathbb{R}^n)$ , which we will again identify with  $\psi$ , by

(7.21) 
$$u_{\psi}(\varphi) = \int \varphi(x)\psi(x) dx.$$

Obviously  $u_{\psi} = 0 \Longrightarrow \psi = 0$ , simply set  $\varphi = \overline{\psi}$  in (7.21). Thus the map

(7.22) 
$$\mathcal{S}(\mathbb{R}^n) \ni \psi \longmapsto u_{\psi} \in \mathcal{S}'(\mathbb{R}^n)$$

is injective. We want to show that

$$(7.23) supp(u_{\psi}) = supp(\psi)$$

on the left given by (7.19) and on the right by (7.18). We show first that

$$\operatorname{supp}(u_{\psi}) \subset \operatorname{supp}(\psi).$$

Thus, we need to see that  $p \notin \operatorname{supp}(\psi) \Rightarrow p \notin \operatorname{supp}(u_{\psi})$ . The first condition is that  $\psi(x) = 0$  in a neighbourhood, U of p, hence there is a  $\mathcal{C}^{\infty}$  function  $\varphi$  with support in U and  $\varphi(p) \neq 0$ . Then  $\varphi\psi \equiv 0$ . Conversely suppose  $p \notin \operatorname{supp}(u_{\psi})$ . Then there exists  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  with  $\varphi(p) \neq 0$  and  $\varphi u_{\psi} = 0$ , i.e.,  $\varphi u_{\psi}(\eta) = 0 \,\forall \, \eta \in \mathcal{S}(\mathbb{R}^n)$ . By the injectivity of  $\mathcal{S}(\mathbb{R}^n) \hookrightarrow \mathcal{S}'(\mathbb{R}^n)$  this means  $\varphi \psi = 0$ , so  $\psi \equiv 0$  in a neighborhood of p and  $p \notin \operatorname{supp}(\psi)$ .

Consider the simplest examples of distribution which are not functions, namely those with support at a given point p. The obvious one is the Dirac delta 'function'

(7.24) 
$$\delta_p(\varphi) = \varphi(p) \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

We can make many more, because  $D^{\alpha}$  is local

(7.25) 
$$\operatorname{supp}(D^{\alpha}u) \subset \operatorname{supp}(u) \ \forall \ u \in \mathcal{S}'(\mathbb{R}^n).$$

Indeed,  $p \notin \text{supp}(u) \Rightarrow \exists \varphi \in \mathcal{S}(\mathbb{R}^n)$ ,  $\varphi u \equiv 0$ ,  $\varphi(p) \neq 0$ . Thus each of the distributions  $D^{\alpha} \delta_p$  also has support contained in  $\{p\}$ . In fact none of them vanish, and they are all linearly independent.

### 8. Convolution and density

We have defined an inclusion map (8.1)

$$\mathcal{S}(\mathbb{R}^n) \ni \varphi \longmapsto u_{\varphi} \in \mathcal{S}'(\mathbb{R}^n), \ u_{\varphi}(\psi) = \int_{\mathbb{R}^n} \varphi(x)\psi(x) \, dx \ \forall \ \psi \in \mathcal{S}(\mathbb{R}^n).$$

This allows us to 'think of'  $\mathcal{S}(\mathbb{R}^n)$  as a subspace of  $\mathcal{S}'(\mathbb{R}^n)$ ; that is we habitually identify  $u_{\varphi}$  with  $\varphi$ . We can do this because we know (8.1) to be injective. We can extend the map (8.1) to include bigger spaces

(8.2) 
$$C_0^0(\mathbb{R}^n) \ni \varphi \longmapsto u_{\varphi} \in \mathcal{S}'(\mathbb{R}^n)$$
$$L^p(\mathbb{R}^n) \ni \varphi \longmapsto u_{\varphi} \in \mathcal{S}'(\mathbb{R}^n)$$
$$M(\mathbb{R}^n) \ni \mu \longmapsto u_{\mu} \in \mathcal{S}'(\mathbb{R}^n)$$
$$u_{\mu}(\psi) = \int_{\mathbb{R}^n} \psi \, d\mu \,,$$

but we need to know that these maps are injective before we can forget about them.

We can see this using *convolution*. This is a sort of 'product' of functions. To begin with, suppose  $v \in \mathcal{C}_0^0(\mathbb{R}^n)$  and  $\psi \in \mathcal{S}(\mathbb{R}^n)$ . We define a new function by 'averaging v with respect to  $\psi$ :'

(8.3) 
$$v * \psi(x) = \int_{\mathbb{R}^n} v(x-y)\psi(y) \, dy.$$

The integral converges by dominated convergence, namely  $\psi(y)$  is integrable and v is bounded,

$$|v(x-y)\psi(y)| \le ||v||_{\mathcal{C}_0^0} |\psi(y)|$$
.

We can use the same sort of estimates to show that  $v * \psi$  is continuous. Fix  $x \in \mathbb{R}^n$ ,

(8.4) 
$$v * \psi(x + x') - v * \psi(x)$$
  
=  $\int (v(x + x' - y) - v(x - y))\psi(y) dy$ .

To see that this is small for x' small, we split the integral into two pieces. Since  $\psi$  is very small near infinity, given  $\epsilon > 0$  we can choose R so large that

(8.5) 
$$||v||_{\infty} \cdot \int_{|y|| \ge R} |\psi(y)| \ dy \le \epsilon/4 \,.$$

The set  $|y| \le R$  is compact and if  $|x| \le R'$ ,  $|x'| \le 1$  then  $|x + x' - y| \le R + R' + 1$ . A continuous function is uniformly continuous on any

compact set, so we can chose  $\delta > 0$  such that

(8.6) 
$$\sup_{\substack{|x'|<\delta\\|y|< R}} |v(x+x'-y)-v(x-y)| \cdot \int_{|y|\leq R} |\psi(y)| \ dy < \epsilon/2.$$

Combining (8.5) and (8.6) we conclude that  $v*\psi$  is continuous. Finally, we conclude that

(8.7) 
$$v \in \mathcal{C}_0^0(\mathbb{R}^n) \Rightarrow v * \psi \in \mathcal{C}_0^0(\mathbb{R}^n).$$

For this we need to show that  $v * \psi$  is small at infinity, which follows from the fact that v is small at infinity. Namely given  $\epsilon > 0$  there exists R > 0 such that  $|v(y)| \le \epsilon$  if  $|y| \ge R$ . Divide the integral defining the convolution into two

$$|v * \psi(x)| \le \int_{|y| > R} u(y)\psi(x - y)dy + \int_{y < R} |u(y)\psi(x - y)|dy \le \epsilon/2||\psi||_{\infty} + ||u||_{\infty} \sup_{B(x,R)} |\psi|.$$

Since  $\psi \in \mathcal{S}(\mathbb{R}^n)$  the last constant tends to 0 as  $|x| \to \infty$ .

We can do much better than this! Assuming  $|x'| \leq 1$  we can use Taylor's formula with remainder to write

(8.8) 
$$\psi(z+x') - \psi(z) = \int_0^1 \frac{d}{dt} \psi(z+tx') dt = \sum_{i=1}^n x_i \cdot \tilde{\psi}_i(z,x').$$

As Problem 23 I ask you to check carefully that

(8.9) 
$$\psi_i(z; x') \in \mathcal{S}(\mathbb{R}^n)$$
 depends continuously on  $x'$  in  $|x'| \leq 1$ .

Going back to (8.3)) we can use the translation and reflection-invariance of Lebesgue measure to rewrite the integral (by changing variable) as

(8.10) 
$$v * \psi(x) = \int_{\mathbb{R}^n} v(y)\psi(x - y) \, dy.$$

This reverses the role of v and  $\psi$  and shows that if both v and  $\psi$  are in  $\mathcal{S}(\mathbb{R}^n)$  then  $v * \psi = \psi * v$ .

Using this formula on (8.4) we find

$$v * \psi(x + x') - v * \psi(x) = \int v(y)(\psi(x + x' - y) - \psi(x - y)) dy$$
$$= \sum_{j=1}^{n} x_j \int_{\mathbb{R}^n} v(y)\tilde{\psi}_j(x - y, x') dy = \sum_{j=1}^{n} x_j(v * \psi_j(\cdot; x')(x)).$$

From (8.9) and what we have already shown,  $v * \psi(\cdot; x')$  is continuous in both variables, and is in  $C_0^0(\mathbb{R}^n)$  in the first. Thus

$$(8.12) v \in \mathcal{C}_0^0(\mathbb{R}^n), \ \psi \in \mathcal{S}(\mathbb{R}^n) \Rightarrow v * \psi \in \mathcal{C}_0^1(\mathbb{R}^n).$$

In fact we also see that

(8.13) 
$$\frac{\partial}{\partial x_j} v * \psi = v * \frac{\partial \psi}{\partial x_j}.$$

Thus  $v * \psi$  inherits its regularity from  $\psi$ .

**Proposition 8.1.** If  $v \in C_0^0(\mathbb{R}^n)$  and  $\psi \in \mathcal{S}(\mathbb{R}^n)$  then

(8.14) 
$$v * \psi \in \mathcal{C}_0^{\infty}(\mathbb{R}^n) = \bigcap_{k>0} \mathcal{C}_0^k(\mathbb{R}^n).$$

*Proof.* This follows from (8.12), (8.13) and induction.

Now, let us make a more special choice of  $\psi$ . We have shown the existence of

(8.15) 
$$\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n), \ \varphi \geq 0, \ \operatorname{supp}(\varphi) \subset \{|x| \leq 1\}.$$

We can also assume  $\int_{\mathbb{R}^n} \varphi \, dx = 1$ , by multiplying by a positive constant. Now consider

(8.16) 
$$\varphi_t(x) = t^{-n} \varphi\left(\frac{x}{t}\right) \ 1 \ge t > 0.$$

This has all the same properties, except that

(8.17) 
$$\operatorname{supp} \varphi_t \subset \{|x| \le t\} , \int \varphi_t \, dx = 1.$$

**Proposition 8.2.** If  $v \in C_0^0(\mathbb{R}^n)$  then as  $t \to 0$ ,  $v_t = v * \varphi_t \to v$  in  $C_0^0(\mathbb{R}^n)$ .

*Proof.* using (8.17) we can write the difference as

(8.18) 
$$|v_t(x) - v(x)| = |\int_{\mathbb{R}^n} (v(x - y) - v(x))\varphi_t(y) dy|$$
  

$$\leq \sup_{|y| < t} |v(x - y) - v(x)| \to 0.$$

Here we have used the fact that  $\varphi_t \geq 0$  has support in  $|y| \leq t$  and has integral 1. Thus  $v_t \to v$  uniformly on any set on which v is uniformly continuous, namel  $\mathbb{R}^n$ !

Corollary 8.3.  $C_0^k(\mathbb{R}^n)$  is dense in  $C_0^p(\mathbb{R}^n)$  for any  $k \geq p$ .

**Proposition 8.4.**  $\mathcal{S}(\mathbb{R}^n)$  is dense in  $\mathcal{C}_0^k(\mathbb{R}^n)$  for any  $k \geq 0$ .

*Proof.* Take k=0 first. The subspace  $C_c^0(\mathbb{R}^n)$  is dense in  $C_0^0(\mathbb{R}^n)$ , by cutting off outside a large ball. If  $v \in C_c^0(\mathbb{R}^n)$  has support in  $\{|x| \leq R\}$  then

$$v * \varphi_t \in \mathcal{C}_c^{\infty}(\mathbb{R}^n) \subset \mathcal{S}(\mathbb{R}^n)$$

has support in  $\{|x| \leq R+1\}$ . Since  $v * \varphi_t \to v$  the result follows for k=0

For  $k \geq 1$  the same argument works, since  $D^{\alpha}(v * \varphi_t) = (D^{\alpha}V) * \varphi_t$ .

Corollary 8.5. The map from finite Radon measures

$$(8.19) M_{fin}(\mathbb{R}^n) \ni \mu \longmapsto u_{\mu} \in \mathcal{S}'(\mathbb{R}^n)$$

is injective.

Now, we want the same result for  $L^2(\mathbb{R}^n)$  (and maybe for  $L^p(\mathbb{R}^n)$ ,  $1 \leq p < \infty$ ). I leave the measure-theoretic part of the argument to you.

**Proposition 8.6.** Elements of  $L^2(\mathbb{R}^n)$  are "continuous in the mean" i.e.,

(8.20) 
$$\lim_{|t| \to 0} \int_{\mathbb{R}^n} |u(x+t) - u(x)|^2 dx = 0.$$

This is Problem 24.

Using this we conclude that

(8.21) 
$$\mathcal{S}(\mathbb{R}^n) \hookrightarrow L^2(\mathbb{R}^n)$$
 is dense

as before. First observe that the space of  $L^2$  functions of compact support is dense in  $L^2(\mathbb{R}^n)$ , since

$$\lim_{R \to \infty} \int_{|x| > R} |u(x)|^2 dx = 0 \,\forall u \in L^2(\mathbb{R}^n).$$

Then look back at the discussion of  $v * \varphi$ , now v is replaced by  $u \in L_c^2(\mathbb{R}^n)$ . The compactness of the support means that  $u \in L^1(\mathbb{R}^n)$  so in

(8.22) 
$$u * \varphi(x) = \int_{\mathbb{R}^n} u(x - y)\varphi(y)dy$$

the integral is absolutely convergent. Moreover

$$|u * \varphi(x + x') - u * \varphi(x)|$$

$$= \left| \int u(y)(\varphi(x + x' - y) - \varphi(x - y)) dy \right|$$

$$\leq C||u|| \sup_{|y| \leq R} |\varphi(x + x' - y) - \varphi(x - y)| \to 0$$

when  $\{|x| \leq R\}$  large enough. Thus  $u * \varphi$  is continuous and the same argument as before shows that

$$u * \varphi_t \in \mathcal{S}(\mathbb{R}^n)$$
.

Now to see that  $u * \varphi_t \to u$ , assuming u has compact support (or not) we estimate the integral

$$|u * \varphi_t(x) - u(x)| = \left| \int (u(x - y) - u(x))\varphi_t(y) \, dy \right|$$

$$\leq \int |u(x - y) - u(x)| \, \varphi_t(y) \, dy.$$

Using the same argument twice

$$\int |u * \varphi_t(x) - u(x)|^2 dx$$

$$\leq \iiint |u(x - y) - u(x)| \varphi_t(y) |u(x - y') - u(x)| \varphi_t(y') dx dy dy'$$

$$\leq \left( \int |u(x - y) - u(x)|^2 \varphi_t(y) \varphi_t(y') dx dy dy' \right)$$

$$\leq \sup_{|u| \leq t} \int |u(x - y) - u(x)|^2 dx.$$

Note that at the second step here I have used Schwarz's inequality with the integrand written as the product

$$|u(x-y)-u(x)| \varphi_t^{1/2}(y)\varphi_t^{1/2}(y') \cdot |u(x-y')-u(x)| \varphi_t^{1/2}(y)\varphi_t^{1/2}(y')$$
.

Thus we now know that

$$L^2(\mathbb{R}^n) \hookrightarrow \mathcal{S}'(\mathbb{R}^n)$$
 is injective.

This means that all our usual spaces of functions 'sit inside'  $\mathcal{S}'(\mathbb{R}^n)$ .

Finally we can use convolution with  $\varphi_t$  to show the existence of smooth partitions of unity. If  $K \in U \subset \mathbb{R}^n$  is a compact set in an open set then we have shown the existence of  $\xi \in \mathcal{C}_c^0(\mathbb{R}^n)$ , with  $\xi = 1$  in some neighborhood of K and  $\xi = 1$  in some neighborhood of K and  $\sup(\xi) \subseteq U$ .

Then consider  $\xi * \varphi_t$  for t small. In fact

$$\operatorname{supp}(\xi * \varphi_t) \subset \{ p \in \mathbb{R}^n \, ; \, \operatorname{dist}(p, \operatorname{supp} \xi) \leq 2t \}$$

and similarly,  $0 \le \xi * \varphi_t \le 1$  and

$$\xi * \varphi_t = 1$$
 at  $p$  if  $\xi = 1$  on  $B(p, 2t)$ .

Using this we get:

**Proposition 8.7.** If  $U_a \subset \mathbb{R}^n$  are open for  $a \in A$  and  $K \subseteq \bigcup_{a \in A} U_a$  then there exist finitely many  $\varphi_i \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ , with  $0 \le \varphi_i \le 1$ , supp $(\varphi_i) \subset U_{a_i}$  such that  $\sum_i \varphi_i = 1$  in a neighbourhood of K.

*Proof.* By the compactness of K we may choose a finite open subcover. Using Lemma 1.8 we may choose a continuous partition,  $\phi'_i$ , of unity subordinate to this cover. Using the convolution argument above we can replace  $\phi'_i$  by  $\phi'_i * \varphi_t$  for t > 0. If t is sufficiently small then this is again a partition of unity subordinate to the cover, but now smooth.

Next we can make a simple 'cut off argument' to show

**Lemma 8.8.** The space  $C_c^{\infty}(\mathbb{R}^n)$  of  $C^{\infty}$  functions of compact support is dense in  $S(\mathbb{R}^n)$ .

*Proof.* Choose  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $\varphi(x) = 1$  in  $|x| \leq 1$ . Then given  $\psi \in \mathcal{S}(\mathbb{R}^n)$  consider the sequence

$$\psi_n(x) = \varphi(x/n)\psi(x)$$
.

Clearly  $\psi_n = \psi$  on  $|x| \leq n$ , so if it converges in  $\mathcal{S}(\mathbb{R}^n)$  it must converge to  $\psi$ . Suppose  $m \geq n$  then by Leibniz's formula<sup>13</sup>

$$D_x^{\alpha}(\psi_n(x) - \psi_m(x))$$

$$= \sum_{\beta < \alpha} {\alpha \choose \beta} D_x^{\beta} \left( \varphi(\frac{x}{n}) - \varphi(\frac{x}{m}) \right) \cdot D_x^{\alpha - \beta} \psi(x) .$$

All derivatives of  $\varphi(x/n)$  are bounded, independent of n and  $\psi_n = \psi_m$  in  $|x| \le n$  so for any p

$$|D_x^{\alpha}(\psi_n(x) - \psi_m(x))| \le \begin{cases} 0 & |x| \le n \\ C_{\alpha,p}\langle x \rangle^{-2p} & |x| \ge n \end{cases}.$$

Hence  $\psi_n$  is Cauchy in  $\mathcal{S}(\mathbb{R}^n)$ .

Thus every element of  $\mathcal{S}'(\mathbb{R}^n)$  is determined by its restriction to  $\mathcal{C}_c^{\infty}(\mathbb{R}^n)$ . The support of a tempered distribution was defined above to be

(8.23) 
$$\operatorname{supp}(u) = \left\{ x \in \mathbb{R}^n; \ \exists \ \varphi \in \mathcal{S}(\mathbb{R}^n), \ \varphi(x) \neq 0, \ \varphi u = 0 \right\}^{\complement}.$$

Using the preceding lemma and the construction of smooth partitions of unity we find

**Proposition 8.9.**  $f u \in \mathcal{S}'(\mathbb{R}^n)$  and  $\operatorname{supp}(u) = \emptyset$  then u = 0.

 $<sup>^{13}</sup>$ Problem 25.

Proof. From (8.23), if  $\psi \in \mathcal{S}(\mathbb{R}^n)$ ,  $\operatorname{supp}(\psi u) \subset \operatorname{supp}(u)$ . If  $x \ni \operatorname{supp}(u)$  then, by definition,  $\varphi u = 0$  for some  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  with  $\varphi(x) \neq 0$ . Thus  $\varphi \neq 0$  on  $B(x, \epsilon)$  for  $\epsilon > 0$  sufficiently small. If  $\psi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  has support in  $B(x, \epsilon)$  then  $\psi u = \tilde{\psi} \varphi u = 0$ , where  $\tilde{\psi} \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ :

$$\tilde{\psi} = \left\{ \begin{array}{ll} \psi/\varphi & \text{in } B(x,\epsilon) \\ 0 & \text{elsewhere} \,. \end{array} \right.$$

Thus, given  $K \in \mathbb{R}^n$  we can find  $\varphi_j \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ , supported in such balls, so that  $\sum_j \varphi_j \equiv 1$  on K but  $\varphi_j u = 0$ . For given  $\mu \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  apply this to  $\operatorname{supp}(\mu)$ . Then

$$\mu = \sum_{j} \varphi_{j} \mu \Rightarrow u(\mu) = \sum_{j} (\phi_{j} u)(\mu) = 0.$$

Thus u = 0 on  $\mathcal{C}_c^{\infty}(\mathbb{R}^n)$ , so u = 0.

The linear space of distributions of compact support will be denoted  $\mathcal{C}_c^{-\infty}(\mathbb{R}^n)$ ; it is often written  $\mathcal{E}'(\mathbb{R}^n)$ .

Now let us give a characterization of the 'delta function'

$$\delta(\varphi) = \varphi(0) \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n) \,,$$

or at least the one-dimensional subspace of  $\mathcal{S}'(\mathbb{R}^n)$  it spans. This is based on the simple observation that  $(x_i\varphi)(0) = 0$  if  $\varphi \in \mathcal{S}(\mathbb{R}^n)$ !

**Proposition 8.10.** If  $u \in \mathcal{S}'(\mathbb{R}^n)$  satisfies  $x_j u = 0$ ,  $j = 1, \dots, n$  then  $u = c\delta$ .

*Proof.* The main work is in characterizing the null space of  $\delta$  as a linear functional, namely in showing that

(8.24) 
$$\mathcal{H} = \{ \varphi \in \mathcal{S}(\mathbb{R}^n); \ \varphi(0) = 0 \}$$

can also be written as

(8.25) 
$$\mathcal{H} = \left\{ \varphi \in \mathcal{S}(\mathbb{R}^n); \ \varphi = \sum_{j=1}^n x_j \psi_j, \ \varphi_j \in \mathcal{S}(\mathbb{R}^n) \right\}.$$

Clearly the right side of (8.25) is contained in the left. To see the converse, suppose first that

(8.26) 
$$\varphi \in \mathcal{S}(\mathbb{R}^n), \ \varphi = 0 \text{ in } |x| < 1.$$

Then define

$$\psi = \begin{cases} 0 & |x| < 1\\ \varphi/|x|^2 & |x| \ge 1. \end{cases}$$

All the derivatives of  $1/|x|^2$  are bounded in  $|x| \ge 1$ , so from Leibniz's formula it follows that  $\psi \in \mathcal{S}(\mathbb{R}^n)$ . Since

$$\varphi = \sum_{j} x_j(x_j \psi)$$

this shows that  $\varphi$  of the form (8.26) is in the right side of (8.25). In general suppose  $\varphi \in \mathcal{S}(\mathbb{R}^n)$ . Then

(8.27) 
$$\varphi(x) - \varphi(0) = \int_0^t \frac{d}{dt} \varphi(tx) dt$$
$$= \sum_{j=1}^n x_j \int_0^t \frac{\partial \varphi}{\partial x_j}(tx) dt.$$

Certainly these integrals are  $C^{\infty}$ , but they may not decay rapidly at infinity. However, choose  $\mu \in C_c^{\infty}(\mathbb{R}^n)$  with  $\mu = 1$  in  $|x| \leq 1$ . Then (8.27) becomes, if  $\varphi(0) = 0$ ,

$$\varphi = \mu \varphi + (1 - \mu) \varphi$$

$$= \sum_{j=1}^{n} x_j \psi_j + (1 - \mu) \varphi, \ \psi_j = \mu \int_0^t \frac{\partial \varphi}{\partial x_j} (tx) \, dt \in \mathcal{S}(\mathbb{R}^n).$$

Since  $(1 - \mu)\varphi$  is of the form (8.26), this proves (8.25). Our assumption on u is that  $x_j u = 0$ , thus

$$u(\varphi) = 0 \ \forall \ \varphi \in \mathcal{H}$$

by (8.25). Choosing  $\mu$  as above, a general  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  can be written

$$\varphi = \varphi(0) \cdot \mu + \varphi', \ \varphi' \in \mathcal{H}.$$

Then

$$u(\varphi) = \varphi(0)u(\mu) \Rightarrow u = c\delta\,,\ c = u(\mu)\,.$$

This result is quite powerful, as we shall soon see. The Fourier transform of an element  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  is  $^{14}$ 

(8.28) 
$$\hat{\varphi}(\xi) = \int e^{-ix\cdot\xi} \varphi(x) \, dx \,, \, \xi \in \mathbb{R}^n \,.$$

<sup>&</sup>lt;sup>14</sup>Normalizations vary, but it doesn't matter much.

The integral certainly converges, since  $|\varphi| \leq C\langle x\rangle^{-n-1}$ . In fact it follows easily that  $\hat{\varphi}$  is continuous, since

$$|\hat{\varphi}(\xi) - \hat{\varphi}(\xi')| \in \int \left| e^{ix - \xi} - e^{-x \cdot \xi'} \right| |\varphi| \ dx$$
$$\to 0 \text{ as } \xi' \to \xi.$$

In fact

**Proposition 8.11.** Fourier transformation, (8.28), defines a continuous linear map

(8.29) 
$$\mathcal{F}: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n), \ \mathcal{F}\varphi = \hat{\varphi}.$$

*Proof.* Differentiating under the integral<sup>15</sup> sign shows that

$$\partial_{\xi_j}\hat{\varphi}(\xi) = -i\int e^{-ix\cdot\xi}x_j\varphi(x)\,dx\,.$$

Since the integral on the right is absolutely convergent that shows that (remember the i's)

(8.30) 
$$D_{\xi_i}\hat{\varphi} = -\widehat{x_j\varphi}, \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

Similarly, if we multiply by  $\xi_j$  and observe that  $\xi_j e^{-ix\cdot\xi} = i\frac{\partial}{\partial x_j} e^{-ix\cdot\xi}$  then integration by parts shows

(8.31) 
$$\xi_{j}\hat{\varphi} = i \int (\frac{\partial}{\partial x_{j}} e^{-ix\cdot\xi})\varphi(x) dx$$
$$= -i \int e^{-ix\cdot\xi} \frac{\partial \varphi}{\partial x_{j}} dx$$
$$\widehat{D_{j}\varphi} = \xi_{j}\hat{\varphi}, \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^{n}).$$

Since  $x_j \varphi$ ,  $D_j \varphi \in \mathcal{S}(\mathbb{R}^n)$  these results can be iterated, showing that

(8.32) 
$$\xi^{\alpha} D_{\varepsilon}^{\beta} \hat{\varphi} = \mathcal{F} \left( (-1)^{|\beta|} D_{x}^{\alpha} x^{\beta} \varphi \right).$$

Thus  $\left| \xi^{\alpha} D_{\xi}^{\beta} \hat{\varphi} \right| \leq C_{\alpha\beta} \sup \left| \langle x \rangle^{+n+1} D_{x}^{\alpha} x^{\beta} \varphi \right| \leq C \|\langle x \rangle^{n+1+|\beta|} \varphi \|_{\mathcal{C}^{|\alpha|}}$ , which shows that  $\mathcal{F}$  is continuous as a map (8.32).

Suppose  $\varphi \in \mathcal{S}(\mathbb{R}^n)$ . Since  $\hat{\varphi} \in \mathcal{S}(\mathbb{R}^n)$  we can consider the distribution  $u \in \mathcal{S}'(\mathbb{R}^n)$ 

(8.33) 
$$u(\varphi) = \int_{\mathbb{R}^n} \hat{\varphi}(\xi) \, d\xi.$$

<sup>&</sup>lt;sup>15</sup>See [5]

The continuity of u follows from the fact that integration is continuous and (8.29). Now observe that

$$u(x_{j}\varphi) = \int_{\mathbb{R}^{n}} \widehat{x_{j}\varphi}(\xi) d\xi$$
$$= -\int_{\mathbb{R}^{n}} D_{\xi_{j}} \widehat{\varphi} d\xi = 0$$

where we use (8.30). Applying Proposition 8.10 we conclude that  $u = c\delta$  for some (universal) constant c. By definition this means

(8.34) 
$$\int_{\mathbb{P}^n} \hat{\varphi}(\xi) \, d\xi = c\varphi(0) \,.$$

So what is the constant? To find it we need to work out an example. The simplest one is

$$\varphi = \exp(-\left|x\right|^2/2).$$

**Lemma 8.12.** The Fourier transform of the Gaussian  $\exp(-|x|^2/2)$  is the Gaussian  $(2\pi)^{n/2} \exp(-|\xi|^2/2)$ .

*Proof.* There are two obvious methods — one uses complex analysis (Cauchy's theorem) the other, which I shall follow, uses the uniqueness of solutions to ordinary differential equations.

First observe that  $\exp(-|x|^2/2) = \prod_j \exp(-x_j^2/2)$ . Thus<sup>16</sup>

$$\hat{\varphi}(\xi) = \prod_{j=1}^{n} \hat{\psi}(\xi_j), \ \psi(x) = e^{-x^2/2},$$

being a function of one variable. Now  $\psi$  satisfies the differential equation

$$(\partial_x + x) \psi = 0,$$

and is the *only* solution of this equation up to a constant multiple. By (8.30) and (8.31) its Fourier transform satisfies

$$\widehat{\partial_x \psi} + \widehat{x\psi} = i\xi \hat{\psi} + i\frac{d}{d\xi} \hat{\varphi} = 0.$$

This is the same equation, but in the  $\xi$  variable. Thus  $\hat{\psi} = ce^{-|\xi|^2/2}$ . Again we need to find the constant. However,

$$\hat{\psi}(0) = c = \int e^{-x^2/2} dx = (2\pi)^{1/2}$$

<sup>&</sup>lt;sup>16</sup>Really by Fubini's theorem, but here one can use Riemann integrals.

by the standard use of polar coordinates:

$$c^{2} = \int_{\mathbb{R}^{n}} e^{-(x^{2}+y^{2})/2} dx dy = \int_{0}^{\infty} \int_{0}^{2\pi} e^{-r^{2}/2} r dr d\theta = 2\pi.$$

This proves the lemma.

Thus we have shown that for any  $\varphi \in \mathcal{S}(\mathbb{R}^n)$ 

(8.35) 
$$\int_{\mathbb{R}^n} \hat{\varphi}(\xi) d\xi = (2\pi)^n \varphi(0).$$

Since this is true for  $\varphi = \exp(-\left|x\right|^2/2)$ . The identity allows us to *invert* the Fourier transform.

#### 9. Fourier inversion

It is shown above that the Fourier transform satisfies the identity

(9.1) 
$$\varphi(0) = (2\pi)^{-n} \int_{\mathbb{R}^n} \hat{\varphi}(\xi) \, d\xi \, \forall \, \varphi \in \mathcal{S}(\mathbb{R}^n) \, .$$

If  $y \in \mathbb{R}^n$  and  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  set  $\psi(x) = \varphi(x+y)$ . The translation-invariance of Lebesgue measure shows that

$$\hat{\psi}(\xi) = \int e^{-ix\cdot\xi} \varphi(x+y) \, dx$$
$$= e^{iy\cdot\xi} \hat{\varphi}(\xi) \, .$$

Applied to  $\psi$  the inversion formula (9.1) becomes

(9.2) 
$$\varphi(y) = \psi(0) = (2\pi)^{-n} \int \hat{\psi}(\xi) d\xi$$
$$= (2\pi)^{-n} \int_{\mathbb{R}^n} e^{iy \cdot \xi} \hat{\varphi}(\xi) d\xi.$$

**Theorem 9.1.** Fourier transform  $\mathcal{F}: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n)$  is an isomorphism with inverse

(9.3) 
$$\mathcal{G}: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n), \, \mathcal{G}\psi(y) = (2\pi)^{-n} \int e^{iy\cdot\xi} \psi(\xi) \, d\xi.$$

*Proof.* The identity (9.2) shows that  $\mathcal{F}$  is 1-1, i.e., injective, since we can remove  $\varphi$  from  $\hat{\varphi}$ . Moreover,

(9.4) 
$$\mathcal{G}\psi(y) = (2\pi)^{-n} \mathcal{F}\psi(-y)$$

So  $\mathcal{G}$  is also a continuous linear map,  $\mathcal{G}: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n)$ . Indeed the argument above shows that  $\mathcal{G} \circ \mathcal{F} = Id$  and the same argument, with some changes of sign, shows that  $\mathcal{F} \cdot \mathcal{G} = Id$ . Thus F and  $\mathcal{G}$  are isomorphisms.

**Lemma 9.2.** For all  $\varphi, \psi \in \mathcal{S}(\mathbb{R}^n)$ , Paseval's identity holds:

(9.5) 
$$\int_{\mathbb{R}^n} \varphi \overline{\psi} \, dx = (2\pi)^{-n} \int_{\mathbb{R}^n} \hat{\varphi} \overline{\hat{\psi}} \, d\xi \,.$$

*Proof.* Using the inversion formula on  $\varphi$ ,

$$\int \varphi \overline{\psi} \, dx = (2\pi)^{-n} \int \left( e^{ix \cdot \xi} \hat{\varphi}(\xi) \, d\xi \right) \overline{\psi}(x) \, dx$$
$$= (2\pi)^{-n} \int \hat{\varphi}(\xi) \overline{\int} e^{-ix \cdot \xi} \psi(x) \, dx \, d\xi$$
$$= (2\pi)^{-n} \int \hat{\varphi}(\xi) \overline{\hat{\varphi}}(\xi) \, d\xi \, .$$

Here the integrals are absolutely convergent, justifying the exchange of orders.

Proposition 9.3. Fourier transform extends to an isomorphism

$$(9.6) \mathcal{F}: L^2(\mathbb{R}^n) \to L^2(\mathbb{R}^n).$$

*Proof.* Setting  $\varphi = \psi$  in (9.5) shows that

(9.7) 
$$\|\mathcal{F}\varphi\|_{L^2} = (2\pi)^{n/2} \|\varphi\|_{L^2}.$$

In particular this proves, given the known density of  $\mathcal{S}(\mathbb{R}^n)$  in  $L^2(\mathbb{R}^n)$ , that  $\mathcal{F}$  is an isomorphism, with inverse  $\mathcal{G}$ , as in (9.6).

For any  $m \in \mathbb{R}$ 

$$\langle x \rangle^m L^2(\mathbb{R}^n) = \left\{ u \in \mathcal{S}'(\mathbb{R}^n) ; \langle x \rangle^{-m} \hat{u} \in L^2(\mathbb{R}^n) \right\}$$

is a well-defined subspace. We define the  $Sobolev\ spaces$  on  $\mathbb{R}^n$  by, for  $m\geq 0$ 

(9.8) 
$$H^{m}(\mathbb{R}^{n}) = \left\{ u \in L^{2}(\mathbb{R}^{n}) ; \, \hat{u} = \mathcal{F}u \in \langle \xi \rangle^{-m} L^{2}(\mathbb{R}^{n}) \right\}.$$
Thus  $H^{m}(\mathbb{R}^{n}) \subset H^{m'}(\mathbb{R}^{n})$  if  $m > m'$ ,  $H^{0}(\mathbb{R}^{n}) = L^{2}(\mathbb{R}^{n})$ .

**Lemma 9.4.** If  $m \in \mathbb{N}$  is an integer, then

$$(9.9) u \in H^m(\mathbb{R}^n) \Leftrightarrow D^{\alpha}u \in L^2(\mathbb{R}^n) \ \forall \ |\alpha| \le m.$$

*Proof.* By definition,  $u \in H^m(\mathbb{R}^n)$  implies that  $\langle \xi \rangle^{-m} \hat{u} \in L^2(\mathbb{R}^n)$ . Since  $\widehat{D^{\alpha}u} = \xi^{\alpha}\hat{u}$  this certainly implies that  $D^{\alpha}u \in L^2(\mathbb{R}^n)$  for  $|\alpha| \leq m$ . Conversely if  $D^{\alpha}u \in L^2(\mathbb{R}^n)$  for all  $|\alpha| \leq m$  then  $\xi^{\alpha}\hat{u} \in L^2(\mathbb{R}^n)$  for all  $|\alpha| \leq m$  and since

$$\langle \xi \rangle^m \le C_m \sum_{|\alpha| \le m} |\xi^{\alpha}| \ .$$

this in turn implies that  $\langle \xi \rangle^m \hat{u} \in L^2(\mathbb{R}^n)$ .

Now that we have considered the Fourier transform of Schwartz test functions we can use the usual method, of duality, to extend it to tempered distributions. If we set  $\eta = \overline{\hat{\psi}}$  then  $\hat{\psi} = \overline{\eta}$  and  $\psi = \mathcal{G}\hat{\psi} = \mathcal{G}\overline{\eta}$  so

$$\overline{\psi}(x) = (2\pi)^{-n} \int e^{-ix\cdot\xi} \overline{\hat{\psi}}(\xi) d\xi$$
$$= (2\pi)^{-n} \int e^{-ix\cdot\xi} \eta(\xi) d\xi = (2\pi)^{-n} \hat{\eta}(x).$$

Substituting in (9.5) we find that

$$\int \varphi \hat{\eta} \, dx = \int \hat{\varphi} \eta \, d\xi \, .$$

Now, recalling how we embed  $\mathcal{S}(\mathbb{R}^n) \hookrightarrow \mathcal{S}'(\mathbb{R}^n)$  we see that

$$(9.10) u_{\hat{\varphi}}(\eta) = u_{\varphi}(\hat{\eta}) \ \forall \ \eta \in \mathcal{S}(\mathbb{R}^n) .$$

**Definition 9.5.** If  $u \in \mathcal{S}'(\mathbb{R}^n)$  we define its Fourier transform by

(9.11) 
$$\hat{u}(\varphi) = u(\hat{\varphi}) \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

As a composite map,  $\hat{u} = u \cdot \mathcal{F}$ , with each term continuous,  $\hat{u}$  is continuous, i.e.,  $\hat{u} \in \mathcal{S}'(\mathbb{R}^n)$ .

**Proposition 9.6.** The definition (9.7) gives an isomorphism

$$\mathcal{F}: \mathcal{S}'(\mathbb{R}^n) \to \mathcal{S}'(\mathbb{R}^n), \ \mathcal{F}u = \hat{u}$$

satisfying the identities

(9.12) 
$$\widehat{D^{\alpha}u} = \xi^{\alpha}u, \ \widehat{x^{\alpha}u} = (-1)^{|\alpha|}D^{\alpha}\hat{u}.$$

*Proof.* Since  $\hat{u} = u \circ \mathcal{F}$  and  $\mathcal{G}$  is the 2-sided inverse of  $\mathcal{F}$ ,

$$(9.13) u = \hat{u} \circ \mathcal{G}$$

gives the inverse to  $\mathcal{F}: \mathcal{S}'(\mathbb{R}^n) \to \mathcal{S}'(\mathbb{R}^n)$ , showing it to be an isomorphism. The identities (9.12) follow from their counterparts on  $\mathcal{S}(\mathbb{R}^n)$ :

$$\widehat{D^{\alpha}u}(\varphi) = D^{\alpha}u(\widehat{\varphi}) = u((-1)^{|\alpha|}D^{\alpha}\widehat{\varphi})$$
$$= u(\widehat{\xi^{\alpha}\varphi}) = \widehat{u}(\xi^{\alpha}\varphi) = \xi^{\alpha}\widehat{u}(\varphi) \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^{n}).$$

We can also define Sobolev spaces of *negative* order:

$$(9.14) H^m(\mathbb{R}^n) = \left\{ u \in \mathcal{S}'(\mathbb{R}^n) ; \, \hat{u} \in \langle \xi \rangle^{-m} L^2(\mathbb{R}^n) \right\}.$$

**Proposition 9.7.** If  $m \leq 0$  is an integer then  $u \in H^m(\mathbb{R}^n)$  if and only if it can be written in the form

(9.15) 
$$u = \sum_{|\alpha| \le -m} D^{\alpha} v_{\alpha}, v_{\alpha} \in L^{2}(\mathbb{R}^{n}).$$

*Proof.* If  $u \in \mathcal{S}'(\mathbb{R}^n)$  is of the form (9.15) then

(9.16) 
$$\hat{u} = \sum_{|\alpha| \le -m} \xi^{\alpha} \hat{v}_{\alpha} \text{ with } \hat{v}\alpha \in L^{2}(\mathbb{R}^{n}).$$

Thus  $\langle \xi \rangle^m \hat{u} = \sum_{|\alpha| \leq -m} \xi^{\alpha} \langle \xi \rangle^m \hat{v}_{\alpha}$ . Since all the factors  $\xi^{\alpha} \langle \xi \rangle^m$  are bounded, each term here is in  $L^2(\mathbb{R}^n)$ , so  $\langle \xi \rangle^m \hat{u} \in L^2(\mathbb{R}^n)$  which is the definition,  $u \in \langle \xi \rangle^{-m} L^2(\mathbb{R}^n)$ .

Conversely, suppose  $u \in H^m(\mathbb{R}^n)$ , i.e.,  $\langle \xi \rangle^m \hat{u} \in L^2(\mathbb{R}^n)$ . The function

$$\left(\sum_{|\alpha| \le -m} |\xi^{\alpha}|\right) \cdot \langle \xi \rangle^m \in L^2(\mathbb{R}^n) \ (m < 0)$$

is bounded below by a positive constant. Thus

$$v = \left(\sum_{|\alpha| \le -m} |\xi^{\alpha}|\right)^{-1} \hat{u} \in L^{2}(\mathbb{R}^{n}).$$

Each of the functions  $\hat{v}_{\alpha} = \operatorname{sgn}(\xi^{\alpha})\hat{v} \in L^{2}(\mathbb{R}^{n})$  so the identity (9.16), and hence (9.15), follows with these choices.

**Proposition 9.8.** Each of the Sobolev spaces  $H^m(\mathbb{R}^n)$  is a Hilbert space with the norm and inner product

(9.17) 
$$||u||_{H^m} = \left(\int_{\mathbb{R}^n} |\hat{u}(\xi)|^2 \langle \xi \rangle^{2m} d\xi\right)^{1/2},$$
$$\langle u, v \rangle = \int_{\mathbb{R}^n} \hat{u}(\xi) \overline{\hat{v}(\xi)} \langle \xi \rangle^{2m} d\xi.$$

The Schwartz space  $\mathcal{S}(\mathbb{R}^n) \hookrightarrow H^m(\mathbb{R}^n)$  is dense for each m and the pairing

(9.18) 
$$H^{m}(\mathbb{R}^{n}) \times H^{-m}(\mathbb{R}^{n}) \ni (u, u') \longmapsto ((u, u')) = \int_{\mathbb{R}^{n}} \hat{u'}(\xi) \hat{u'}(\cdot \xi) d\xi \in \mathbb{C}$$

gives an identification  $(H^m(\mathbb{R}^n))' = H^{-m}(\mathbb{R}^n)$ .

*Proof.* The Hilbert space property follows essentially directly from the definition (9.14) since  $\langle \xi \rangle^{-m} L^2(\mathbb{R}^n)$  is a Hilbert space with the norm (9.17). Similarly the density of  $\mathcal{S}$  in  $H^m(\mathbb{R}^n)$  follows, since  $\mathcal{S}(\mathbb{R}^n)$  dense in  $L^2(\mathbb{R}^n)$  (Problem L11.P3) implies  $\langle \xi \rangle^{-m} \mathcal{S}(\mathbb{R}^n) = \mathcal{S}(\mathbb{R}^n)$  is dense in  $\langle \xi \rangle^{-m} L^2(\mathbb{R}^n)$  and so, since  $\mathcal{F}$  is an isomorphism in  $\mathcal{S}(\mathbb{R}^n)$ ,  $\mathcal{S}(\mathbb{R}^n)$  is dense in  $H^m(\mathbb{R}^n)$ .

Finally observe that the pairing in (9.18) makes sense, since  $\langle \xi \rangle^{-m} \hat{u}(\xi)$ ,  $\langle \xi \rangle^m \hat{u}'(\xi) \in L^2(\mathbb{R}^n)$  implies

$$\hat{u}(\xi))\hat{u'}(-\xi) \in L^1(\mathbb{R}^n)$$
.

Furthermore, by the self-duality of  $L^2(\mathbb{R}^n)$  each continuous linear functional

$$U: H^m(\mathbb{R}^n) \to \mathbb{C}, \ U(u) \le C \|u\|_{H^m}$$

can be written uniquely in the form

$$U(u) = ((u, u'))$$
 for some  $u' \in H^{-m}(\mathbb{R}^n)$ .

Notice that if  $u, u' \in \mathcal{S}(\mathbb{R}^n)$  then

$$((u, u')) = \int_{\mathbb{R}^n} u(x)u'(x) dx.$$

This is always how we "pair" functions — it is the natural pairing on  $L^2(\mathbb{R}^n)$ . Thus in (9.18) what we have shown is that this pairing on test function

$$\mathcal{S}(\mathbb{R}^n) \times \mathcal{S}(\mathbb{R}^n) \ni (u, u') \longmapsto ((u, u')) = \int_{\mathbb{R}^n} u(x)u'(x) dx$$

extends by *continuity* to  $H^m(\mathbb{R}^n) \times H^{-m}(\mathbb{R}^n)$  (for each fixed m) when it identifies  $H^{-m}(\mathbb{R}^n)$  as the dual of  $H^m(\mathbb{R}^n)$ . This was our 'picture' at the beginning.

For m > 0 the spaces  $H^m(\mathbb{R}^n)$  represents elements of  $L^2(\mathbb{R}^n)$  that have "m" derivatives in  $L^2(\mathbb{R}^n)$ . For m < 0 the elements are ?? of "up to -m" derivatives of  $L^2$  functions. For integers this is precisely ??.

### 10. Sobolev embedding

The properties of Sobolev spaces are briefly discussed above. If m is a positive integer then  $u \in H^m(\mathbb{R}^n)$  'means' that u has up to m derivatives in  $L^2(\mathbb{R}^n)$ . The question naturally arises as to the sense in which these 'weak' derivatives correspond to old-fashioned 'strong' derivatives. Of course when m is not an integer it is a little harder to imagine what these 'fractional derivatives' are. However the main result is:

**Theorem 10.1** (Sobolev embedding). If  $u \in H^m(\mathbb{R}^n)$  where m > n/2 then  $u \in \mathcal{C}_0^0(\mathbb{R}^n)$ , i.e.,

(10.1) 
$$H^m(\mathbb{R}^n) \subset \mathcal{C}_0^0(\mathbb{R}^n), \ m > n/2.$$

*Proof.* By definition,  $u \in H^m(\mathbb{R}^n)$  means  $v \in \mathcal{S}'(\mathbb{R}^n)$  and  $\langle \xi \rangle^m \hat{u}(\xi) \in L^2(\mathbb{R}^n)$ . Suppose first that  $u \in \mathcal{S}(\mathbb{R}^n)$ . The Fourier inversion formula shows that

$$(2\pi)^n |u(x)| = \left| \int e^{ix \cdot \xi} \hat{u}(\xi) d\xi \right|$$

$$\leq \left( \int_{\mathbb{R}^n} \langle \xi \rangle^{2m} |\hat{u}(\xi)|^2 d\xi \right)^{1/2} \cdot \left( \sum_{\mathbb{R}^n} \langle \xi \rangle^{-2m} d\xi \right)^{1/2}.$$

Now, if m > n/2 then the second integral is finite. Since the first integral is the norm on  $H^m(\mathbb{R}^n)$  we see that

(10.2) 
$$\sup_{\mathbb{P}^n} |u(x)| = ||u||_{L^{\infty}} \le (2\pi)^{-n} ||u||_{H^m}, \, m > n/2.$$

This is all for  $u \in \mathcal{S}(\mathbb{R}^n)$ , but  $\mathcal{S}(\mathbb{R}^n) \hookrightarrow H^m(\mathbb{R}^n)$  is dense. The estimate (10.2) shows that if  $u_j \to u$  in  $H^m(\mathbb{R}^n)$ , with  $u_j \in \mathcal{S}(\mathbb{R}^n)$ , then  $u_j \to u'$  in  $C_0^0(\mathbb{R}^n)$ . In fact u' = u in  $\mathcal{S}'(\mathbb{R}^n)$  since  $u_j \to u$  in  $L^2(\mathbb{R}^n)$  and  $u_j \to u'$  in  $C_0^0(\mathbb{R}^n)$  both imply that  $\int u_j \varphi$  converges, so

$$\int_{\mathbb{R}^n} u_j \varphi \to \int_{\mathbb{R}^n} u \varphi = \int_{\mathbb{R}^n} u' \varphi \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

Notice here the precise meaning of u = u',  $u \in H^m(\mathbb{R}^n) \subset L^2(\mathbb{R}^n)$ ,  $u' \in \mathcal{C}_0^0(\mathbb{R}^n)$ . When identifying  $u \in L^2(\mathbb{R}^n)$  with the corresponding tempered distribution, the values on any set of measure zero 'are lost'. Thus as functions (10.1) means that each  $u \in H^m(\mathbb{R}^n)$  has a representative  $u' \in \mathcal{C}_0^0(\mathbb{R}^n)$ .

We can extend this to higher derivatives by noting that

**Proposition 10.2.** If  $u \in H^m(\mathbb{R}^n)$ ,  $m \in \mathbb{R}$ , then  $D^{\alpha}u \in H^{m-|\alpha|}(\mathbb{R}^n)$  and

(10.3) 
$$D^{\alpha}: H^{m}(\mathbb{R}^{n}) \to H^{m-|\alpha|}(\mathbb{R}^{n})$$

is continuous.

*Proof.* First it is enough to show that each  $D_j$  defines a continuous linear map

(10.4) 
$$D_j: H^m(\mathbb{R}^n) \to H^{m-1}(\mathbb{R}^n) \ \forall \ j$$

since then (10.3) follows by composition.

If  $m \in \mathbb{R}$  then  $u \in H^m(\mathbb{R}^n)$  means  $\hat{u} \in \langle \xi \rangle^{-m} L^2(\mathbb{R}^n)$ . Since  $\widehat{D_j u} = \xi_j \cdot \hat{u}$ , and

$$|\xi_j| \langle \xi \rangle^{-m} \le C_m \langle \xi \rangle^{-m+1} \ \forall \ m$$

we conclude that  $D_i u \in H^{m-1}(\mathbb{R}^n)$  and

$$||D_j u||_{H^{m-1}} \le C_m ||u||_{H^m} .$$

Applying this result we see

Corollary 10.3. If  $k \in \mathbb{N}_0$  and  $m > \frac{n}{2} + k$  then

(10.5) 
$$H^m(\mathbb{R}^n) \subset \mathcal{C}_0^k(\mathbb{R}^n).$$

Proof. If  $|\alpha| \leq k$ , then  $D^{\alpha}u \in H^{m-k}(\mathbb{R}^n) \subset \mathcal{C}_0^0(\mathbb{R}^n)$ . Thus the 'weak derivatives'  $D^{\alpha}u$  are continuous. Still we have to check that this means that u is itself k times continuously differentiable. In fact this again follows from the density of  $\mathcal{S}(\mathbb{R}^n)$  in  $H^m(\mathbb{R}^n)$ . The continuity in (10.3) implies that if  $u_j \to u$  in  $H^m(\mathbb{R}^n)$ ,  $m > \frac{n}{2} + k$ , then  $u_j \to u'$  in  $\mathcal{C}_0^k(\mathbb{R}^n)$  (using its completeness). However u = u' as before, so  $u \in \mathcal{C}_0^k(\mathbb{R}^n)$ .

In particular we see that

(10.6) 
$$H^{\infty}(\mathbb{R}^n) = \bigcap_{m} H^m(\mathbb{R}^n) \subset \mathcal{C}^{\infty}(\mathbb{R}^n).$$

These functions are not in general Schwartz test functions.

**Proposition 10.4.** Schwartz space can be written in terms of weighted Sobolev spaces

(10.7) 
$$\mathcal{S}(\mathbb{R}^n) = \bigcap_k \langle x \rangle^{-k} H^k(\mathbb{R}^n) .$$

*Proof.* This follows directly from (10.5) since the left side is contained in

$$\bigcap_{k} \langle x \rangle^{-k} \mathcal{C}_0^{k-n}(\mathbb{R}^n) \subset \mathcal{S}(\mathbb{R}^n).$$

**Theorem 10.5** (Schwartz representation). Any tempered distribution can be written in the form of a finite sum

(10.8) 
$$u = \sum_{\substack{|\alpha| \le m \\ |\beta| \le m}} x^{\alpha} D_x^{\beta} u_{\alpha\beta}, \ u_{\alpha\beta} \in \mathcal{C}_0^0(\mathbb{R}^n).$$

or in the form

(10.9) 
$$u = \sum_{\substack{|\alpha| \le m \\ |\beta| \le m}} D_x^{\beta}(x^{\alpha}v_{\alpha\beta}), \ v_{\alpha\beta} \in \mathcal{C}_0^0(\mathbb{R}^n).$$

Thus every tempered distribution is a finite sum of derivatives of continuous functions of poynomial growth.

*Proof.* Essentially by definition any  $u \in \mathcal{S}'(\mathbb{R}^n)$  is continuous with respect to *one* of the norms  $\|\langle x \rangle^k \varphi\|_{\mathcal{C}^k}$ . From the Sobolev embedding theorem we deduce that, with m > k + n/2,

$$|u(\varphi)| \le C ||\langle x \rangle^k \varphi||_{H^m} \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

This is the same as

$$\left|\langle x\rangle^{-k}u(\varphi)\right| \leq C\|\varphi\|_{H^m} \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

which shows that  $\langle x \rangle^{-k} u \in H^{-m}(\mathbb{R}^n)$ , i.e., from Proposition 9.8,

$$\langle x \rangle^{-k} u = \sum_{|\alpha| \le m} D^{\alpha} u_{\alpha} \,, \ u_{\alpha} \in L^{2}(\mathbb{R}^{n}) \,.$$

In fact, choose j > n/2 and consider  $v_{\alpha} \in H^{j}(\mathbb{R}^{n})$  defined by  $\hat{v}_{\alpha} = \langle \xi \rangle^{-j} \hat{u}_{\alpha}$ . As in the proof of Proposition 9.14 we conclude that

$$u_{\alpha} = \sum_{|\beta| \le j} D^{\beta} u'_{\alpha,\beta}, \ u'_{\alpha,\beta} \in H^{j}(\mathbb{R}^{n}) \subset \mathcal{C}^{0}_{0}(\mathbb{R}^{n}).$$

Thus,<sup>17</sup>

(10.10) 
$$u = \langle x \rangle^k \sum_{|\gamma| < M} D_{\alpha}^{\gamma} v_{\gamma} , \ v_{\gamma} \in \mathcal{C}_0^0(\mathbb{R}^n) .$$

To get (10.9) we 'commute' the factor  $\langle x \rangle^k$  to the inside; since I have not done such an argument carefully so far, let me do it as a lemma.

<sup>&</sup>lt;sup>17</sup>This is probably the most useful form of the representation theorem!

**Lemma 10.6.** For any  $\gamma \in \mathbb{N}_0^n$  there are polynomials  $p_{\alpha,\gamma}(x)$  of degrees at most  $|\gamma - \alpha|$  such that

$$\langle x \rangle^k D^{\gamma} v = \sum_{\alpha < \gamma} D^{\gamma - \alpha} \left( p_{\alpha, \gamma} \langle x \rangle^{k - 2|\gamma - \alpha|} v \right) .$$

*Proof.* In fact it is convenient to prove a more general result. Suppose p is a polynomial of a degree at most j then there exist polynomials of degrees at most  $j + |\gamma - \alpha|$  such that

(10.11) 
$$p\langle x\rangle^k D^{\gamma}v = \sum_{\alpha < \gamma} D^{\gamma - \alpha} (p_{\alpha, \gamma}\langle x\rangle^{k - 2|\gamma - \alpha|}v).$$

The lemma follows from this by taking p = 1.

Furthermore, the identity (10.11) is trivial when  $\gamma = 0$ , and proceeding by induction we can suppose it is known whenever  $|\gamma| \leq L$ . Taking  $|\gamma| = L + 1$ ,

$$D^{\gamma} = D_i D^{\gamma'} |\gamma'| = L.$$

Writing the identity for  $\gamma'$  as

$$p\langle x\rangle^k D^{\gamma'} = \sum_{\alpha' \le \gamma'} D^{\gamma' - \alpha'} (p_{\alpha', \gamma'} \langle x\rangle^{k - 2|\gamma' - \alpha'|} v)$$

we may differentiate with respect to  $x_i$ . This gives

$$p\langle x\rangle^k D^{\gamma} = -D_j(p\langle x\rangle^k) \cdot D^{\gamma'} v + \sum_{|\alpha'| \le \gamma} D^{\gamma - \alpha'}(p'_{\alpha', \gamma'}\langle x\rangle^{k - 2|\gamma - \alpha| + 2} v).$$

The first term on the right expands to

$$\left(-(D_j p) \cdot \langle x \rangle^k D^{\gamma'} v - \frac{1}{i} k p x_j \langle x \rangle^{k-2} D^{\gamma'} v\right).$$

We may apply the inductive hypothesis to each of these terms and rewrite the result in the form (10.11); it is only necessary to check the order of the polynomials, and recall that  $\langle x \rangle^2$  is a polynomial of degree 2.

Applying Lemma 10.6 to (10.10) gives (10.9), once negative powers of  $\langle x \rangle$  are absorbed into the continuous functions. Then (10.8) follows from (10.9) and Leibniz's formula.

### 11. Differential operators.

In the last third of the course we will apply what we have learned about distributions, and a little more, to understand properties of differential operators with constant coefficients. Before I start talking about these, I want to prove another density result.

So far we have *not* defined a topology on  $\mathcal{S}'(\mathbb{R}^n)$  – I will leave this as an optional exercise.<sup>18</sup> However we shall consider a notion of convergence. Suppose  $u_j \in \mathcal{S}'(\mathbb{R}^n)$  is a sequence in  $\mathcal{S}'(\mathbb{R}^n)$ . It is said to converge weakly to  $u \in \mathcal{S}'(\mathbb{R}^n)$  if

(11.1) 
$$u_i(\varphi) \to u(\varphi) \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^n).$$

There is no 'uniformity' assumed here, it is rather like pointwise convergence (except the linearity of the functions makes it seem stronger).

**Proposition 11.1.** The subspace  $S(\mathbb{R}^n) \subset S'(\mathbb{R}^n)$  is weakly dense, i.e., each  $u \in S'(\mathbb{R}^n)$  is the weak limit of a subspace  $u_j \in S(\mathbb{R}^n)$ .

*Proof.* We can use Schwartz representation theorem to write, for some m depending on u,

$$u = \langle x \rangle^m \sum_{|\alpha| \le m} D^{\alpha} u_{\alpha}, \ u_{\alpha} \in L^2(\mathbb{R}^n).$$

We know that  $\mathcal{S}(\mathbb{R}^n)$  is dense in  $L^2(\mathbb{R}^n)$ , in the sense of metric spaces so we can find  $u_{\alpha,j} \in \mathcal{S}(\mathbb{R}^n)$ ,  $u_{\alpha,j} \to u_{\alpha}$  in  $L^2(\mathbb{R}^n)$ . The density result then follows from the basic properties of weak convergence.

**Proposition 11.2.** If  $u_j \to u$  and  $u'_j \to u'$  weakly in  $\mathcal{S}'(\mathbb{R}^n)$  then  $cu_j \to cu$ ,  $u_j + u'_j \to u + u'$ ,  $D^{\alpha}u_j \to D^{\alpha}u$  and  $\langle x \rangle^m u_j \to \langle x \rangle^m u$  weakly in  $\mathcal{S}'(\mathbb{R}^n)$ .

*Proof.* This follows by writing everyting in terms of pairings, for example if  $\varphi \in \mathcal{S}(\mathbb{R}^n)$ 

$$D^{\alpha}u_{j}(\varphi) = u_{j}((-1)^{(\alpha)}D^{\alpha}\varphi) \to u((-1)^{(\alpha)}D^{\alpha}\varphi) = D^{\alpha}u(\varphi).$$

This weak density shows that our definition of  $D_j$ , and  $x_j \times$  are unique if we require Proposition 11.2 to hold.

We have discussed differentiation as an operator (meaning just a linear map between spaces of function-like objects)

$$D_i: \mathcal{S}'(\mathbb{R}^n) \to \mathcal{S}'(\mathbb{R}^n)$$
.

 $<sup>^{18}</sup>$ Problem 34.

Any polynomial on  $\mathbb{R}^n$ 

$$p(\xi) = \sum_{|\alpha| \le m} p_{\alpha} \xi^{\alpha} \,, \ p_{\alpha} \in \mathbb{C}$$

defines a differential operator<sup>19</sup>

(11.2) 
$$p(D)u = \sum_{|\alpha| \le m} p_{\alpha} D^{\alpha} u.$$

Before discussing any general theorems let me consider some examples.

(11.3) On 
$$\mathbb{R}^2$$
,  $\overline{\partial} = \partial_x + i\partial_y$  "d-bar operator"

(11.4) on 
$$\mathbb{R}^n$$
,  $\Delta = \sum_{j=1}^n D_j^2$  "Laplacian"

(11.5) on 
$$\mathbb{R} \times \mathbb{R}^n = \mathbb{R}^{n+1}$$
,  $D_t^2 - \Delta$  "Wave operator"

(11.6) on 
$$\mathbb{R} \times \mathbb{R}^n = \mathbb{R}^{n+1}$$
,  $\partial_t + \Delta$  "Heat operator"

(11.7) on 
$$\mathbb{R} \times \mathbb{R}^n = \mathbb{R}^{n+1}$$
,  $D_t + \Delta$  "Schrödinger operator"

Functions, or distributions, satisfying  $\overline{\partial}u = 0$  are said to be holomorphic, those satisfying  $\Delta u = 0$  are said to be harmonic.

**Definition 11.3.** An element  $E \in \mathcal{S}'(\mathbb{R}^n)$  satisfying

$$(11.8) P(D)E = \delta$$

is said to be a (tempered) fundamental solution of P(D).

**Theorem 11.4** (without proof). Every non-zero constant coefficient differential operator has a tempered fundamental solution.

This is quite hard to prove and not as interesting as it might seem. We will however give lots of examples, starting with  $\overline{\partial}$ . Consider the function

(11.9) 
$$E(x,y) = \frac{1}{2\pi} (x+iy)^{-1}, \ (x,y) \neq 0.$$

**Lemma 11.5.** E(x,y) is locally integrable and so defines  $E \in \mathcal{S}'(\mathbb{R}^2)$  by

(11.10) 
$$E(\varphi) = \frac{1}{2\pi} \int_{\mathbb{R}^2} (x+iy)^{-1} \varphi(x,y) \, dx \, dy,$$

and E so defined is a tempered fundamental solution of  $\overline{\partial}$ .

<sup>&</sup>lt;sup>19</sup>More correctly a partial differential operator with constant coefficients.

*Proof.* Since  $(x+iy)^{-1}$  is smooth and bounded away from the origin the local integrability follows from the estimate, using polar coordinates,

(11.11) 
$$\int_{|(x,y)|<1} \frac{dx \, dy}{|x+iy|} = \int_0^{2\pi} \int_0^1 \frac{r \, dr \, d\theta}{r} = 2\pi \, .$$

Differentiating directly in the region where it is smooth,

$$\partial_x (x+iy)^{-1} = -(x+iy)^{-2}, \ \partial_y (x+iy)^{-1} = -i(x \in iy)^{-2}$$

so indeed,  $\overline{\partial}E = 0$  in  $(x, y) \neq 0$ .<sup>20</sup>

The derivative is *really* defined by

(11.12) 
$$(\overline{\partial}E)(\varphi) = E(-\overline{\partial}\varphi)$$

$$= \lim_{\epsilon \downarrow 0} -\frac{1}{2\pi} \int_{\substack{|x| \ge \epsilon \\ |y| \ge \epsilon}} (x+iy)^{-1} \overline{\partial}\varphi \, dx \, dy.$$

Here I have cut the space  $\{|x| \leq \epsilon, |y| \leq \epsilon\}$  out of the integral and used the local integrability in taking the limit as  $\epsilon \downarrow 0$ . Integrating by parts in x we find

$$-\int_{\substack{|x|\geq\epsilon\\|y|\geq\epsilon}} (x+iy)^{-1} \partial_x \varphi \, dx \, dy = \int_{\substack{|x|\geq\epsilon\\|y|\geq\epsilon}} (\partial_x (x+iy)^{-1}) \varphi \, dx \, dy$$
$$+\int_{\substack{|y|\leq\epsilon\\x=-\epsilon}} (x+iy)^{-1} \varphi(x,y) \, dy - \int_{\substack{|y|\leq\epsilon\\x=-\epsilon}} (x+iy)^{-1} \varphi(x,y) \, dy.$$

There is a corrsponding formula for integration by parts in y so, recalling that  $\overline{\partial}E = 0$  away from (0,0),

$$(11.13) \quad 2\pi \overline{\partial} E(\varphi) = \lim_{\epsilon \downarrow 0} \int_{|y| \le \epsilon} \left[ (\epsilon + iy)^{-1} \varphi(\epsilon, y) - (-\epsilon + iy)^{-1} \varphi(-\epsilon, y) \right] dy + i \lim_{\epsilon \downarrow 0} \int_{|x| \le \epsilon} \left[ (x + i\epsilon)^{-1} \varphi(x, \epsilon) - (x - i\epsilon)^{-1} \varphi(x, \epsilon) \right] dx,$$

assuming that both limits exist. Now, we can write

$$\varphi(x,y) = \varphi(0,0) + x\psi_1(x_1y) + y\psi_2(x,y)$$
.

Replacing  $\varphi$  by either  $x\psi_1$  or  $y\psi_2$  in (11.13) both limits are zero. For example

$$\left| \int_{|y| \le \epsilon} (\epsilon + iy)^{-1} \epsilon \psi_1(\epsilon, y) \, dy \right| \le \int_{|y| \le \epsilon} |\psi_1| \to 0.$$

<sup>&</sup>lt;sup>20</sup>Thus at this stage we know  $\overline{\partial}E$  must be a sum of derivatives of  $\delta$ .

Thus we get the same result in (11.13) by replacing  $\varphi(x,y)$  by  $\varphi(0,0)$ . Then  $2\pi \overline{\partial} E(\varphi) = c\varphi(0)$ ,

$$c = \lim_{\epsilon \downarrow 0} 2\epsilon \int_{|y| \le \epsilon} \frac{dy}{\epsilon^2 + y^2} = \lim_{\epsilon \downarrow 0} < \int_{|y| \le 1} \frac{dy}{1 + y^2} = 2\pi.$$

Let me remind you that we have already discussed the convolution of functions

$$u * v(x) = \int u(x - y)v(y) dy = v * u(x).$$

This makes sense provided u is of slow growth and  $s \in \mathcal{S}(\mathbb{R}^n)$ . In fact we can rewrite the definition in terms of pairing

$$(11.14) (u * \varphi)(x) = \langle u, \varphi(x - \cdot) \rangle$$

where the  $\cdot$  indicates the variable in the pairing.

**Theorem 11.6** (Hörmander, Theorem 4.1.1). If  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  then  $u * \varphi \in \mathcal{S}'(\mathbb{R}^n) \cap \mathcal{C}^{\infty}(\mathbb{R}^n)$  and if  $\operatorname{supp}(\varphi) \subseteq \mathbb{R}^n$ 

$$\operatorname{supp}(u * \varphi) \subset \operatorname{supp}(u) + \operatorname{supp}(\varphi).$$

For any multi-index  $\alpha$ 

$$D^{\alpha}(u * \varphi) = D^{\alpha}u * \varphi = u * D^{\alpha}\varphi.$$

*Proof.* If  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  then for any fixed  $x \in \mathbb{R}^n$ ,

$$\varphi(x-\cdot)\in\mathcal{S}(\mathbb{R}^n)$$
.

Indeed the seminorm estimates required are

$$\sup_{y} (1 + |y|^2)^{k/2} |D^{\alpha}{}_{y}\varphi(x - y)| < \infty \ \forall \ \alpha, k > 0.$$

Since 
$$D^{\alpha}{}_{y}\varphi(x-y)=(-1)^{|\alpha|}(D^{\alpha}\varphi)(x-y)$$
 and

$$(1 + |y|^2) \le (1 + |x - y|^2)(1 + |x|^2)$$

we conclude that

$$\|(1+|y|^2)^{k/2}D^{\alpha}{}_{y}(x-y)\|_{L^{\infty}} \leq (1+|x|^2)^{k/2}\|\langle y\rangle^k D^{\alpha}{}_{y}\varphi(y)\|_{L^{\infty}}.$$

The continuity of  $u \in \mathcal{S}'(\mathbb{R}^n)$  means that for some k

$$|u(\varphi)| \le C \sup_{|\alpha| \le k} \|(y)^k D^{\alpha} \varphi\|_{L^{\infty}}$$

so it follows that

$$(11.15) |u * \varphi(x)| = |\langle u, \varphi(x - \cdot) \rangle| \le C(1 + |x|^2)^{k/2}.$$

The argument above shows that  $x \mapsto \varphi(x-\cdot)$  is a continuous function of  $x \in \mathbb{R}^n$  with values in  $\mathcal{S}(\mathbb{R}^n)$ , so  $u * \varphi$  is continuous and satisfies (11.15). It is therefore an element of  $\mathcal{S}'(\mathbb{R}^n)$ .

Differentiability follows in the same way since for each j, with  $e_j$  the jth unit vector

$$\frac{\varphi(x+se_j-y)-\varphi(x-y)}{s}\in\mathcal{S}(\mathbb{R}^n)$$

is continuous in  $x \in \mathbb{R}^n$ ,  $s \in \mathbb{R}$ . Thus,  $u * \varphi$  has continuous partial derivatives and

$$D_j u * \varphi = u * D_j \varphi.$$

The same argument then shows that  $u*\varphi \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ . That  $D_j(u*\varphi) = D_j u * \varphi$  follows from the definition of derivative of distributions

$$D_{j}(u * \varphi(x)) = (u * D_{j}\varphi)(x)$$

$$= \langle u, D_{x_{j}}\varphi(x - y)\rangle = -\langle u(y), D_{y_{j}}\varphi(x - y)\rangle_{y}$$

$$= (D_{j}u) * \varphi.$$

Finally consider the support property. Here we are assuming that  $\operatorname{supp}(\varphi)$  is compact; we also know that  $\operatorname{supp}(u)$  is a closed set. We have to show that

(11.16) 
$$\overline{x} \notin \operatorname{supp}(u) + \operatorname{supp}(\varphi)$$

implies  $u * \varphi(x') = 0$  for x' near  $\overline{x}$ . Now (11.16) just means that

(11.17) 
$$\operatorname{supp} \varphi(\overline{x} - \cdot) \cap \operatorname{supp}(u) = \phi,$$

Since supp  $\varphi(x-\cdot)=\{y\in\mathbb{R}^n;x-y\in\operatorname{supp}(\varphi)\}$ , so both statements mean that there is  $no\ y\in\operatorname{supp}(\varphi)$  with  $\overline{x}-y\in\operatorname{supp}(u)$ . This can also be written

$$\operatorname{supp}(\varphi) \cap \operatorname{supp} u(x - \cdot) = \phi$$

and as we showed when discussing supports implies

$$u * \varphi(x') = \langle u(x' - \cdot), \varphi \rangle = 0.$$

From (11.17) this is an *open* condition on x', so the support property follows.

Now suppose  $\varphi, \psi \in \mathcal{S}(\mathbb{R}^n)$  and  $u \in \mathcal{S}'(\mathbb{R}^n)$ . Then

$$(11.18) \qquad (u * \varphi) * \psi = u * (\varphi * \psi).$$

This is really Hörmander's Lemma 4.1.3 and Theorem 4.1.2; I ask you to prove it as Problem 35.

We have shown that  $u * \varphi$  is  $\mathcal{C}^{\infty}$  if  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $\varphi \in \mathcal{S}(\mathbb{R}^n)$ , i.e., the regularity of  $u * \varphi$  follows from the regularity of one of the

factors. This makes it reasonable to expect that u \* v can be defined when  $u \in \mathcal{S}'(\mathbb{R}^n)$ ,  $v \in \mathcal{S}'(\mathbb{R}^n)$  and one of them has compact support. If  $v \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  and  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  then

$$u * v(\varphi) = \int \langle u(\cdot), v(x - \cdot) \rangle \varphi(x) \, dx = \int \langle u(\cdot), v(x - \cdot) \rangle \check{v} \varphi(-x) \, dx$$

where  $\dot{\varphi}(z) = \varphi(-z)$ . In fact using Problem 35,

(11.19) 
$$u * v(\varphi) = ((u * v) * \check{\varphi})(0) = (u * (v * \check{\varphi}))(0).$$

Here,  $v, \varphi$  are both smooth, but notice

**Lemma 11.7.** If  $v \in \mathcal{S}'(\mathbb{R}^n)$  has compact support and  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  then  $v * \varphi \in \mathcal{S}(\mathbb{R}^n)$ .

*Proof.* Since  $v \in \mathcal{S}'(\mathbb{R}^n)$  has compact support there exists  $\chi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  such that  $\chi v = v$ . Then

$$v * \varphi(x) = (\chi v) * \varphi(x) = \langle \chi v(y), \varphi(x - y) \rangle_y$$
$$= \langle u(y), \chi(y)\varphi(x - y) \rangle_y.$$

Thus, for some k,

$$|v * \varphi(x)| \le C \|\chi(y)\varphi(x - y)\|_{(k)}$$

where  $\| \|_{(k)}$  is one of our norms on  $\mathcal{S}(\mathbb{R}^n)$ . Since  $\chi$  is supported in some large ball,

$$\|\chi(y)\varphi(x-y)\|_{(k)} \le \sup_{|\alpha| \le k} |\langle y \rangle^k D^{\alpha}{}_y(\chi(y)\varphi(x-y))|$$

$$\le C \sup_{|y| \le R} \sup_{|\alpha| \le k} |(D^{\alpha}\varphi)(x-y)|$$

$$\le C_N \sup_{|y| \le R} (1+|x-y|^2)^{-N/2}$$

$$\le C_N(1+|x|^2)^{-N/2}.$$

Thus  $(1 + |x|^2)^{N/2} |v * \varphi|$  is bounded for each N. The same argument applies to the derivative using Theorem 11.6, so

$$v * \varphi \in \mathcal{S}(\mathbb{R}^n)$$
.

In fact we get a little more, since we see that for each k there exists k' and C (depending on k and v) such that

$$||v * \varphi||_{(k)} \le C||\varphi||_{(k')}.$$

This means that

$$v*: \mathcal{S}(\mathbb{R}^n) \to \mathcal{S}(\mathbb{R}^n)$$

is a continuous linear map.

Now (11.19) allows us to define u\*v when  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $v \in \mathcal{S}'(\mathbb{R}^n)$  has compact support by

$$u * v(\varphi) = u * (v * \check{\varphi})(0).$$

Using the continuity above, I ask you to check that  $u * v \in \mathcal{S}'(\mathbb{R}^n)$  in Problem 36. For the moment let me assume that this convolution has the same properties as before – I ask you to check the main parts of this in Problem 37.

Recall that  $E \in \mathcal{S}'(\mathbb{R}^n)$  is a fundamental situation for P(D), a constant coefficient differential operator, if  $P(D)E = \delta$ . We also use a weaker notion.

**Definition 11.8.** A parametrix for a constant coefficient differential operator P(D) is a distribution  $F \in \mathcal{S}'(\mathbb{R}^n)$  such that

(11.20) 
$$P(D)F = \delta + \psi, \ \psi \in \mathcal{C}^{\infty}(\mathbb{R}^n).$$

An operator P(D) is said to be hypoelliptic if it has a parametrix satisfying

$$(11.21) \qquad \operatorname{sing} \operatorname{supp}(F) \subset \{0\} ,$$

where for any  $u \in \mathcal{S}'(\mathbb{R}^n)$ 

(11.22) 
$$(\operatorname{sing supp}(u))^{\mathbf{c}} = \{ \overline{x} \in \mathbb{R}^n ; \exists \varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n) , \varphi(\overline{x}) \neq 0, \varphi u \in \mathcal{C}_c^{\infty}(\mathbb{R}^n) \} .$$

Since the same  $\varphi$  must work for nearby points in (11.22), the set sing supp(u) is *closed*. Furthermore

(11.23) 
$$\operatorname{sing} \operatorname{supp}(u) \subset \operatorname{supp}(u).$$

As Problem 37 I ask you to show that if  $K \in \mathbb{R}^n$  and  $K \cap \text{sing supp}(u) = \phi$  the  $\exists \varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $\varphi(x) = 1$  in a neighbourhood of K such that  $\varphi u \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ . In particular

(11.24) 
$$\operatorname{sing supp}(u) = \phi \Rightarrow u \in \mathcal{S}'(\mathbb{R}^n) \cap \mathcal{C}^{\infty}(\mathbb{R}^n).$$

**Theorem 11.9.** If P(D) is hypoelliptic then

(11.25) 
$$\operatorname{sing supp}(u) = \operatorname{sing supp}(P(D)u) \ \forall \ u \in \mathcal{S}'(\mathbb{R}^n).$$

*Proof.* One half of this is true for any differential operator:

**Lemma 11.10.** If  $u \in \mathcal{S}'(\mathbb{R}^n)$  then for any polynomial

(11.26) 
$$\operatorname{sing supp}(P(D)u) \subset \operatorname{sing supp}(u) \ \forall \ u \in \mathcal{S}'(\mathbb{R}^n).$$

*Proof.* We must show that  $\overline{x} \notin \operatorname{sing supp}(u) \Rightarrow \overline{x} \notin \operatorname{sing supp}(P(D)u)$ . Now, if  $\overline{x} \notin \operatorname{sing\,supp}(u)$  we can find  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ ,  $\varphi \equiv 1$  near  $\overline{x}$ , such that  $\varphi u \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ . Then

$$P(D)u = P(D)(\varphi u + (1 - \varphi)u)$$
  
=  $P(D)(\varphi u) + P(D)((1 - \varphi)u)$ .

The first term is  $\mathcal{C}^{\infty}$  and  $\overline{x} \notin \operatorname{supp}(P(D)((1-\varphi)u))$ , so  $\overline{x} \notin \operatorname{sing supp}(P(D)u)$ .

It remains to show the converse of (11.26) where P(D) is assumed to be hypoelliptic. Take F, a parametrix for P(D) with sing supp  $u \subset \{0\}$ and assume, or rather arrange, that F have compact support. In fact if  $\overline{x} \notin \operatorname{sing\,supp}(P(D)u)$  we can arrange that

$$(\operatorname{supp}(F) + \overline{x}) \cap \operatorname{sing} \operatorname{supp}(P(D)u) = \phi.$$

Now  $P(D)F = \delta \psi$  with  $\psi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  so

$$u = \delta * u = (P(D)F) * u - \psi * u.$$

Since  $\psi * u \in \mathcal{C}^{\infty}$  it suffices to show that  $\bar{x} \notin \text{sing supp } ((P(D)u) * f)$ . Take  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $\varphi f \in \mathcal{C}^{\infty}$ , f = P(D)u but

$$(\operatorname{supp} F + \overline{x}) \cap \operatorname{supp}(\varphi) = 0.$$

Then  $f = f_1 + f_2$ ,  $f_1 = \varphi f \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  so

$$f * F = f_1 * F + f_2 * F$$

where  $f_1 * F \in \mathcal{C}^{\infty}(\mathbb{R}^n)$  and  $\overline{x} \notin \text{supp}(f_2 * F)$ . It follows that  $\overline{x} \notin$  $\operatorname{sing} \operatorname{supp}(u)$ .

Example 11.1. If u is holomorphic on  $\mathbb{R}^n$ ,  $\overline{\partial} u = 0$ , then  $u \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ .

Recall from last time that a differential operator P(D) is said to be hypoelliptic if there exists  $F \in \mathcal{S}'(\mathbb{R}^n)$  with

(11.27) 
$$P(D)F - \delta \in \mathcal{C}^{\infty}(\mathbb{R}^n) \text{ and } \operatorname{sing} \operatorname{supp}(F) \subset \{0\} .$$

The second condition here means that if  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  and  $\varphi(x) = 1$  in  $|x| < \epsilon$  for some  $\epsilon > 0$  then  $(1-\varphi)F \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ . Since  $P(D)((1-\varphi)F) \in$  $\mathcal{C}^{\infty}(\mathbb{R}^n)$  we conclude that

$$P(D)(\varphi F) - \delta \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$$

and we may well suppose that F, replaced now by  $\varphi F$ , has compact support. Last time I showed that

If 
$$P(D)$$
 is hypoelliptic and  $u \in \mathcal{S}'(\mathbb{R}^n)$  then

$$\operatorname{sing} \operatorname{supp}(u) = \operatorname{sing} \operatorname{supp}(P(D)u).$$

I will remind you of the proof later.

First however I want to discuss the important notion of *ellipticity*. Remember that P(D) is 'really' just a polynomial, called the *charac*teristic polynomial

$$P(\xi) = \sum_{|\alpha| \le m} C_{\alpha} \xi^{\alpha} .$$

It has the property

$$\widehat{P(D)u}(\xi) = P(\xi)\widehat{u}(\xi) \ \forall \ u \in \mathcal{S}'(\mathbb{R}^n).$$

This shows (if it isn't already obvious) that we can remove  $P(\xi)$  from P(D) thought of as an operator on  $\mathcal{S}'(\mathbb{R}^n)$ .

We can think of inverting P(D) by dividing by  $P(\xi)$ . This works well provided  $P(\xi) \neq 0$ , for all  $\xi \in \mathbb{R}^n$ . An example of this is

$$P(\xi) = |\xi|^2 + 1 = \sum_{j=1}^{n} +1.$$

However even the Laplacian,  $\Delta = \sum_{j=1}^{n} D_{j}^{2}$ , does not satisfy this rather stringent condition.

It is reasonable to expect the top order derivatives to be the most important. We therefore consider

$$P_m(\xi) = \sum_{|\alpha|=m} C_{\alpha} \xi^{\alpha}$$

the leading part, or principal symbol, of P(D).

**Definition 11.11.** A polynomial  $P(\xi)$ , or P(D), is said to be elliptic of order m provided  $P_m(\xi) \neq 0$  for all  $0 \neq \xi \in \mathbb{R}^n$ .

So what I want to show today is

**Theorem 11.12.** Every elliptic differential operator P(D) is hypoelliptic.

We want to find a parametrix for P(D); we already know that we might as well suppose that F has compact support. Taking the Fourier transform of (11.27) we see that  $\hat{F}$  should satisfy

(11.28) 
$$P(\xi)\widehat{F}(\xi) = 1 + \widehat{\psi}, \ \widehat{\psi} \in \mathcal{S}(\mathbb{R}^n).$$

Here we use the fact that  $\psi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n) \subset \mathcal{S}(\mathbb{R}^n)$ , so  $\widehat{\psi} \in \mathcal{S}(\mathbb{R}^n)$  too. First suppose that  $P(\xi) = P_m(\xi)$  is actually homogeneous of degree m. Thus

$$P_m(\xi) = |\xi|^m P_m(\hat{\xi}), \ \hat{\xi} = \xi/|\xi|, \ \xi \neq 0.$$

The assumption at ellipticity means that

(11.29) 
$$P_m(\hat{\xi}) \neq 0 \ \forall \ \hat{\xi} \in \mathcal{S}^{n-1} = \{ \xi \in \mathbb{R}^n; |\xi| = 1 \} \ .$$

Since  $S^{n-1}$  is *compact* and  $P_m$  is continuous

(11.30) 
$$\left| P_m(\widehat{\xi}) \right| \ge C > 0 \ \forall \ \widehat{\xi} \in \mathcal{S}^{n-1},$$

for some constant C. Using homogeneity

(11.31) 
$$\left| P_m(\widehat{\xi}) \right| \ge C \left| \xi \right|^m, C > 0 \ \forall \ \xi \in \mathbb{R}^n.$$

Now, to get  $\widehat{F}$  from (11.28) we want to divide by  $P_m(\xi)$  or multiply by  $1/P_m(\xi)$ . The only problem with defining  $1/P_m(\xi)$  is at  $\xi = 0$ . We shall simply avoid this unfortunate point by choosing  $P \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  as before, with  $\varphi(\xi) = 1$  in  $|\xi| \leq 1$ .

**Lemma 11.13.** If  $P_m(\xi)$  is homogeneous of degree m and elliptic then

(11.32) 
$$Q(\xi) = \frac{(1 - \varphi(\xi))}{P_m(\xi)} \in \mathcal{S}'(\mathbb{R}^n)$$

is the Fourier transform of a parametrix for  $P_m(D)$ , satisfying (11.27).

*Proof.* Clearly  $Q(\xi)$  is a continuous function and  $|Q(\xi)| \leq C(1+|\xi|)^{-m} \, \forall \, \xi \in \mathbb{R}^n$ , so  $Q \in \mathcal{S}'(\mathbb{R}^n)$ . It therefore is the Fourier transform of some  $F \in \mathcal{S}'(\mathbb{R}^n)$ . Furthermore

$$\widehat{P_m(D)}F(\xi) = P_m(\xi)\widehat{F} = P_m(\xi)Q(\xi)$$
$$= 1 - \varphi(\xi),$$
$$\Rightarrow P_m(D)F = \delta + \psi, \ \widehat{\psi}(\xi) = -\varphi(\xi).$$

Since  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n) \subset \mathcal{S}(\mathbb{R}^n)$ ,  $\psi \in \mathcal{S}(\mathbb{R}^n) \subset \mathcal{C}^{\infty}(\mathbb{R}^n)$ . Thus F is a parametrix for  $P_m(D)$ . We still need to show the 'hard part' that

$$(11.33) \qquad \qquad \operatorname{sing} \operatorname{supp}(F) \subset \{0\} \ .$$

We can show (11.33) by considering the distributions  $x^{\alpha}F$ . The idea is that for  $|\alpha|$  large,  $x^{\alpha}$  vanishes rather rapidly at the origin and this should 'weaken' the singularity of F there. In fact we shall show that

(11.34) 
$$x^{\alpha}F \in H^{|\alpha|+m-n-1}(\mathbb{R}^n), |\alpha| > n+1-m.$$

If you recall, these Sobolev spaces are defined in terms of the Fourier transform, namely we must show that

$$\widehat{x^{\alpha}F} \in \langle \xi \rangle^{-|\alpha|-m+n+1} L^2(\mathbb{R}^n)$$
.

Now  $\widehat{x^{\alpha}F} = (-1)^{|\alpha|} D^{\alpha}{}_{\xi}\widehat{F}$ , so what we need to cinsider is the behaviour of the derivatives of  $\widehat{F}$ , which is just  $Q(\xi)$  in (11.32).

**Lemma 11.14.** Let  $P(\xi)$  be a polynomial of degree m satisfying

$$(11.35) |P(\xi)| \ge C |\xi|^m in |\xi| > 1/C for some C > 0,$$

then for some constants  $C_{\alpha}$ 

(11.36) 
$$\left| D^{\alpha} \frac{1}{P(\xi)} \right| \le C_{\alpha} \left| \xi \right|^{-m - |\alpha|} \text{ in } |\xi| > 1/C.$$

*Proof.* The estimate in (11.36) for  $\alpha = 0$  is just (11.35). To prove the higher estimates that for each  $\alpha$  there is a polynomial of degree at most  $(m-1)|\alpha|$  such that

(11.37) 
$$D^{\alpha} \frac{1}{P(\xi)} = \frac{L_{\alpha}(\xi)}{(P(\xi))^{1+|\alpha|}}.$$

Once we know (11.37) we get (11.36) straight away since

$$\left| D^{\alpha} \frac{1}{P(\xi)} \right| \le \frac{C'_{\alpha} |\xi|^{(m-1)|\alpha|}}{C^{1+|\alpha|} |\xi|^{m(1+|\alpha|)}} \le C_{\alpha} |\xi|^{-m-|\alpha|}.$$

We can prove (11.37) by induction, since it is certainly true for  $\alpha = 0$ . Suppose it is true for  $|\alpha| \le k$ . To get the same identity for each  $\beta$  with  $|\beta| = k+1$  it is enough to differentiate one of the identities with  $|\alpha| = k$  once. Thus

$$D^{\beta} \frac{1}{P(\xi)} = D_j D^{\alpha} \frac{1}{P(\xi)} = \frac{D_j L_{\alpha}(\xi)}{P(\xi)^{1+|\alpha|}} - \frac{(1+|\alpha|)L_{\alpha}D_j P(\xi)}{(P(\xi))^{2+|\alpha|}}.$$

Since  $L_{\beta}(\xi) = P(\xi)D_{j}L_{\alpha}(\xi) - (1+|\alpha|)L_{\alpha}(\xi)D_{j}P(\xi)$  is a polynomial of degree at most  $(m-1)|\alpha| + m - 1 = (m-1)|\beta|$  this proves the lemma.

Going backwards, observe that  $Q(\xi) = \frac{1-\varphi}{P_m(\xi)}$  is smooth in  $|\xi| \leq 1/C$ , so (11.36) implies that

(11.38) 
$$|D^{\alpha}Q(\xi)| \leq C_{\alpha}(1+|\xi|)^{-m-|\alpha|}$$
$$\Rightarrow \langle \xi \rangle^{\ell} D^{\alpha} Q \in L^{2}(\mathbb{R}^{n}) \text{ if } \ell - m - |\alpha| < -\frac{n}{2},$$

which certainly holds if  $\ell = |\alpha| + m - n - 1$ , giving (11.34). Now, by Sobolev's embedding theorem

$$x^{\alpha}F \in \mathcal{C}^k \text{ if } |\alpha| > n+1-m+k+\frac{n}{2}.$$

In particular this means that if we choose  $\mu \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $0 \notin \operatorname{supp}(\mu)$  then for every k,  $\mu/|x|^{2k}$  is smooth and

$$\mu F = \frac{\mu}{|x|^{2k}} |x|^{2k} F \in \mathcal{C}^{2\ell-2n}, \ \ell > n.$$

Thus  $\mu F \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  and this is what we wanted to show, sing supp $(F) \subset \{0\}$ .

So now we have actually proved that  $P_m(D)$  is hypoelliptic if it is elliptic. Rather than go through the proof again to make sure, let me go on to the general case and in doing so review it.

*Proof. Proof of theorem.* We need to show that if  $P(\xi)$  is elliptic then P(D) has a parametrix F as in (11.27). From the discussion above the ellipticity of  $P(\xi)$  implies (and is equivalent to)

$$|P_m(\xi)| \ge c |\xi|^m, \ c > 0.$$

On the other hand

$$P(\xi) - P_m(\xi) = \sum_{|\alpha| < m} C_{\alpha} \xi^{\alpha}$$

is a polynomial of degree at most m-1, so

$$|P(\xi) - P_m(\xi)| 2 \le C'(1 + |\xi|)^{m-1}$$
.

This means that id C > 0 is large enough then in  $|\xi| > C$ ,  $C'(1 + |\xi|)^{m-1} < \frac{c}{2} |\xi|^m$ , so

$$|P(\xi)| \ge |P_m(\xi)| - |P(\xi) - P_m(\xi)|$$
  
  $\ge c |\xi|^m - C'(1 + |\xi|)^{m-1} \ge \frac{c}{2} |\xi|^m.$ 

This means that  $P(\xi)$  itself satisfies the conditions of Lemma 11.14. Thus if  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  is equal to 1 in a large enough ball then  $Q(xi) = (1 - \varphi(\xi))/P(\xi)$  in  $\mathcal{C}^{\infty}$  and satisfies (11.36) which can be written

$$|D^{\alpha}Q(\xi)| \le C_{\alpha}(1+|\xi|)^{m-|\alpha|}.$$

The discussion above now shows that defining  $F \in \mathcal{S}'(\mathbb{R}^n)$  by  $\widehat{F}(\xi) = Q(\xi)$  gives a solution to (11.27).

The last step in the proof is to show that if  $F \in \mathcal{S}'(\mathbb{R}^n)$  has compact support, and satisfies (11.27), then

$$u \in \mathcal{S}(\mathbb{R}^n), P(D)u \in \mathcal{S}'(\mathbb{R}^n) \cap \mathcal{C}^{\infty}(\mathbb{R}^n)$$
  
 $\Rightarrow u = F * (P(D)u) - \psi * u \in \mathcal{C}^{\infty}(\mathbb{R}^n).$ 

Let me refine this result a little bit.

**Proposition 11.15.** If  $f \in \mathcal{S}'(\mathbb{R}^n)$  and  $\mu \in \mathcal{S}'(\mathbb{R}^n)$  has compact support then

$$\operatorname{sing} \operatorname{supp}(u * f) \subset \operatorname{sing} \operatorname{supp}(u) + \operatorname{sing} \operatorname{supp}(f).$$

*Proof.* We need to show that  $p \notin \operatorname{sing supp}(u) \in \operatorname{sing supp}(f)$  then  $p \notin \operatorname{sing supp}(u * f)$ . Once we can fix p, we might as well suppose that f has compact support too. Indeed, choose a large ball B(R, 0) so that

$$z \notin B(0,R) \Rightarrow p \notin \text{supp}(u) + B(0,R)$$
.

This is possible by the assumed boundedness of  $\operatorname{supp}(u)$ . Then choose  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $\varphi = 1$  on B(0,R); it follows from Theorem L16.2, or rather its extension to distributions, that  $\phi \notin \operatorname{supp}(u(1-\varphi)f)$ , so we can replace f by  $\varphi f$ , noting that  $\operatorname{sing supp}(\varphi f) \subset \operatorname{sing supp}(f)$ . Now if f has compact support we can choose compact neighbourhoods  $K_1, K_2$  of  $\operatorname{sing supp}(u)$  and  $\operatorname{sing supp}(f)$  such that  $p \notin K_1 + K_2$ . Furthermore we an decompose  $u = u_1 + u_2, f = f_1 + f_2$  so that  $\operatorname{supp}(u_1) \subset K_1$ ,  $\operatorname{supp}(f_2) \subset K_2$  and  $u_2, f_2 \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ . It follows that

$$u * f = u_1 * f_1 + u_2 * f_2 + u_1 * f_2 + u_2 * f_2$$
.

Now,  $p \notin \text{supp}(u_1 * f_1)$ , by the support property of convolution and the three other terms are  $\mathcal{C}^{\infty}$ , since at least one of the factors is  $\mathcal{C}^{\infty}$ . Thus  $p \notin \text{sing supp}(u * f)$ .

The most important example of a differential operator which is hypoelliptic, but not elliptic, is the heat operator

(11.39) 
$$\partial_t + \Delta = \partial_t - \sum_{j=1}^n \partial_{x_j}^2.$$

In fact the distribution

(11.40) 
$$E(t,x) = \begin{cases} \frac{1}{(4\pi t)^{n/2}} \exp\left(-\frac{|x|^2}{4t}\right) & t \ge 0\\ 0 & t \le 0 \end{cases}$$

is a fundamental solution. First we need to check that E is a distribution. Certainly E is  $\mathcal{C}^{\infty}$  in t > 0. Moreover as  $t \downarrow 0$  in  $x \neq 0$  it vanishes with all derivatives, so it is  $\mathcal{C}^{\infty}$  except at t = 0, x = 0. Since it is clearly measurable we will check that it is locally integrable near the origin, i.e.,

(11.41) 
$$\int_{\substack{0 \le t \le 1 \\ |x| \le 1}} E(t, x) \, dx \, dt < \infty \,,$$

since  $E \ge 0$ . We can change variables, setting  $X = x/t^{1/2}$ , so  $dx = t^{n/2} dX$  and the integral becomes

$$\frac{1}{(4\pi)^{n/2}} \int_0^t \int_{|X| < t^{-1/2}} \exp(-\frac{|X|^2}{4}) \, dx \, dt < \infty.$$

Since E is actually bounded near infinity, it follows that  $E \in \mathcal{S}'\mathbb{R}^n$ ,

$$E(\varphi) = \int_{t>0} E(t, x)\varphi(t, x) dx dt \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}^{n+1}).$$

As before we want to compute

(11.42) 
$$(\partial_t + \Delta)E(\varphi) = E(-\partial_t \varphi + \Delta \varphi)$$

$$= \lim_{\mathcal{E}\downarrow 0} \int_{\mathcal{E}}^{\infty} \int_{\mathbb{R}^n} E(t, x)(-\partial_t \varphi + \Delta \varphi) \, dx \, dt \, .$$

First we check that  $(\partial_t + \Delta)E = 0$  in t > 0, where it is a  $\mathcal{C}^{\infty}$  function. This is a straightforward computation:

$$\partial_t E = -\frac{n}{2t}E + \frac{|x|^2}{4t^2}E$$

$$\partial_{x_j} E = -\frac{x_j}{2t}E, \ \partial_{x_j}^2 E = -\frac{1}{2t}E + \frac{x_j^2}{4t^2}E$$

$$\Rightarrow \Delta E = \frac{n}{2t}E + \frac{|x|^2}{4t^2}E.$$

Now we can integrate by parts in (11.42) to get

$$(\partial_t + \Delta)E(\varphi) = \lim_{\mathcal{E}\downarrow 0} \int_{\mathbb{R}^n} \varphi(\mathcal{E}, x) \frac{e^{-|x|^2/4\mathcal{E}}}{(4\pi\mathcal{E})^{n/2}} dx.$$

Making the same change of variables as before,  $X = x/2\mathcal{E}^{1/2}$ ,

$$(\partial_t + \Delta)E(\varphi) = \lim_{\mathcal{E}\downarrow 0} \int_{\mathbb{R}^n} \varphi(\mathcal{E}, \mathcal{E}^{1/2}X) \frac{e^{-|x|^2}}{\pi^{n/2}} dX.$$

As  $\mathcal{E} \downarrow 0$  the integral here is bounded by the integrable function  $C \exp(-|X|^2)$ , for some C > 0, so by Lebesgue's theorem of dominated convergence, conveys to the integral of the limit. This is

$$\varphi(0,0) \cdot \int_{\mathbb{R}^n} e^{-|x|^2} \frac{dx}{\pi^{n/2}} = \varphi(0,0) .$$

Thus

$$(\partial_t + \Delta)E(\varphi) = \varphi(0,0) \Rightarrow (\partial_t + \Delta)E = \delta_t \delta_x$$
,

so E is indeed a fundamental solution. Since it vanishes in t < 0 it is canned a forward fundamental solution.

Let's see what we can use it for.

**Proposition 11.16.** If  $f \in \mathcal{S}'\mathbb{R}^n$  has compact support  $\exists ! u \in \mathcal{S}'\mathbb{R}^n$  with  $\operatorname{supp}(m) \subset \{t \geq -T\}$  for some T and

$$(11.43) (\partial_t + \Delta)u = f \text{ in } \mathbb{R}^{n+1}.$$

*Proof.* Naturally we try u = E \* f. That it satisfies (11.43) follows from the properties of convolution. Similarly if T is such that  $\operatorname{supp}(f) \subset \{t \geq T\}$  then

$$\operatorname{supp}(u) \subset \operatorname{supp}(f) + \operatorname{supp}(E) \subset \{t \ge T \mid ...$$

So we need to show uniqueness. If  $u_1, u_2 \in \mathcal{S}'\mathbb{R}^n$  in two solutions of (11.43) then their difference  $v = u_1 - u_2$  satisfies the 'homogeneous' equation  $(\partial_t + \Delta)v = 0$ . Furthermore, v = 0 in t < T' for some T'. Given any  $E \in \mathbb{R}$  choose  $\varphi(t) \in \mathcal{C}^{\infty}(\mathbb{R})$  with  $\varphi(t) = 0$  in  $t > \overline{t} + 1$ ,  $\varphi(t) = 1$  in  $t < \overline{t}$  and consider

$$E_{\overline{t}} = \varphi(t)E = F_1 + F_2$$
,

where  $F_1 = \psi E_{\bar{t}}$  for some  $\psi \in \mathcal{C}_c^{\infty} \mathbb{R}^{n+1}$ ),  $\psi = 1$  near 0. Thus  $F_1$  has comapet support and in fact  $F_2 \in \mathcal{S}\mathbb{R}^n$ . I ask you to check this last statement as Problem L18.P1.

Anyway,

$$(\partial_t + \Delta)(F_1 + F_2) = \delta + \psi \in \mathcal{S}\mathbb{R}^n, \ \psi_{\overline{t}} = 0 \ t \le \overline{t}.$$

Now.

$$(\partial_t + \Delta)(E_t * u) = 0 = u + \psi_{\bar{t}} * u.$$

Since supp $(\psi_{\bar{t}}) \subset \{t \geq \bar{t}\}$ , the second tier here is supported in  $t \geq \bar{t} \geq T'$ . Thus u = 0 in  $t < \bar{t} + T'$ , but  $\bar{t}$  is arbitrary, so u = 0.

Notice that the assumption that  $u \in \mathcal{S}'\mathbb{R}^n$  is not redundant in the statement of the Proposition, if we allow "large" solutions they become non-unique. Problem L18.P2 asks you to apply the fundamental solution to solve the initial value problem for the heat operator.

Next we make similar use of the fundamental solution for Laplace's operator. If  $n \geq 3$  the

(11.44) 
$$E = C_n |x|^{-n+2}$$

is a fundamental solution. You should check that  $\Delta E_n = 0$  in  $x \neq 0$  directly, I will show later that  $\Delta E_n = \delta$ , for the appropriate choice of  $C_n$ , but you can do it directly, as in the case n = 3.

**Theorem 11.17.** If  $f \in S\mathbb{R}^n \exists ! u \in C_0^{\infty}\mathbb{R}^n$  such that  $\Delta u = f$ .

*Proof.* Since convolution  $u = E * f \in \mathcal{S}'\mathbb{R}^n \cap \mathcal{C}^{\infty}\mathbb{R}^n$  is defined we certainly get a solution to  $\Delta u = f$  this way. We need to check that  $u \in \mathcal{C}_0^{\infty}\mathbb{R}^n$ . First we know that  $\Delta$  is hypoelliptic so we can decompose

$$E = F_1 + F_2$$
,  $F_1 \in \mathcal{S}'\mathbb{R}^n$ , supp  $F \in \mathbb{R}^n$ 

and then  $F_2 \in \mathcal{C}^{\infty} \mathbb{R}^n$ . In fact we can see from (11.44) that

$$|D^{\alpha}F_2(x)| \le C_{\alpha}(1+|x|)^{-n+2-|\alpha|}$$
.

Now,  $F_1 * f \in \mathcal{S}\mathbb{R}^n$ , as we showed before, and continuing the integral we see that

$$|D^{\alpha}u| \le |D^{\alpha}F_2 * f| + C_N(1+|x|)^{-N} \ \forall \ N$$
  
$$\le C_{\alpha}'(1+|x|)^{-n+2-|\alpha|}.$$

Since n > 2 it follows that  $u \in \mathcal{C}_0^{\infty} \mathbb{R}^n$ .

So only the uniqueness remains. If there are two solutions,  $u_1, u_2$  for a given f then  $v = u_1 - u_2 \in \mathcal{C}_0^{\infty} \mathbb{R}^n$  satisfies  $\Delta v = 0$ . Since  $v \in \mathcal{S}' \mathbb{R}^n$  we can take the Fourier transform and see that

$$|\chi|^2 \widehat{v}(\chi) = 0 \Rightarrow \operatorname{supp}(\widehat{v}) \subset \{0\}$$
.

an earlier problem was to conclude from this that  $\widehat{v} = \sum_{|\alpha| \leq m} C_{\alpha} D^{\alpha} \delta$  for some constants  $C_{\alpha}$ . This in turn implies that v is a polynomial. However the only polynomials in  $\mathcal{C}_0^0 \mathbb{R}^n$  are identically 0. Thus v = 0 and uniqueness follows.

### 12. Cone support and wavefront set

In discussing the singular support of a tempered distibution above, notice that

$$\operatorname{singsupp}(u) = \emptyset$$

only implies that  $u \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ , not as one might want, that  $u \in \mathcal{S}(\mathbb{R}^n)$ . We can however 'refine' the concept of singular support a little to get this.

Let us think of the sphere  $\mathbb{S}^{n-1}$  as the set of 'asymptotic directions' in  $\mathbb{R}^n$ . That is, we identify a point in  $\mathbb{S}^{n-1}$  with a half-line  $\{a\bar{x}; a \in (0, \infty)\}$  for  $0 \neq \bar{x} \in \mathbb{R}^n$ . Since two points give the same half-line if and only if they are positive multiples of each other, this means we think of the sphere as the quotient

$$(12.1)$$

Of course if we have a metric on  $\mathbb{R}^n$ , for instance the usual Euclidean metric, then we can identify  $\mathbb{S}^{n-1}$  with the unit sphere. However (12.1) does not require a choice of metric.

Now, suppose we consider functions on  $\mathbb{R}^n \setminus \{0\}$  which are (positively) homogeneous of degree 0. That is  $f(a\bar{x}) = f(\bar{x})$ , for all a > 0, and they are just functions on  $\mathbb{S}^{n-1}$ . Smooth functions on  $\mathbb{S}^{n-1}$  correspond (if you like by definition) with smooth functions on  $\mathbb{R}^n \setminus \{0\}$  which are homogeneous of degree 0. Let us take such a function  $\psi \in \mathcal{C}^{\infty}(\mathbb{R}^n \setminus \{0\})$ ,  $\psi(ax) = \psi(x)$  for all a > 0. Now, to make this smooth on  $\mathbb{R}^n$  we need to cut it off near 0. So choose a cutoff function  $\chi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ , with  $\chi(x) = 1$  in |x| < 1. Then

(12.2) 
$$\psi_R(x) = \psi(x)(1 - \chi(x/R)) \in \mathcal{C}^{\infty}(\mathbb{R}^n),$$

for any R > 0. This function is supported in  $|x| \ge R$ . Now, if  $\psi$  has support near some point  $\omega \in \mathbb{S}^{n-1}$  then for R large the corresponding function  $\psi_R$  will 'localize near  $\omega$  as a point at infinity of  $\mathbb{R}^n$ .' Rather than try to understand this directly, let us consider a corresponding analytic construction.

First of all, a function of the form  $\psi_R$  is a multiplier on  $\mathcal{S}(\mathbb{R}^n)$ . That is,

(12.3) 
$$\psi_{R} : \mathcal{S}(\mathbb{R}^{n}) \longrightarrow \mathcal{S}(\mathbb{R}^{n}).$$

To see this, the main problem is to estimate the derivatives at infinity, since the product of smooth functions is smooth. This in turn amounts to estimating the derivatives of  $\psi$  in  $|x| \geq 1$ . This we can do using the homogeneity.

**Lemma 12.1.** If  $\psi \in C^{\infty}(\mathbb{R}^n \setminus \{0\})$  is homogeneous of degree 0 then

$$(12.4) |D^{\alpha}\psi| \le C_{\alpha}|x|^{-|\alpha|}.$$

*Proof.* I should not have even called this a lemma. By the chain rule, the derivative of order  $\alpha$  is a homogeneous function of degree  $-|\alpha|$  from which (12.4) follows.

For the smoothed versio,  $\psi_R$ , of  $\psi$  this gives the estimates

$$(12.5) |D^{\alpha}\psi_R(x)| \le C_{\alpha}\langle x \rangle^{-|\alpha|}.$$

This allows us to estimate the derivatives of the product of a Schwartz function and  $\psi_R$ :

$$(12.6) \quad x^{\beta} D^{\alpha}(\psi_R f)$$

$$= \sum_{\gamma \leq \alpha} {\alpha \choose \gamma} D^{\alpha - \gamma} \psi_R x^{\beta} D^{\gamma} f \Longrightarrow \sup_{|x| \geq 1} |x^{\beta} D^{\alpha}(\psi_R f)| \leq C \sup ||f||_k$$

for some seminorm on  $\mathcal{S}(\mathbb{R}^n)$ . Thus the map (12.3) is actually continuous. This continuity means that  $\psi_R$  is a multiplier on  $\mathcal{S}'(\mathbb{R}^n)$ , defined as usual by duality:

(12.7) 
$$\psi_R u(f) = u(\psi_R f) \ \forall \ f \in \mathcal{S}(\mathbb{R}^n).$$

**Definition 12.2.** The cone-support and cone-singular-support of a tempered distribution are the subsets  $Csp(u) \subset \mathbb{R}^n \cup \mathbb{S}^{n-1}$  and  $Css(u) \subset \mathbb{R}^n \cup \mathbb{S}^{n-1}$  defined by the conditions (12.8)

$$\operatorname{Csp}(u) \cap \mathbb{R}^{n} = \operatorname{supp}(u)$$

$$(\operatorname{Csp}(u))^{\complement} \cap \mathbb{S}^{n-1} = \{ \omega \in \mathbb{S}^{n-1}; \\ \exists R > 0, \ \psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1}), \ \psi(\omega) \neq 0, \ \psi_{R}u = 0 \},$$

$$\operatorname{Css}(u) \cap \mathbb{R}^{n} = \operatorname{singsupp}(u)$$

$$(\operatorname{Css}(u))^{\complement} \cap \mathbb{S}^{n-1} = \{ \omega \in \mathbb{S}^{n-1}; \\ \exists R > 0, \ \psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1}), \ \psi(\omega) \neq 0, \ \psi_{R}u \in \mathcal{S}(\mathbb{R}^{n}) \}.$$

That is, on the  $\mathbb{R}^n$  part these are the same sets as before but 'at infinity' they are defined by conic localization on  $\mathbb{S}^{n-1}$ .

In considering  $\operatorname{Csp}(u)$  and  $\operatorname{Css}(u)$  it is convenient to combine  $\mathbb{R}^n$  and  $\mathbb{S}^{n-1}$  into a compactification of  $\mathbb{R}^n$ . To do so (topologically) let us identify  $\mathbb{R}^n$  with the interior of the unit ball with respect to the Euclidean metric using the map

(12.9) 
$$\mathbb{R}^n \ni x \longmapsto \frac{x}{\langle x \rangle} \in \{ y \in \mathbb{R}^n; |y| \le 1 \} = \mathbb{B}^n.$$

Clearly  $|x| < \langle x \rangle$  and for  $0 \le a < 1$ ,  $|x| = a \langle x \rangle$  has only the solution  $|x| = a/(1-a^2)^{\frac{1}{2}}$ . Thus if we combine (12.9) with the identification of  $\mathbb{S}^n$  with the unit sphere we get an identification

(12.10) 
$$\mathbb{R}^n \cup \mathbb{S}^{n-1} \simeq \mathbb{B}^n.$$

Using this identification we can, and will, regard Csp(u) and Css(u) as subsets of  $\mathbb{B}^{n,21}$ 

**Lemma 12.3.** For any  $u \in \mathcal{S}'(\mathbb{R}^n)$ ,  $\operatorname{Csp}(u)$  and  $\operatorname{Css}(u)$  are closed subsets of  $\mathbb{B}^n$  and if  $\tilde{\psi} \in \mathcal{C}^{\infty}(\mathbb{S}^n)$  has  $\operatorname{supp}(\tilde{\psi}) \cap \operatorname{Css}(u) = \emptyset$  then for R sufficiently large  $\tilde{\psi}_R u \in \mathcal{S}(\mathbb{R}^n)$ .

*Proof.* Directly from the definition we know that  $Csp(u) \cap \mathbb{R}^n$  is closed, as is  $Css(u) \cap \mathbb{R}^n$ . Thus, in each case, we need to show that if  $\omega \in \mathbb{S}^{n-1}$  and  $\omega \notin Csp(u)$  then Csp(u) is disjoint from some neighbourhood of  $\omega$  in  $\mathbb{B}^n$ . However, by definition,

$$U = \{x \in \mathbb{R}^n; \psi_R(x) \neq 0\} \cup \{\omega' \in \mathbb{S}^{n-1}; \psi(\omega') \neq 0\}$$

is such a neighbourhood. Thus the fact that Csp(u) is closed follows directly from the definition. The argument for Css(u) is essentially the same.

Thus, for each point in  $\operatorname{supp}(\psi) \subset \mathbb{S}^{n-1}$  there exists a conic localizer for which  $\psi_R u \in \mathcal{S}(\mathbb{R}^n)$ . By compactness we may choose a finite number of these functions  $\psi_j$  such that the open sets  $\{\psi_j(\omega) > 0\}$  cover  $\operatorname{supp}(\tilde{\psi})$ . By assumption  $(\psi_j)_{R_j} u \in \mathcal{S}(\mathbb{R}^n)$  for some  $R_j > 0$ . However this will remain true if  $R_j$  is increased, so we may suppose that  $R_j = R$  is independent of j. Then for function

$$\mu = \sum_{j} |\psi_{j}|^{2} \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$$

we have  $\mu_R u \in \mathcal{S}(\mathbb{R}^n)$ . Since  $\tilde{\psi} = \psi' \mu$  for some  $\mu \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$  it follows that  $\tilde{\psi}_{R+1} u \in \mathcal{S}(\mathbb{R}^n)$  as claimed.

Corollary 12.4. If  $u \in \mathcal{S}'(\mathbb{R}^n)$  then  $Css(u) = \emptyset$  if and only if  $u \in \mathcal{S}(\mathbb{R}^n)$ .

Proof. Certainly  $\operatorname{Css}(u) = \emptyset$  if  $u \in \mathcal{S}(\mathbb{R}^n)$ . If  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $\operatorname{Css}(u) = \emptyset$  then from Lemma 12.3,  $\psi_R u \in \mathcal{S}(\mathbb{R}^n)$  where  $\psi = 1$ . Thus  $v = (1 - \psi_R)u \in \mathcal{C}_c^{-\infty}(\mathbb{R}^n)$  has  $\operatorname{singsupp}(v) = \emptyset$  so  $v \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  and hence  $u \in \mathcal{S}(\mathbb{R}^n)$ .

<sup>&</sup>lt;sup>21</sup>In fact while the topology here is correct the smooth structure on  $\mathbb{B}^n$  is not the right one<sup>TM</sup>— see Problem?? For our purposes here this issue is irrelevant.

Of course the analogous result for Csp(u), that  $Csp(u) = \emptyset$  if and only if u = 0 follows from the fact that this is true if  $supp(u) = \emptyset$ . I will treat a few other properties as self-evident. For instance (12.11)

$$Csp(\phi u) \subset Csp(u), \ Css(\phi u) \subset Css(u) \ \forall \ u \in \mathcal{S}'(\mathbb{R}^n), \ \phi \in \mathcal{S}(\mathbb{R}^n)$$

and

(12.12) 
$$\operatorname{Csp}(c_1u_1 + c_2u_2) \subset \operatorname{Csp}(u_1) \cup \operatorname{Csp}(u_2),$$
  
 $\operatorname{Css}(c_1u_1 + c_2u_2) \subset \operatorname{Css}(u_1) \cup \operatorname{Css}(u_2)$   
 $\forall u_1, u_2 \in \mathcal{S}'(\mathbb{R}^n), c_1, c_2 \in \mathbb{C}.$ 

One useful consequence of having the cone support at our disposal is that we can discuss sufficient conditions to allow us to multiply distributions; we will get better conditions below using the same idea but applied to the wavefront set but this preliminary discussion is used there. In general the product of two distributions is not defined, and indeed not definable, as a distribution. However, we can always multiply an element of  $\mathcal{S}'(\mathbb{R}^n)$  and an element of  $\mathcal{S}(\mathbb{R}^n)$ .

To try to understand multiplication look at the question of *pairing* between two distributions.

**Lemma 12.5.** If  $K_i \subset \mathbb{B}^n$ , i = 1, 2, are two disjoint closed (hence compact) subsets then we can define an unambiguous pairing

(12.13) 
$$\{u \in \mathcal{S}'(\mathbb{R}^n); \operatorname{Css}(u) \subset K_1\} \times \{u \in \mathcal{S}'(\mathbb{R}^n); \operatorname{Css}(u) \subset K_2\} \ni (u_1, u_2) \longrightarrow u_1(u_2) \in \mathbb{C}.$$

Proof. To define the pairing, choose a function  $\psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$  which is identically equal to 1 in a neighbourhood of  $K_1 \cap \mathbb{S}^{n-1}$  and with support disjoint from  $K_2 \cap \mathbb{S}^{n-1}$ . Then extend it to be homogeneous, as above, and cut off to get  $\psi_R$ . If R is large enough  $\mathrm{Csp}(\psi_R)$  is disjoint from  $K_2$ . Then  $\psi_R + (1 - \psi)_R = 1 + \nu$  where  $\nu \in \mathcal{C}^{\infty}_c(\mathbb{R}^n)$ . We can find another function  $\mu \in \mathcal{C}^{\infty}_c(\mathbb{R}^n)$  such that  $\psi_1 = \psi_R + \mu = 1$  in a neighbourhood of  $K_1$  and with  $\mathrm{Csp}(\psi_1)$  disjoint from  $K_2$ . Once we have this, for  $u_1$  and  $u_2$  as in (12.13),

(12.14) 
$$\psi_1 u_2 \in \mathcal{S}(\mathbb{R}^n) \text{ and } (1 - \psi_1) u_1 \in \mathcal{S}(\mathbb{R}^n)$$

since in both cases Css is empty from the definition. Thus we can define the desired pairing between  $u_1$  and  $u_2$  by

$$(12.15) u_1(u_2) = u_1(\psi_1 u_2) + u_2((1 - \psi_1)u_1).$$

Of course we should check that this definition is independent of the cut-off function used in it. However, if we go through the definition and choose a different function  $\psi'$  to start with, extend it homogeneously and cut off (probably at a different R) and then find a correction term  $\mu'$  then the 1-parameter linear homotopy between them

$$(12.16) \psi_1(t) = t\psi_1 + (1-t)\psi_1', \ t \in [0,1]$$

satisfies all the conditions required of  $\psi_1$  in formula (12.14). Thus in fact we get a smooth family of pairings, which we can write for the moment as

$$(12.17) (u_1, u_2)_t = u_1(\psi_1(t)u_2) + u_2((1 - \psi_1(t))u_1).$$

By inspection, this is an affine-linear function of t with derivative

(12.18) 
$$u_1((\psi_1 - \psi_1')u_2) + u_2((\psi_1' - \psi_1))u_1).$$

Now, we just have to justify moving the smooth function in (12.18) to see that this gives zero. This should be possible since  $Csp(\psi'_1 - \psi_1)$  is disjoint from *both*  $K_1$  and  $K_2$ .

In fact, to be very careful for once, we should construct another function  $\chi$  in the same way as we constructed  $\psi_1$  to be homogenous near infinity and smooth and such that  $Csp(\chi)$  is also disjoint from both  $K_1$  and  $K_2$  but  $\chi = 1$  on  $Csp(\psi'_1 - \psi_1)$ . Then  $\chi(\psi'_1 - \psi_1) = \psi'_1 - \psi_1$  so we can insert it in (12.18) and justify

(12.19) 
$$u_1((\psi_1 - \psi_1')u_2) = u_1(\chi^2(\psi_1 - \psi_1')u_2) = (\chi u_1)((\psi_1 - \psi_1')\chi u_2)$$
  
=  $(\chi u_2)(\psi_1 - \psi_1')\chi u_1) = u_2(\psi_1 - \psi_1')\chi u_1).$ 

Here the second equality is just the identity for  $\chi$  as a (multiplicative) linear map on  $\mathcal{S}(\mathbb{R}^n)$  and hence  $\mathcal{S}'(\mathbb{R}^n)$  and the operation to give the crucial, third, equality is permissible because both elements are in  $\mathcal{S}(\mathbb{R}^n)$ .

Once we have defined the pairing between tempered distibutions with disjoint conic singular supports, in the sense of (12.14), (12.15), we can define the product under the same conditions. Namely to define the product of say  $u_1$  and  $u_2$  we simply set

(12.20) 
$$u_1u_2(\phi) = u_1(\phi u_2) = u_2(\phi u_1) \ \forall \ \phi \in \mathcal{S}(\mathbb{R}^n),$$
  
provided  $\operatorname{Css}(u_1) \cap \operatorname{Css}(u_2) = \emptyset.$ 

Indeed, this would be true if one of  $u_1$  or  $u_2$  was itself in  $\mathcal{S}(\mathbb{R}^n)$  and makes sense in general. I leave it to you to check the continuity statement required to prove that the product is actually a tempered distibution (Problem 78).

One can also give a similar discussion of the convolution of two tempered distributions. Once again we do not have a definition of u\*v as a tempered distribution for all  $u, v \in \mathcal{S}'(\mathbb{R}^n)$ . We do know how to define the convolution if either u or v is compactly supported, or if either is in  $\mathcal{S}(\mathbb{R}^n)$ . This leads directly to

**Lemma 12.6.** If  $Css(u) \cap S^{n-1} = \emptyset$  then u \* v is defined unambiguously by

(12.21) 
$$u * v = u_1 * v + u_2 * v, \ u_1 = (1 - \chi(\frac{x}{r}))u, \ u_2 = u - u_1$$

where  $\chi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  has  $\chi(x) = 1$  in  $|x| \leq 1$  and R is sufficiently large; there is a similar definition if  $\mathrm{Css}(v) \cap \mathbb{S}^{n-1} = \emptyset$ .

Proof. Since  $Css(u) \cap \mathbb{S}^{n-1} = \emptyset$ , we know that  $Css(u_1) = \emptyset$  if R is large enough, so then both terms on the right in (12.21) are well-defined. To see that the result is independent of R just observe that the difference of the right-hand side for two values of R is of the form w \* v - w \* v with w compactly supported.

Now, we can go even further using a slightly more sophisticated decomposition based on

**Lemma 12.7.** If  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $Css(u) \cap \Gamma = \emptyset$  where  $\Gamma \subset \mathbb{S}^{n-1}$  is a closed set, then  $u = u_1 + u_2$  where  $Csp(u_1) \cap \Gamma = \emptyset$  and  $u_2 \in \mathcal{S}(\mathbb{R}^n)$ ; in fact

(12.22) 
$$u = u_1' + u_1'' + u_2 \text{ where } u_1' \in \mathcal{C}_c^{-\infty}(\mathbb{R}^n) \text{ and}$$
  
  $0 \notin \text{supp}(u_1''), \ x \in \mathbb{R}^n \setminus \{0\}, \ x/|x| \in \Gamma \Longrightarrow x \notin \text{supp}(u_1'').$ 

*Proof.* A covering argument which you should provide.  $\Box$ 

Let  $\Gamma_i \subset \mathbb{R}^n$ , i = 1, 2, be closed cones. That is they are closed sets such that if  $x \in \Gamma_i$  and a > 0 then  $ax \in \Gamma_i$ . Suppose in addition that

(12.23) 
$$\Gamma_1 \cap (-\Gamma_2) = \{0\}.$$

That is, if  $x \in \Gamma_1$  and  $-x \in \Gamma_2$  then x = 0. Then it follows that for some c > 0,

$$(12.24) x \in \Gamma_1, y \in \Gamma_2 \Longrightarrow |x+y| \ge c(|x|+|y|).$$

To see this consider x+y where  $x \in \Gamma_1$ ,  $y \in \Gamma_2$  and  $|y| \leq |x|$ . We can assume that  $x \neq 0$ , otherwise the estimate is trivially true with c=1, and then  $Y=y/|x| \in \Gamma_1$  and  $X=x/|x| \in \Gamma_2$  have  $|Y| \leq 1$  and |X|=1. However  $X+Y \neq 0$ , since |X|=1, so by the continuity of the sum,  $|X+Y| \geq 2c > 0$  for some c>0. Thus  $|X+Y| \geq c(|X|+|Y|)$  and the result follows by scaling back. The other case, of  $|x| \leq |y|$ 

follows by the same argument with x and y interchanged, so (12.24) is a consequence of (12.23).

**Lemma 12.8.** For any  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $\phi \in \mathcal{S}(\mathbb{R}^n)$ ,

(12.25) 
$$\operatorname{Css}(\phi * u) \subset \operatorname{Css}(u) \cap \mathbb{S}^{n-1}.$$

*Proof.* We already know that  $\phi * u$  is smooth, so  $Css(\phi * u) \subset \mathbb{S}^{n-1}$ . Thus, we need to show that if  $\omega \in \mathbb{S}^{n-1}$  and  $\omega \notin Css(u)$  then  $\omega \notin Css(\phi * u)$ .

Fix such a point  $\omega \in \mathbb{S}^{n-1} \setminus \operatorname{Css}(u)$  and take a closed set  $\Gamma \subset \mathbb{S}^{n-1}$  which is a neighbourhood of  $\omega$  but which is still disjoint from  $\operatorname{Css}(u)$  and then apply Lemma 12.7. The two terms  $\phi * u_2$ , where  $u_2 \in \mathcal{S}(\mathbb{R}^n)$  and  $\phi * u_1'$  where  $u_1' \in \mathcal{C}_c^{-\infty}(\mathbb{R}^n)$  are both in  $\mathcal{S}(\mathbb{R}^n)$  so we can assume that u has the support properties of  $u_1''$ . In particular there is a smaller closed subset  $\Gamma_1 \subset \mathbb{S}^{n-1}$  which is still a neighbourhood of  $\omega$  but which does not meet  $\Gamma_2$ , which is the closure of the complement of  $\Gamma$ . If we replace these  $\Gamma_i$  by the closed cones of which they are the 'cross-sections' then we are in the situation of (12.23) and (12.23), except for the signs. That is, there is a constant c > 0 such that

$$(12.26) |x - y| \ge c(|x| + |y|).$$

Now, we can assume that there is a cutoff function  $\psi_R$  which has support in  $\Gamma_2$  and is such that  $u = \psi_R u$ . For any conic cutoff,  $\psi'_R$ , with support in  $\Gamma_1$ 

$$(12.27) \quad \psi_R'(\phi * u) = \langle \psi_R u, \phi(x - \cdot) \rangle = \langle u(y), \psi_R(y) \psi_R'(x) \phi(x - y) \rangle.$$

The continuity of u means that this is estimated by some Schwartz seminorm

(12.28) 
$$\sup_{y,|\alpha| \le k} |D_y^{\alpha}(\psi_R(y)\psi_R'(x)\phi(x-y))| (1+|y|)^k$$

$$\le C_N \|\phi\| \sup_y (1+|x|+|y|)^{-N} (1+|y|)^k \le C_N \|\phi\| (1+|x|)^{-N+k}$$

for some Schwartz seminorm on  $\phi$ . Here we have used the estimate (12.24), in the form (12.26), using the properties of the supports of  $\psi'_R$  and  $\psi_R$ . Since this is true for any N and similar estimates hold for the derivatives, it follows that  $\psi'_R(u * \phi) \in \mathcal{S}(\mathbb{R}^n)$  and hence that  $\omega \notin \mathrm{Css}(u * \phi)$ .

Corollary 12.9. Under the conditions of Lemma 12.6

(12.29) 
$$\operatorname{Css}(u * v) \subset (\operatorname{singsupp}(u) + \operatorname{singsupp}(v)) \cup (\operatorname{Css}(v) \cap \mathbb{S}^{n-1}).$$

*Proof.* We can apply Lemma 12.8 to the first term in (12.21) to conclude that it has conic singular support contained in the second term in (12.29). Thus it is enough to show that (12.29) holds when  $u \in$ 

 $C_c^{-\infty}(\mathbb{R}^n)$ . In that case we know that the singular support of the convolution is contained in the first term in (12.29), so it is enough to consider the conic singular support in the sphere at infinity. Thus, if  $\omega \notin \mathrm{Css}(v)$  we need to show that  $\omega \notin \mathrm{Css}(u*v)$ . Using Lemma 12.7 we can decompose  $v=v_1+v_2+v_3$  as a sum of a Schwartz term, a compact supported term and a term which does not have  $\omega$  in its conic support. Then  $u*v_1$  is Schwartz,  $u*v_2$  has compact support and satisfies (12.29) and  $\omega$  is not in the cone support of  $u*v_3$ . Thus (12.29) holds in general.

**Lemma 12.10.** If  $u, v \in \mathcal{S}'(\mathbb{R}^n)$  and  $\omega \in \mathrm{Css}(u) \cap \mathbb{S}^{n-1} \Longrightarrow -\omega \notin \mathrm{Css}(v)$  then their convolution is defined unambiguously, using the pairing in Lemma 12.5, by

$$(12.30) u * v(\phi) = u(\check{v} * \phi) \ \forall \ \phi \in \mathcal{S}(\mathbb{R}^n).$$

*Proof.* Since  $\check{v}(x) = v(-x)$ ,  $\operatorname{Css}(\check{v}) = -\operatorname{Css}(v)$  so applying Lemma 12.8 we know that

(12.31) 
$$\operatorname{Css}(\check{v} * \phi) \subset -\operatorname{Css}(v) \cap \mathbb{S}^{n-1}.$$

Thus,  $Css(v) \cap Css(\check{v} * \phi) = \emptyset$  and the pairing on the right in (12.30) is well-defined by Lemma 12.5. Continuity follows from your work in Problem 78.

In Problem 79 I ask you to get a bound on  $Css(u * v) \cap \mathbb{S}^{n-1}$  under the conditions in Lemma 12.10.

Let me do what is actually a fundamental computation.

**Lemma 12.11.** For a conic cutoff,  $\psi_R$ , where  $\psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$ ,

(12.32) 
$$\operatorname{Css}(\widehat{\psi_R}) \subset \{0\}.$$

*Proof.* This is actually much easier than it seems. Namely we already know that  $D^{\alpha}(\psi_R)$  is smooth and homogeneous of degree  $-|\alpha|$  near infinity. From the same argument it follows that

(12.33) 
$$D^{\alpha}(x^{\beta}\psi_R) \in L^2(\mathbb{R}^n) \text{ if } |\alpha| > |\beta| + n/2$$

since this is a smooth function homogeneous of degree less than -n/2 near infinity, hence square-integrable. Now, taking the Fourier transform gives

(12.34) 
$$\xi^{\alpha} D^{\beta}(\widehat{\psi}_R) \in L^2(\mathbb{R}^n) \ \forall \ |\alpha| > |\beta| + n/2.$$

If we localize in a cone near infinity, using a (completely unrelated) cutoff  $\psi'_{R'}(\xi)$  then we must get a Schwartz function since (12.35)

$$|\xi|^{|\alpha|}\psi'_{R'}(\xi)D^{\beta}(\widehat{\psi}_{R}) \in L^{2}(\mathbb{R}^{n}) \ \forall \ |\alpha| > |\beta| + n/2 \Longrightarrow \psi'_{R'}(\xi)\widehat{\psi}_{R} \in \mathcal{S}(\mathbb{R}^{n}).$$

Indeed this argument applies anywhere that  $\xi \neq 0$  and so shows that (12.32) holds.

Now, we have obtained some reasonable looking conditions under which the product uv or the convolution u\*v of two elements of  $\mathcal{S}'(\mathbb{R}^n)$  is defined. However, reasonable as they might be there is clearly a flaw, or at least a deficiency, in the discussion. We know that in the simplest of cases,

$$\widehat{u * v} = \widehat{u}\widehat{v}.$$

Thus, it is very natural to expect a relationship between the conditions under which the product of the Fourier transforms is defined and the conditions under which the convolution is defined. Is there? Well, not much it would seem, since on the one hand we are considering the relationship between  $\operatorname{Css}(\widehat{u})$  and  $\operatorname{Css}(\widehat{v})$  and on the other the relationship between  $\operatorname{Css}(u) \cap \mathbb{S}^{n-1}$  and  $\operatorname{Css}(v) \cap \mathbb{S}^{n-1}$ . If these are to be related, we would have to find a relationship of some sort between  $\operatorname{Css}(u)$  and  $\operatorname{Css}(\widehat{u})$ . As we shall see, there is one but it is not very strong as can be guessed from Lemma 12.11. This is not so much a bad thing as a sign that we should look for another notion which combines aspects of both  $\operatorname{Css}(u)$  and  $\operatorname{Css}(\widehat{u})$ . This we will do through the notion of wavefront set. In fact we define two related objects. The first is the more conventional, the second is more natural in our present discussion.

**Definition 12.12.** If  $u \in \mathcal{S}'(\mathbb{R}^n)$  we define the wavefront set of u to be

(12.37) WF(u) = 
$$\{(x, \omega) \in \mathbb{R}^n \times \mathbb{S}^{n-1};$$
  
 $\exists \ \phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n), \ \phi(x) \neq 0, \ \omega \notin \mathrm{Css}(\widehat{\phi u})\}^{\complement}$ 

and more generally the scattering wavefront set by

(12.38) 
$$\operatorname{WF}_{\operatorname{sc}}(u) = \operatorname{WF}(u) \cup \{(\omega, p) \in \mathbb{S}^{n-1} \times \mathbb{B}^n; \exists \psi \in \mathcal{C}^{\infty}(\mathbb{S}^n), \ \psi(\omega) \neq 0, \ R > 0 \ such \ that \ p \notin \operatorname{Css}(\widehat{\psi_R u})\}^{\complement}.$$

So, the definition is really always the same. To show that  $(p,q) \notin \mathrm{WF}_{\mathrm{sc}}(u)$  we need to find 'a cutoff  $\Phi$  near p' – depending on whether  $p \in \mathbb{R}^n$  or  $p \in \mathbb{S}^{n-1}$  this is either  $\Phi = \phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $F = \phi(p) \neq 0$  or a  $\psi_R$  where  $\psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$  has  $\psi(p) \neq 0$  – such that  $q \notin \mathrm{Css}(\widehat{\Phi u})$ . One crucial property is

**Lemma 12.13.** If  $(p,q) \notin \operatorname{WF}_{\operatorname{sc}}(u)$  then if  $p \in \mathbb{R}^n$  there exists a neighbourhood  $U \subset \mathbb{R}^n$  of p and a neighbourhood  $U \subset \mathbb{B}^n$  of q such that for all  $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with support in  $U, U' \cap \operatorname{Css}(\widehat{\phi u}) = \emptyset$ ; similarly

if  $p \in \mathbb{S}^{n-1}$  then there exists a neigbourhood  $\tilde{U} \subset \mathbb{B}^n$  of p such that  $U' \cap \operatorname{Css}(\widehat{\psi_R u}) = \emptyset$  if  $\operatorname{Csp}(\omega_R) \subset \tilde{U}$ .

*Proof.* First suppose  $p \in \mathbb{R}^n$ . From the definition of conic singular support, (12.37) means precisely that there exists  $\psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$ ,  $\psi(\omega) \neq 0$  and R such that

(12.39) 
$$\psi_R(\widehat{\phi u}) \in \mathcal{S}(\mathbb{R}^n).$$

Since we know that  $\widehat{\phi u} \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ , this is actually true for all R > 0 as soon as it is true for one value. Furthermore, if  $\phi' \in \mathcal{C}^{\infty}_{c}(\mathbb{R}^n)$  has  $\operatorname{supp}(\phi') \subset \{\phi \neq 0\}$  then  $\omega \notin \operatorname{Css}(\widehat{\phi'u})$  follows from  $\omega \notin \operatorname{Css}(\widehat{\phi u})$ . Indeed we can then write  $\phi' = \mu \phi$  where  $\mu \in \mathcal{C}^{\infty}_{c}(\mathbb{R}^n)$  so it suffices to show that if  $v \in \mathcal{C}^{-\infty}_{c}(\mathbb{R}^n)$  has  $\omega \notin \operatorname{Css}(\widehat{v})$  then  $\omega \notin \operatorname{Css}(\widehat{\mu v})$  if  $\mu \in \mathcal{C}^{\infty}_{c}(\mathbb{R}^n)$ . Since  $\widehat{\mu v} = (2\pi)^{-n}v * \widehat{u}$  where  $\widecheck{v} = \widehat{\mu} \in \mathcal{S}(\mathbb{R}^n)$ , applying Lemma 12.8 we see that  $\operatorname{Css}(v * \widehat{v}) \subset \operatorname{Css}(\widehat{v})$ , so indeed  $\omega \notin \operatorname{Css}(\widehat{\phi'u})$ .

The case that  $p \in \mathbb{S}^{n-1}$  is similar. Namely we have one cut-off  $\psi_R$  with  $\psi(p) \neq 0$  and  $q \notin \mathrm{Css}(\widehat{\omega_R u})$ . We can take  $U = \{\psi_{R+10} \neq 0\}$  since if  $\psi'_{R'}$  has conic support in U then  $\psi'_{R'} = \psi'' R' \psi_R$  for some  $\psi'' \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$ . Thus

(12.40) 
$$\widehat{\psi'_{R'}u} = v * \widehat{\psi_R u}, \ \check{v} = \widehat{\omega''_{R''}}.$$

From Lemma 12.11 and Corollary 12.9 we deduce that

(12.41) 
$$\operatorname{Css}(\widehat{\psi'_{R'}u}) \subset \operatorname{Css}(\widehat{\omega_R u})$$

and hence the result follows with U' a small neighbourhood of q.

Proposition 12.14. For any  $u \in \mathcal{S}'(\mathbb{R}^n)$ ,

(12.42) WF<sub>sc</sub>(u) 
$$\subset \partial(\mathbb{B}^n \times \mathbb{B}^n) = (\mathbb{B}^n \times \mathbb{S}^{n-1}) \cup (\mathbb{S}^{n-1} \times \mathbb{B}^n)$$
  
=  $(\mathbb{R}^n \times \mathbb{S}^{n-1}) \cup (\mathbb{S}^{n-1} \times \mathbb{S}^{n-1}) \cup (\mathbb{S}^{n-1} \times \mathbb{R}^n)$ 

and WF(u)  $\subset \mathbb{R}^n$  are closed sets and under projection onto the first variable (12.43)

$$\pi_1(\mathrm{WF}(u)) = \mathrm{singsupp}(u) \subset \mathbb{R}^n, \ \pi_1(\mathrm{WF}_{\mathrm{sc}}(u)) = \mathrm{Css}(u) \subset \mathbb{B}^n.$$

Proof. To prove the first part of (12.43) we need to show that if  $(\bar{x}, \omega) \notin WF(u)$  for all  $\omega \in \mathbb{S}^{n-1}$  with  $\bar{x} \in \mathbb{R}^n$  fixed, then  $\bar{x} \notin \text{singsupp}(u)$ . The definition (12.37) means that for each  $\omega \in \mathbb{S}^{n-1}$  there exists  $\phi_{\omega} \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $\phi_{\omega}(\bar{x}) \neq 0$  such that  $\omega \notin \text{Css}(\widehat{\phi_{\omega}u})$ . Since  $\text{Css}(\phi u)$  is closed and  $\mathbb{S}^{n-1}$  is compact, a finite number of these cutoffs,  $\phi_j \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ , can be chosen so that  $\phi_j(\bar{x}) \neq 0$  with the  $\mathbb{S}^{n-1} \setminus \text{Css}(\widehat{\phi_j u})$  covering  $\mathbb{S}^{n-1}$ . Now applying Lemma 12.13 above, we can find one

 $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ , with support in  $\bigcap_j \{\phi_j(x) \neq 0\}$  and  $\phi(\bar{x}) \neq 0$ , such that  $\mathrm{Css}(\widehat{\phi u}) \subset \mathrm{Css}(\widehat{\phi_j u})$  for each j and hence  $\phi u \in \mathcal{S}(\mathbb{R}^n)$  (since it is already smooth). Thus indeed it follows that  $\bar{x} \notin \mathrm{singsupp}(u)$ . The converse, that  $\bar{x} \notin \mathrm{singsupp}(u)$  implies  $(\bar{x}, \omega) \notin \mathrm{WF}(u)$  for all  $\omega \in \mathbb{S}^{n-1}$  is immediate.

The argument to prove the second part of (12.43) is similar. Since, by definition,  $\operatorname{WF}_{\operatorname{sc}}(u) \cap (\mathbb{R}^n \times \mathbb{B}^n) = \operatorname{WF}(u)$  and  $\operatorname{Css}(u) \cap \mathbb{R}^n = \operatorname{singsupp}(u)$  we only need consider points in  $\operatorname{Css}(u) \cap \mathbb{S}^{n-1}$ . Now, we first check that if  $\theta \notin \operatorname{Css}(u)$  then  $\{\theta\} \times \mathbb{B}^n \cap \operatorname{WF}_{\operatorname{sc}}(u) = \emptyset$ . By definition of  $\operatorname{Css}(u)$  there is a cut-off  $\psi_R$ , where  $\psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$  and  $\psi(\theta) \neq 0$ , such that  $\psi_R u \in \mathcal{S}(\mathbb{R}^n)$ . From (12.38) this implies that  $(\theta, p) \notin \operatorname{WF}_{\operatorname{sc}}(u)$  for all  $p \in \mathbb{B}^n$ .

Now, Lemma 12.13 allows us to apply the same argument as used above for WF. Namely we are given that  $(\theta, p) \notin \mathrm{WF}_{\mathrm{sc}}(u)$  for all  $p \in \mathbb{B}^n$ . Thus, for each p we may find  $\psi_R$ , depending on p, such that  $\psi(\theta) \neq 0$  and  $p \notin \mathrm{Css}(\widehat{\psi_R u})$ . Since  $\mathbb{B}^n$  is compact, we may choose a finite subset of these conic localizers,  $\psi_{R_j}^{(j)}$  such that the intersection

of the corresponding sets  $\operatorname{Css}(\psi_{R_j}^{(j)}u)$ , is empty, i.e. their complements cover  $\mathbb{B}^n$ . Now, using Lemma 12.13 we may choose one  $\psi$  with support in the intersection of the sets  $\{\psi^{(j)} \neq 0\}$  with  $\psi(\theta) \neq 0$  and one R such that  $\operatorname{Css}(\widehat{\psi_R u}) = \emptyset$ , but this just means that  $\psi_R u \in \mathcal{S}(\mathbb{R}^n)$  and so  $\theta \notin \operatorname{Css}(u)$  as desired.

The fact that these sets are closed (in the appropriate sets) follows directly from Lemma 12.13.  $\Box$ 

Corollary 12.15. For  $u \in \mathcal{S}'(\mathbb{R}^n)$ ,

(12.44) 
$$WF_{sc}(u) = \emptyset \iff u \in \mathcal{S}(\mathbb{R}^n).$$

Let me return to the definition of  $WF_{sc}(u)$  and rewrite it, using what we have learned so far, in terms of a decomposition of u.

**Proposition 12.16.** For any  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $(p,q) \in \partial(\mathbb{B}^n \times \mathbb{B}^n)$ ,

(12.45) 
$$(p,q) \notin \mathrm{WF}_{\mathrm{sc}}(u) \iff$$
  
 $u = u_1 + u_2, \ u_1, \ u_2 \in \mathcal{S}'(\mathbb{R}^n), \ p \notin \mathrm{Css}(u_1), \ q \notin \mathrm{Css}(\widehat{u_2}).$ 

Proof. For given  $(p,q) \notin \mathrm{WF}_{\mathrm{sc}}(u)$ , take  $\Phi = \phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  with  $\phi \equiv 1$  near p, if  $p \in \mathbb{R}^n$  or  $\Phi = \psi_R$  with  $\psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n-1})$  and  $\psi \equiv 1$  near p, if  $p \in \mathbb{S}^{n-1}$ . In either case  $p \notin \mathrm{Css}(u_1)$  if  $u_1 = (1-\Phi)u$  directly from the definition. So  $u_2 = u - u_1 = \Phi u$ . If the support of  $\Phi$  is small enough it follows as in the discussion in the proof of Proposition 12.14 that

$$(12.46) q \notin \operatorname{Css}(\widehat{u_2}).$$

Thus we have (12.45) in the forward direction.

For reverse implication it follows directly that  $(p,q) \notin \mathrm{WF}_{\mathrm{sc}}(u_1)$  and that  $(p,q) \notin \mathrm{WF}_{\mathrm{sc}}(u_2)$ .

This restatement of the definition makes it clear that there a high degree of symmetry under the Fourier transform

Corollary 12.17. For any  $u \in \mathcal{S}'(\mathbb{R}^n)$ ,

$$(12.47) (p,q) \in WF_{sc}(u)) \iff (q,-p) \in WF_{sc}(\hat{u}).$$

*Proof.* I suppose a corollary should not need a proof, but still . . . . The statement (12.47) is equivalent to

$$(12.48) (p,q) \notin \mathrm{WF}_{\mathrm{sc}}(u)) \Longrightarrow (q,-p) \notin \mathrm{WF}_{\mathrm{sc}}(\hat{u})$$

since the reverse is the same by Fourier inversion. By (12.45) the condition on the left is equivalent to  $u = u_1 + u_2$  with  $p \notin \mathrm{Css}(u_1)$ ,  $q \notin \mathrm{Css}(\widehat{u_2})$ . Hence equivalent to

(12.49) 
$$\widehat{u} = v_1 + v_2, \ v_1 = \widehat{u}_2, \ \widehat{v}_2 = (2\pi)^{-n} \widecheck{u}_1$$
  
so  $q \notin \operatorname{Css}(v_1), -p \notin \operatorname{Css}(\widehat{v}_2)$  which proves (12.47).

Now, we can exploit these notions to refine our conditions under which pairing, the product and convolution can be defined.

Theorem 12.18. For  $u, v \in \mathcal{S}'(\mathbb{R}^n)$ 

(12.50) 
$$uv \in \mathcal{S}'(\mathbb{R}^n)$$
 is unambiguously defined provided

$$(p,\omega) \in \mathrm{WF}_{\mathrm{sc}}(u) \cap (\mathbb{B}^n \times \mathbb{S}^{n-1}) \Longrightarrow (p,-\omega) \notin \mathrm{WF}_{\mathrm{sc}}(v)$$

and

(12.51) 
$$u * v \in \mathcal{S}'(\mathbb{R}^n)$$
 is unambiguously defined provided

$$(\theta,q)\in \mathrm{WF}_{\mathrm{sc}}(u)\cap (\mathbb{S}^{n-1}\times \mathbb{B}^n) \Longrightarrow (-\theta,q)\notin \mathrm{WF}_{\mathrm{sc}}(v).$$

*Proof.* Let us consider convolution first. The hypothesis, (12.51) means that for each  $\theta \in \mathbb{S}^{n-1}$  (12.52)

$$\{q \in \mathbb{B}^{n-1}; (\theta, q) \in \mathrm{WF}_{\mathrm{sc}}(u)\} \cap \{q \in \mathbb{B}^{n-1}; (-\theta, q) \in \mathrm{WF}_{\mathrm{sc}}(v)\} = \emptyset.$$

Now, the fact that WF<sub>sc</sub> is always a closed set means that (12.52) remains true near  $\theta$  in the sense that if  $U \subset \mathbb{S}^{n-1}$  is a sufficiently small neighbourhood of  $\theta$  then

$$(12.53) \quad \{q \in \mathbb{B}^{n-1}; \exists \ \theta' \in U, \ (\theta', q) \in \mathrm{WF}_{\mathrm{sc}}(u)\}$$
$$\cap \{q \in \mathbb{B}^{n-1}; \exists \ \theta'' \in U, \ (-\theta'', q) \in \mathrm{WF}_{\mathrm{sc}}(v)\} = \emptyset.$$

The compactness of  $\mathbb{S}^{n-1}$  means that there is a finite cover of  $\mathbb{S}^{n-1}$  by such sets  $U_j$ . Now select a partition of unity  $\psi_i$  of  $\mathbb{S}^{n-1}$  which is not only subordinate to this open cover, so each  $\psi_i$  is supported in one of the  $U_i$  but satisfies the additional condition that

(12.54) 
$$\operatorname{supp}(\psi_i) \cap (-\operatorname{supp}(\psi_{i'})) \neq \emptyset \Longrightarrow \operatorname{supp}(\psi_i) \cup (-\operatorname{supp}(\psi_{i'})) \subset U_j \text{ for some } j.$$

Now, if we set  $u_i = (\psi_i)_R u$ , and  $v_{i'} = (\psi_{i'})_R v$ , we know that  $u - \sum_i u_i$  has compact support and similarly for v. Since convolution is already known to be possible if (at least) one factor has compact support, it suffices to define  $u_i * v_{i'}$  for every i, i'. So, first suppose that  $\operatorname{supp}(\psi_i) \cap$ 

 $(-\sup(\psi_{i'})) \neq \emptyset$ . In this case we conclude from (12.54) that

(12.55) 
$$\operatorname{Css}(\widehat{u_i}) \cap \operatorname{Css}(\widehat{v_{i'}}) = \emptyset.$$

Thus we may define

$$\widehat{u_i * v_{i'}} = \widehat{u_i} \widehat{v_{i'}}$$

using (12.20). On the other hand if supp  $\psi_i \cap (-\operatorname{supp}(\psi_{i'})) = \emptyset$  then

(12.57) 
$$\operatorname{Css}(u_i) \cap (-\operatorname{Css}(v_{i'})) \cap \mathbb{S}^{n-1} = \emptyset$$

and in this case we can define  $u_i * v_{i'}$  using Lemma 12.10.

Thus with such a decomposition of u and v all terms in the convolution are well-defined. Of course we should check that this definition is independent of choices made in the decomposition. I leave this to you.

That the product is well-defined under condition (12.50) now follows if we define it using convolution, i.e. as

$$\widehat{uv} = f * q, \ f = \widehat{u}, \ \check{q} = \widehat{v}.$$

Indeed, using (12.47), (12.50) for u and v becomes (12.51) for f and g.

# 13. Homogeneous distributions

Next time I will talk about homogeneous distributions. On  $\mathbb R$  the functions

$$x_t^s = \begin{cases} x^s & x > 0\\ 0 & x < 0 \end{cases}$$

where  $S \in \mathbb{R}$ , is locally integrable (and hence a tempered distribution) precisely when S > -1. As a function it is homogeneous of degree s. Thus if a > 0 then

$$(ax)_t^s = a^s x_t^s$$
.

Thinking of  $x_t^s = \mu_s$  as a distribution we can set this as

$$\mu_s(ax)(\varphi) = \int \mu_s(ax)\varphi(x) dx$$
$$= \int \mu_s(x)\varphi(x/a) \frac{dx}{a}$$
$$= a^s \mu_s(\varphi).$$

Thus if we define  $\varphi_a(x) = \frac{1}{a}\varphi(\frac{x}{a})$ , for any a > 0,  $\varphi \in \mathcal{S}(\mathbb{R})$  we can ask whether a distribution is homogeneous:

$$\mu(\varphi_a) = a^s \mu(\varphi) \ \forall \ \varphi \in \mathcal{S}(\mathbb{R}).$$

### 16. Spectral Theorem

For a bounded operator T on a Hilbert space we define the spectrum as the set

(16.1) 
$$\operatorname{spec}(T) = \{ z \in \mathbb{C}; T - z \operatorname{Id} \text{ is not invertible} \}.$$

**Proposition 16.1.** For any bounded linear operator on a Hilbert space  $\operatorname{spec}(T) \subset \mathbb{C}$  is a compact subset of  $\{|z| \leq ||T||\}$ .

*Proof.* We show that the set  $\mathbb{C} \setminus \operatorname{spec}(T)$  (generally called the resolvent set of T) is open and contains the complement of a sufficiently large ball. This is based on the convergence of the Neumann series. Namely if T is bounded and ||T|| < 1 then

(16.2) 
$$(\operatorname{Id} -T)^{-1} = \sum_{j=0}^{\infty} T^{j}$$

converges to a bounded operator which is a two-sided inverse of  $\operatorname{Id} - T$ . Indeed,  $||T^j|| \leq ||T||^j$  so the series is convergent and composing with  $\operatorname{Id} - T$  on either side gives a telescoping series reducing to the identity. Applying this result, we first see that

(16.3) 
$$(T - z) = -z(\operatorname{Id} - T/z)$$

is invertible if |z| > ||T||. Similarly, if  $(T - z_0)^{-1}$  exists for some  $z_0 \in \mathbb{C}$  then

(16.4) 
$$(T-z) = (T-z_0) - (z-z_0) = (T-z_0)^{-1} (\operatorname{Id} - (z-z_0)(T-z_0)^{-1})$$
  
exists for  $|z-z_0| ||(T-z_0)^{-1}|| < 1$ .

In general it is rather difficult to precisely locate  $\operatorname{spec}(T)$ .

However for a bounded self-adjoint operator it is easier. One sign of this is the the norm of the operator has an alternative, simple, charac-terization. Namely

(16.5) if 
$$A^* = A$$
 then  $\sup_{\|\phi\|=1} \langle A\phi, \phi \rangle| = \|A\|$ .

If a is this supermum, then clearly  $a \leq ||A||$ . To see the converse, choose any  $\phi$ ,  $\psi \in H$  with norm 1 and then replace  $\psi$  by  $e^{i\theta}\psi$  with  $\theta$  chosen so that  $\langle A\phi, \psi \rangle$  is real. Then use the polarization identity to write

(16.6) 
$$4\langle A\phi, \psi \rangle = \langle A(\phi + \psi), (\phi + \psi) \rangle - \langle A(\phi - \psi), (\phi - \psi) \rangle + i\langle A(\phi + i\psi), (\phi + i\psi) \rangle - i\langle A(\phi - i\psi), (\phi - i\psi) \rangle.$$

Now, by the assumed reality we may drop the last two terms and see that

$$(16.7) \ 4|\langle A\phi, \psi \rangle| \le a(\|\phi + \psi\|^2 + \|\phi - \psi\|^2) = 2a(\|\phi\|^2 + \|\psi\|^2) = 4a.$$

Thus indeed  $||A|| = \sup_{\|\phi\| = \|\psi\| = 1} |\langle A\phi, \psi \rangle| = a$ .

We can always subtract a real constant from A so that A' = A - t satisfies

$$(16.8) -\inf_{\|\phi\|=1} \langle A'\phi, \phi \rangle = \sup_{\|\phi\|=1} \langle A'\phi, \phi \rangle = \|A'\|.$$

Then, it follows that  $A' \pm ||A'||$  is not invertible. Indeed, there exists a sequence  $\phi_n$ , with  $||\phi_n|| = 1$  such that  $\langle (A' - ||A'||)\phi_n, \phi_n \rangle \to 0$ . Thus (16.9)

$$\|(A'-\|A'\|)\phi_n\|^2 = -2\langle A'\phi_n, \phi_n\rangle + \|A'\phi_n\|^2 + \|A'\|^2 \le -2\langle A'\phi_n, \phi_n\rangle + 2\|A'\|^2 \to 0.$$

This shows that A' - ||A'|| cannot be invertible and the same argument works for A' + ||A'||. For the original operator A if we set

(16.10) 
$$m = \inf_{\|\phi\|=1} \langle A\phi, \phi \rangle \ M = \sup_{\|\phi\|=1} \langle A\phi, \phi \rangle$$

then we conclude that neither  $A - m \operatorname{Id}$  nor  $A - M \operatorname{Id}$  is invertible and  $||A|| = \max(-m, M)$ .

**Proposition 16.2.** If A is a bounded self-adjoint operator then, with m and M defined by (16.10),

$$(16.11) \{m\} \cup \{M\} \subset \operatorname{spec}(A) \subset [m, M].$$

*Proof.* We have already shown the first part, that m and M are in the spectrum so it remains to show that A-z is invertible for all  $z \in \mathbb{C} \setminus [m, M]$ .

Using the self-adjointness

(16.12) 
$$\operatorname{Im}\langle (A-z)\phi, \phi \rangle = -\operatorname{Im} z \|\phi\|^2.$$

This implies that A-z is invertible if  $z \in \mathbb{C} \setminus \mathbb{R}$ . First it shows that  $(A-z)\phi=0$  implies  $\phi=0$ , so A-z is injective. Secondly, the range is closed. Indeed, if  $(A-z)\phi_n \to \psi$  then applying (16.12) directly shows that  $\|\phi_n\|$  is bounded and so can be replaced by a weakly convergent subsequence. Applying (16.12) again to  $\phi_n - \phi_m$  shows that the sequence is actually Cauchy, hence convergens to  $\phi$  so  $(A-z)\phi=\psi$  is in the range. Finally, the orthocomplement to this range is the null space of  $A^* - \bar{z}$ , which is also trivial, so A-z is an isomorphism and (16.12) also shows that the inverse is bounded, in fact

(16.13) 
$$||(A-z)^{-1}|| \le \frac{1}{|\operatorname{Im} z|}.$$

When  $z \in \mathbb{R}$  we can replace A by A' satisfying (16.8). Then we have to show that A' - z is inverible for |z| > ||A||, but that is shown in the proof of Proposition 16.1.

The basic estimate leading to the spectral theorem is:

**Proposition 16.3.** If A is a bounded self-adjoint operator and p is a real polynomial in one variable,

(16.14) 
$$p(t) = \sum_{i=0}^{N} c_i t^i, \ c_N \neq 0,$$

then 
$$p(A) = \sum_{i=0}^{N} c_i A^i$$
 satisfies

(16.15) 
$$||p(A)|| \le \sup_{t \in [m,M]} |p(t)|.$$

*Proof.* Clearly, p(A) is a bounded self-adjoint operator. If  $s \notin p([m, M])$  then p(A) - s is invertible. Indeed, the roots of p(t) - s must cannot lie in [m.M], since otherwise  $s \in p([m, M])$ . Thus, factorizing p(s) - t we have

(16.16)

$$p(t) - s = c_N \prod_{i=1}^{N} (t - t_i(s)), \ t_i(s) \notin [m, M] \Longrightarrow (p(A) - s)^{-1}$$
 exists

since  $p(A) = c_N \sum_i (A - t_i(s))$  and each of the factors is invertible.

Thus spec $(p(A)) \subset p([m, M])$ , which is an interval (or a point), and from Proposition 16.3 we conclude that  $||p(A)|| \leq \sup p([m, M])$  which is (16.15).

Now, reinterpreting (16.15) we have a linear map

(16.17) 
$$\mathcal{P}(\mathbb{R}) \ni p \longmapsto p(A) \in \mathcal{B}(H)$$

from the real polynomials to the bounded self-adjoint operators which is continuous with respect to the supremum norm on [m, M]. Since polynomials are dense in continuous functions on finite intervals, we see that (16.17) extends by continuity to a linear map (16.18)

$$\mathcal{C}([m,M]) \ni f \longmapsto f(A) \in \mathcal{B}(H), \ \|f(A)\| \le \|f\|_{[m,M]}, \ fg(A) = f(A)g(A)$$

where the multiplicativity follows by continuity together with the fact that it is true for polynomials.

Now, consider any two elements  $\phi, \psi \in H$ . Evaluating f(A) on  $\phi$  and pairing with  $\psi$  gives a linear map

(16.19) 
$$\mathcal{C}([m, M]) \ni f \longmapsto \langle f(A)\phi, \psi \rangle \in \mathbb{C}.$$

This is a linear functional on C([m, M]) to which we can apply the Riesz representatin theorem and conclude that it is defined by integration

against a unique Radon measure  $\mu_{\phi,\psi}$ :

(16.20) 
$$\langle f(A)\phi, \psi \rangle = \int_{[m,M]} f d\mu_{\phi,\psi}.$$

The total mass  $|\mu_{\phi,\psi}|$  of this measure is the norm of the functional. Since it is a Borel measure, we can take the integral on  $-\infty, b$ ] for any  $b \in \mathbb{R}$  ad, with the uniqueness, this shows that we have a continuous sesquilinear map (16.21)

$$P_b(\phi, \psi): H \times H \ni (\phi, \psi) \longmapsto \int_{[m,b]} d\mu_{\phi,\psi} \in \mathbb{R}, \ |P_b(\phi, \psi)| \le ||A|| ||\phi|| ||\psi||.$$

From the Hilbert space Riesz representation theorem it follows that this sesquilinear form defines, and is determined by, a bounded linear operator

(16.22) 
$$P_b(\phi, \psi) = \langle P_b \phi, \psi \rangle, \ \|P_b\| \le \|A\|.$$

In fact, from the functional calculus (the multiplicativity in (16.18)) we see that

(16.23) 
$$P_b^* = P_b, P_b^2 = P_b, ||P_b|| \le 1,$$

so  $P_b$  is a projection.

Thus the spectral theorem gives us an increasing (with b) family of commuting self-adjoint projections such that  $\mu_{\phi,\psi}((-\infty,b]) = \langle P_b\phi,\psi\rangle$  determines the Radon measure for which (16.20) holds. One can go further and think of  $P_b$  itself as determining a measure

$$\mu((-\infty, b]) = P_b$$

which takes values in the projections on H and which allows the functions of A to be written as integrals in the form

$$(16.25) f(A) = \int_{[m,M]} f d\mu$$

of which (16.20) becomes the 'weak form'. To do so one needs to develop the theory of such measures and the corresponding integrals. This is not so hard but I shall not do it.

### 17. Problems

*Problem 1.* Prove that  $u_+$ , defined by (1.10) is linear.

Problem 2. Prove Lemma 1.8.

Hint(s). All functions here are supposed to be continuous, I just don't bother to keep on saying it.

- (1) Recall, or check, that the local compactness of a metric space X means that for each point  $x \in X$  there is an  $\epsilon > 0$  such that the ball  $\{y \in X; d(x,y) \leq \delta\}$  is compact for  $\delta \leq \epsilon$ .
- (2) First do the case n=1, so  $K \subseteq U$  is a compact set in an open subset.
  - (a) Given  $\delta > 0$ , use the local compactness of X, to cover K with a finite number of compact closed balls of radius at most  $\delta$ .
  - (b) Deduce that if  $\epsilon > 0$  is small enough then the set  $\{x \in X; d(x,K) \le \epsilon\}$ , where

$$d(x, K) = \inf_{y \in K} d(x, y),$$

is compact.

- (c) Show that d(x, K), for K compact, is continuous.
- (d) Given  $\epsilon > 0$  show that there is a continuous function  $g_{\epsilon}$ :  $\mathbb{R} \longrightarrow [0,1]$  such that  $g_{\epsilon}(t) = 1$  for  $t \leq \epsilon/2$  and  $g_{\epsilon}(t) = 0$  for  $t > 3\epsilon/4$ .
- (e) Show that  $f = g_{\epsilon} \circ d(\cdot, K)$  satisfies the conditions for n = 1 if  $\epsilon > 0$  is small enough.
- (3) Prove the general case by induction over n.
  - (a) In the general case, set  $K' = K \cap U_1^{\complement}$  and show that the inductive hypothesis applies to K' and the  $U_j$  for j > 1; let  $f'_j$ ,  $j = 2, \ldots, n$  be the functions supplied by the inductive assumption and put  $f' = \sum_{j \geq 2} f'_j$ .
  - assumption and put  $f' = \sum_{j \geq 2} f'_j$ . (b) Show that  $K_1 = K \cap \{f' \leq \frac{1}{2}\}$  is a compact subset of  $U_1$ .
  - (c) Using the case n = 1 construct a function F for  $K_1$  and  $U_1$ .
  - (d) Use the case n = 1 again to find G such that G = 1 on K and supp $(G) \subseteq \{f' + F > \frac{1}{2}\}.$
  - (e) Make sense of the functions

$$f_1 = F \frac{G}{f' + F}, \ f_j = f'_j \frac{G}{f' + F}, \ j \ge 2$$

and show that they satisfies the inductive assumptions.

*Problem* 3. Show that  $\sigma$ -algebras are closed under countable intersections.

Problem 4. (Easy) Show that if  $\mu$  is a complete measure and  $E \subset F$  where F is measurable and has measure 0 then  $\mu(E) = 0$ .

*Problem* 5. Show that compact subsets are measurable for any Borel measure. (This just means that compact sets are Borel sets if you follow through the tortuous terminology.)

*Problem* 6. Show that the smallest  $\sigma$ -algebra containing the sets

$$(a,\infty] \subset [-\infty,\infty]$$

for all  $a \in \mathbb{R}$ , generates what is called above the 'Borel'  $\sigma$ -algebra on  $[-\infty, \infty]$ .

Problem 7. Write down a careful proof of Proposition 1.1.

Problem 8. Write down a careful proof of Proposition 1.2.

Problem 9. Let X be the metric space

$$X = \{0\} \cup \{1/n; n \in \mathbb{N} = \{1, 2, \ldots\}\} \subset \mathbb{R}$$

with the induced metric (i.e. the same distance as on  $\mathbb{R}$ ). Recall why X is compact. Show that the space  $\mathcal{C}_0(X)$  and its dual are infinite dimensional. Try to describe the dual space in terms of sequences; at least *guess* the answer.

Problem 10. For the space  $Y = \mathbb{N} = \{1, 2, ...\} \subset \mathbb{R}$ , describe  $C_0(Y)$  and guess a description of its dual in terms of sequences.

Problem 11. Let  $(X, \mathcal{M}, \mu)$  be any measure space (so  $\mu$  is a measure on the  $\sigma$ -algebra  $\mathcal{M}$  of subsets of X). Show that the set of equivalence classes of  $\mu$ -integrable functions on X, with the equivalence relation given by (4.8), is a normed linear space with the usual linear structure and the norm given by

$$||f|| = \int_X |f| d\mu.$$

Problem 12. Let  $(X, \mathcal{M})$  be a set with a  $\sigma$ -algebra. Let  $\mu : \mathcal{M} \to \mathbb{R}$  be a finite measure in the sense that  $\mu(\phi) = 0$  and for any  $\{E_i\}_{i=1}^{\infty} \subset \mathcal{M}$  with  $E_i \cap E_j = \phi$  for  $i \neq j$ ,

(17.1) 
$$\mu\left(\bigcup_{i=1}^{\infty} E_i\right) = \sum_{i=1}^{\infty} \mu(E_i)$$

with the series on the right always absolutely convergence (i.e., this is part of the requirement on  $\mu$ ). Define

(17.2) 
$$|\mu|(E) = \sup \sum_{i=1}^{\infty} |\mu(E_i)|$$

for  $E \in \mathcal{M}$ , with the supremum over *all* measurable decompositions  $E = \bigcup_{i=1}^{\infty} E_i$  with the  $E_i$  disjoint. Show that  $|\mu|$  is a finite, positive measure.

**Hint 1.** You must show that  $|\mu|(E) = \sum_{i=1}^{\infty} |\mu|(A_i)$  if  $\bigcup_i A_i = E$ ,  $A_i \in \mathcal{M}$  being disjoint. Observe that if  $A_j = \bigcup_l A_{jl}$  is a measurable decomposition of  $A_j$  then together the  $A_{jl}$  give a decomposition of E. Similarly, if  $E = \bigcup_j E_j$  is any such decomposition of E then  $A_{jl} = A_j \cap E_l$  gives such a decomposition of  $A_j$ .

**Hint 2.** See [5] p. 117!

Problem 13. (Hahn Decomposition) With assumptions as in Problem 12:

- (1) Show that  $\mu_{+} = \frac{1}{2}(|\mu| + \mu)$  and  $\mu_{-} = \frac{1}{2}(|\mu| \mu)$  are positive measures,  $\mu = \mu_{+} \mu_{-}$ . Conclude that the definition of a measure based on (4.16) is the *same* as that in Problem 12.
- (2) Show that  $\mu_{\pm}$  so constructed are orthogonal in the sense that there is a set  $E \in \mathcal{M}$  such that  $\mu_{-}(E) = 0$ ,  $\mu_{+}(X \setminus E) = 0$ .

**Hint.** Use the definition of  $|\mu|$  to show that for any  $F \in \mathcal{M}$  and any  $\epsilon > 0$  there is a subset  $F' \in \mathcal{M}$ ,  $F' \subset F$  such that  $\mu_+(F') \geq \mu_+(F) - \epsilon$  and  $\mu_-(F') \leq \epsilon$ . Given  $\delta > 0$  apply this result repeatedly (say with  $\epsilon = 2^{-n}\delta$ ) to find a decreasing sequence of sets  $F_1 = X$ ,  $F_n \in \mathcal{M}$ ,  $F_{n+1} \subset F_n$  such that  $\mu_+(F_n) \geq \mu_+(F_{n-1}) - 2^{-n}\delta$  and  $\mu_-(F_n) \leq 2^{-n}\delta$ . Conclude that  $G = \bigcap_n F_n$  has  $\mu_+(G) \geq \mu_+(X) - \delta$  and  $\mu_-(G) = 0$ . Now let  $G_m$  be chosen this way with  $\delta = 1/m$ . Show that  $E = \bigcup_m G_m$  is as required.

Problem 14. Now suppose that  $\mu$  is a finite, positive Radon measure on a locally compact metric space X (meaning a finite positive Borel measure outer regular on Borel sets and inner regular on open sets). Show that  $\mu$  is inner regular on all Borel sets and hence, given  $\epsilon > 0$  and  $E \in \mathcal{B}(X)$  there exist sets  $K \subset E \subset U$  with K compact and U open such that  $\mu(K) \geq \mu(E) - \epsilon$ ,  $\mu(E) \geq \mu(U) - \epsilon$ .

**Hint.** First take U open, then use *its* inner regularity to find K with  $K' \subseteq U$  and  $\mu(K') \geq \mu(U) - \epsilon/2$ . How big is  $\mu(E \setminus K')$ ? Find  $V \supset K' \setminus E$  with V open and look at  $K = K' \setminus V$ .

Problem 15. Using Problem 14 show that if  $\mu$  is a finite Borel measure on a locally compact metric space X then the following three conditions are equivalent

- (1)  $\mu = \mu_1 \mu_2$  with  $\mu_1$  and  $\mu_2$  both positive finite Radon measures.
- (2)  $|\mu|$  is a finite positive Radon measure.
- (3)  $\mu_+$  and  $\mu_-$  are finite positive Radon measures.

Problem 16. Let || || be a norm on a vector space V. Show that  $||u|| = (u, u)^{1/2}$  for an inner product satisfying (5.1) - (5.4) if and only if the parallelogram law holds for every pair  $u, v \in V$ .

Hint (From Dimitri Kountourogiannis)

If  $\|\cdot\|$  comes from an inner product, then it must satisfy the polarisation identity:

$$(x,y) = 1/4(\|x+y\|^2 - \|x-y\|^2 - i\|x+iy\|^2 - i\|x-iy\|^2)$$

i.e, the inner product is recoverable from the norm, so use the RHS (right hand side) to define an inner product on the vector space. You will need the paralellogram law to verify the additivity of the RHS. Note the polarization identity is a bit more transparent for real vector spaces. There we have

$$(x,y) = 1/2(\|x+y\|^2 - \|x-y\|^2)$$

both are easy to prove using  $||a||^2 = (a, a)$ .

Problem 17. Show (Rudin does it) that if  $u : \mathbb{R}^n \to \mathbb{C}$  has continuous partial derivatives then it is differentiable at each point in the sense of (6.5).

Problem 18. Consider the function  $f(x) = \langle x \rangle^{-1} = (1+|x|^2)^{-1/2}$ . Show that

$$\frac{\partial f}{\partial x_j} = l_j(x) \cdot \langle x \rangle^{-3}$$

with  $l_j(x)$  a linear function. Conclude by induction that  $\langle x \rangle^{-1} \in \mathcal{C}_0^k(\mathbb{R}^n)$  for all k.

Problem 19. Show that  $\exp(-|x|^2) \in \mathcal{S}(\mathbb{R}^n)$ .

Problem 20. Prove (7.7), probably by induction over k.

Problem 21. Prove Lemma 7.4.

*Hint.* Show that a set  $U \ni 0$  in  $\mathcal{S}(\mathbb{R}^n)$  is a neighbourhood of 0 if and only if for some k and  $\epsilon > 0$  it contains a set of the form

$$\left\{ \varphi \in \mathcal{S}(\mathbb{R}^n) ; \sum_{\substack{|\alpha| \le k, \\ |\beta| \le k}} \sup \left| x^{\alpha} D^{\beta} \varphi \right| < \epsilon \right\}.$$

Problem 22. Prove (8.7), by estimating the integrals.

Problem 23. Prove (8.9) where

$$\psi_j(z;x') = \int_0^t \frac{\partial \psi}{\partial z_j}(z+tx') dt$$
.

Problem 24. Prove (8.20). You will probably have to go back to first principles to do this. Show that it is enough to assume  $u \geq 0$  has compact support. Then show it is enough to assume that u is a simple, and integrable, function. Finally look at the definition of Lebesgue measure and show that if  $E \subset \mathbb{R}^n$  is Borel and has finite Lebesgue measure then

$$\lim_{|t| \to \infty} \mu(E \setminus (E+t)) = 0$$

where  $\mu =$  Lebesgue measure and

$$E + t = \{ p \in \mathbb{R}^n ; p' + t, p' \in E \}$$
.

Problem 25. Prove Leibniz' formula

$$D^{\alpha}{}_{x}(\varphi\psi) = \sum_{\beta \leq \alpha} \binom{\alpha}{\beta} D^{\alpha}{}_{x} \varphi \cdot d^{\alpha-\beta}_{x} \psi$$

for any  $C^{\infty}$  functions and  $\varphi$  and  $\psi$ . Here  $\alpha$  and  $\beta$  are multiindices,  $\beta \leq \alpha$  means  $\beta_j \leq \alpha_j$  for each j? and

$$\begin{pmatrix} \alpha \\ \beta \end{pmatrix} = \prod_{j} \begin{pmatrix} \alpha_j \\ \beta_j \end{pmatrix}.$$

I suggest induction!

Problem 26. Prove the generalization of Proposition 8.10 that  $u \in \mathcal{S}'(\mathbb{R}^n)$ , supp $(w) \subset \{0\}$  implies there are constants  $c\alpha$ ,  $|\alpha| \leq m$ , for some m, such that

$$u = \sum_{|\alpha| \le m} c_{\alpha} D^{\alpha} \delta.$$

Hint This is not so easy! I would be happy if you can show that  $u \in M(\mathbb{R}^n)$ , supp  $u \subset \{0\}$  implies  $u = c\delta$ . To see this, you can show that

$$\varphi \in \mathcal{S}(\mathbb{R}^n), \ \varphi(0) = 0$$
  
 $\Rightarrow \exists \varphi_j \in \mathcal{S}(\mathbb{R}^n), \ \varphi_j(x) = 0 \text{ in } |x| \le \epsilon_j > 0(\downarrow 0),$   
 $\sup |\varphi_j - \varphi| \to 0 \text{ as } j \to \infty.$ 

To prove the general case you need something similar — that given m, if  $\varphi \in \mathcal{S}(\mathbb{R}^n)$  and  $D^{\alpha}_{x}\varphi(0) = 0$  for  $|\alpha| \leq m$  then  $\exists \varphi_j \in \mathcal{S}(\mathbb{R}^n)$ ,  $\varphi_j = 0$  in  $|x| \leq \epsilon_j$ ,  $\epsilon_j \downarrow 0$  such that  $\varphi_j \to \varphi$  in the  $\mathcal{C}^m$  norm.

Problem 27. If  $m \in \mathbb{N}$ , m' > 0 show that  $u \in H^m(\mathbb{R}^n)$  and  $D^{\alpha}u \in H^{m'}(\mathbb{R}^n)$  for all  $|\alpha| \leq m$  implies  $u \in H^{m+m'}(\mathbb{R}^n)$ . Is the converse true?

Problem 28. Show that every element  $u \in L^2(\mathbb{R}^n)$  can be written as a sum

$$u = u_0 + \sum_{j=1}^n D_j u_j, \ u_j \in H^1(\mathbb{R}^n), \ j = 0, \dots, n.$$

*Problem* 29. Consider for n = 1, the locally integrable function (the Heaviside function),

$$H(x) = \begin{cases} 0 & x \le 0 \\ 1 & x > 1. \end{cases}$$

Show that  $D_xH(x)=c\delta$ ; what is the constant c?

Problem 30. For what range of orders m is it true that  $\delta \in H^m(\mathbb{R}^n)$ ,  $\delta(\varphi) = \varphi(0)$ ?

*Problem* 31. Try to write the Dirac measure explicitly (as possible) in the form (10.8). How many derivatives do you think are necessary?

Problem 32. Go through the computation of  $\overline{\partial}E$  again, but cutting out a disk  $\{x^2 + y^2 \le \epsilon^2\}$  instead.

Problem 33. Consider the Laplacian, (11.4), for n = 3. Show that  $E = c(x^2 + y^2)^{-1/2}$  is a fundamental solution for some value of c.

Problem 34. Recall that a topology on a set X is a collection  $\mathcal{F}$  of subsets (called the *open* sets) with the properties,  $\phi \in \mathcal{F}$ ,  $X \in \mathcal{F}$  and  $\mathcal{F}$  is closed under finite intersections and arbitrary unions. Show that the following definition of an open set  $U \subset \mathcal{S}'(\mathbb{R}^n)$  defines a topology:

$$\forall u \in U \text{ and all } \varphi \in \mathcal{S}(\mathbb{R}^n) \ \exists \epsilon > 0 \text{ st.}$$
$$|(u' - u)(\varphi)| < \epsilon \Rightarrow u' \in U.$$

This is called the weak topology (because there are very few open sets). Show that  $u_j \to u$  weakly in  $\mathcal{S}'(\mathbb{R}^n)$  means that for every open set  $U \ni u \; \exists N \; \text{st.} \; u_j \in U \; \forall \; j \geq N$ .

Problem 35. Prove (11.18) where  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $\varphi, \psi \in \mathcal{S}(\mathbb{R}^n)$ .

Problem 36. Show that for fixed  $v \in \mathcal{S}'(\mathbb{R}^n)$  with compact support

$$\mathcal{S}(\mathbb{R}^n) \ni \varphi \mapsto v * \varphi \in \mathcal{S}(\mathbb{R}^n)$$

is a continuous linear map.

Problem 37. Prove the ?? to properties in Theorem 11.6 for u \* v where  $u \in \mathcal{S}'(\mathbb{R}^n)$  and  $v \in \mathcal{S}'(\mathbb{R}^n)$  with at least one of them having compact support.

Problem 38. Use Theorem 11.9 to show that if P(D) is hypoelliptic then every parametrix  $F \in \mathcal{S}(\mathbb{R}^n)$  has sing supp $(F) = \{0\}$ .

Problem 39. Show that if P(D) is an elliptic differential operator of order  $m, u \in L^2(\mathbb{R}^n)$  and  $P(D)u \in L^2(\mathbb{R}^n)$  then  $u \in H^m(\mathbb{R}^n)$ .

*Problem* 40 (Taylor's theorem). Let  $u: \mathbb{R}^n \longrightarrow \mathbb{R}$  be a real-valued function which is k times continuously differentiable. Prove that there is a polynomial p and a continuous function v such that

$$u(x) = p(x) + v(x)$$
 where  $\lim_{|x| \downarrow 0} \frac{|v(x)|}{|x|^k} = 0$ .

Problem 41. Let  $\mathcal{C}(\mathbb{B}^n)$  be the space of continuous functions on the (closed) unit ball,  $\mathbb{B}^n = \{x \in \mathbb{R}^n; |x| \leq 1\}$ . Let  $\mathcal{C}_0(\mathbb{B}^n) \subset \mathcal{C}(\mathbb{B}^n)$  be the subspace of functions which vanish at each point of the boundary and let  $\mathcal{C}(\mathbb{S}^{n-1})$  be the space of continuous functions on the unit sphere. Show that inclusion and restriction to the boundary gives a short exact sequence

$$\mathcal{C}_0(\mathbb{B}^n) \hookrightarrow \mathcal{C}(\mathbb{B}^n) \longrightarrow \mathcal{C}(\mathbb{S}^{n-1})$$

(meaning the first map is injective, the second is surjective and the image of the first is the null space of the second.)

Problem 42 (Measures). A measure on the ball is a continuous linear functional  $\mu: \mathcal{C}(\mathbb{B}^n) \longrightarrow \mathbb{R}$  where continuity is with respect to the supremum norm, i.e. there must be a constant C such that

$$|\mu(f)| \le C \sup_{x \in \mathbb{R}^n} |f(x)| \ \forall \ f \in \mathcal{C}(\mathbb{B}^n).$$

Let  $M(\mathbb{B}^n)$  be the linear space of such measures. The space  $M(\mathbb{S}^{n-1})$  of measures on the sphere is defined similarly. Describe an injective map

$$M(\mathbb{S}^{n-1}) \longrightarrow M(\mathbb{B}^n).$$

Can you define another space so that this can be extended to a short exact sequence?

*Problem* 43. Show that the Riemann integral defines a measure

(17.3) 
$$\mathcal{C}(\mathbb{B}^n) \ni f \longmapsto \int_{\mathbb{R}^n} f(x) dx.$$

Problem 44. If  $g \in \mathcal{C}(\mathbb{B}^n)$  and  $\mu \in M(\mathbb{B}^n)$  show that  $g\mu \in M(\mathbb{B}^n)$ where  $(g\mu)(f) = \mu(fg)$  for all  $f \in \mathcal{C}(\mathbb{B}^n)$ . Describe all the measures with the property that

$$x_j\mu = 0$$
 in  $M(\mathbb{B}^n)$  for  $j = 1, \dots, n$ .

Problem 45 (Hörmander, Theorem 3.1.4). Let  $I \subset \mathbb{R}$  be an open, nonempty interval.

- i) Show (you may use results from class) that there exists  $\psi \in$  $\mathcal{C}^\infty_c(I)$  with  $\int_{\mathbb{R}} \psi(x) ds = 1$ . \nii) Show that any  $\phi \in \mathcal{C}^\infty_c(I)$  may be written in the form

$$\phi = \tilde{\phi} + c\psi, \ c \in \mathbb{C}, \ \tilde{\phi} \in \mathcal{C}_c^{\infty}(I) \text{ with } \int_{\mathbb{R}} \tilde{\phi} = 0.$$

- iii) Show that if  $\tilde{\phi} \in \mathcal{C}_c^{\infty}(I)$  and  $\int_{\mathbb{R}} \tilde{\phi} = 0$  then there exists  $\mu \in$  $C_c^{\infty}(I)$  such that  $\frac{d\mu}{dx} = \tilde{\phi}$  in I. iv) Suppose  $u \in C^{-\infty}(I)$  satisfies  $\frac{du}{dx} = 0$ , i.e.

$$u(-\frac{d\phi}{dx}) = 0 \ \forall \ \phi \in \mathcal{C}_c^{\infty}(I),$$

show that u = c for some constant c.

v) Suppose that  $u \in \mathcal{C}^{-\infty}(I)$  satisfies  $\frac{du}{dx} = c$ , for some constant c, show that u = cx + d for some  $d \in \mathbb{C}$ .

Problem 46. [Hörmander Theorem 3.1.16]

i) Use Taylor's formula to show that there is a fixed  $\psi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ such that any  $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  can be written in the form

$$\phi = c\psi + \sum_{j=1}^{n} x_j \psi_j$$

where  $c \in \mathbb{C}$  and the  $\psi_j \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  depend on  $\phi$ .

ii) Recall that  $\delta_0$  is the distribution defined by

$$\delta_0(\phi) = \phi(0) \ \forall \ \phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n);$$

explain why  $\delta_0 \in \mathcal{C}^{-\infty}(\mathbb{R}^n)$ .

iii) Show that if  $u \in \mathcal{C}^{-\infty}(\mathbb{R}^n)$  and  $u(x_i\phi) = 0$  for all  $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$ and j = 1, ..., n then  $u = c\delta_0$  for some  $c \in \mathbb{C}$ .

iv) Define the 'Heaviside function'

$$H(\phi) = \int_0^\infty \phi(x) dx \ \forall \ \phi \in \mathcal{C}_c^\infty(\mathbb{R});$$

show that  $H \in \mathcal{C}^{-\infty}(\mathbb{R})$ .

v) Compute  $\frac{d}{dx}H \in \mathcal{C}^{-\infty}(\mathbb{R})$ .

Problem 47. Using Problems 45 and 46, find all  $u \in \mathcal{C}^{-\infty}(\mathbb{R})$  satisfying the differential equation

$$x\frac{du}{dx} = 0 \text{ in } \mathbb{R}.$$

These three problems are all about homogeneous distributions on the line, extending various things using the fact that

$$x_{+}^{z} = \begin{cases} \exp(z \log x) & x > 0\\ 0 & x \le 0 \end{cases}$$

is a continuous function on  $\mathbb R$  if  $\operatorname{Re} z>0$  and is differentiable if  $\operatorname{Re} z>1$  and then satisfies

$$\frac{d}{dx}x_+^z = zx_+^{z-1}.$$

We used this to define

(17.4) 
$$x_{+}^{z} = \frac{1}{z+k} \frac{1}{z+k-1} \cdots \frac{1}{z+1} \frac{d^{k}}{dx^{k}} x_{+}^{z+k} \text{ if } z \in \mathbb{C} \setminus -\mathbb{N}.$$

Problem 48. [Hadamard regularization]

i) Show that (17.4) just means that for each  $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R})$ 

$$x_{+}^{z}(\phi) = \frac{(-1)^{k}}{(z+k)\cdots(z+1)} \int_{0}^{\infty} \frac{d^{k}\phi}{dx^{k}}(x)x^{z+k}dx, \operatorname{Re} z > -k, \ z \notin -\mathbb{N}.$$

ii) Use integration by parts to show that (17.5)

$$x_{+}^{z}(\phi) = \lim_{\epsilon \downarrow 0} \left[ \int_{\epsilon}^{\infty} \phi(x) x^{z} dx - \sum_{j=1}^{k} C_{j}(\phi) \epsilon^{z+j} \right], \text{ Re } z > -k, \ z \notin -\mathbb{N}$$

for certain constants  $C_j(\phi)$  which you should give explicitly. [This is called Hadamard regularization after Jacques Hadamard, feel free to look at his classic book [3].]

iii) Assuming that  $-k+1 \ge \operatorname{Re} z > -k$ ,  $z \ne -k+1$ , show that there can only be one set of the constants with j < k (for each choice of  $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R})$ ) such that the limit in (17.5) exists.

iiv) Use ii), and maybe iii), to show that

$$\frac{d}{dx}x_+^z = zx_+^{z-1} \text{ in } \mathcal{C}^{-\infty}(\mathbb{R}) \ \forall \ z \notin -\mathbb{N}_0 = \{0, 1, \dots\}.$$

- v) Similarly show that  $xx_+^z = x_+^{z+1}$  for all  $z \notin -\mathbb{N}$ . vi) Show that  $x_+^z = 0$  in x < 0 for all  $z \notin -\mathbb{N}$ . (Duh.)

Problem 49. [Null space of  $x \frac{d}{dx} - z$ ]

- i) Show that if  $u \in \mathcal{C}^{-\infty}(\mathbb{R})$  then  $\tilde{u}(\phi) = u(\tilde{\phi})$ , where  $\tilde{\phi}(x) =$  $\phi(-x) \ \forall \ \phi \in \mathcal{C}_c^{\infty}(\mathbb{R})$ , defines an element of  $\mathcal{C}^{-\infty}(\mathbb{R})$ . What is  $\tilde{u}$ if  $u \in \mathcal{C}^0(\mathbb{R})$ ? Compute  $\delta_0$ .
- ii) Show that  $\frac{d}{dx}\tilde{u} = -\frac{d}{dx}u$ .
- iii) Define  $x_-^z = \widetilde{x_+^z}$  for  $z \notin -\mathbb{N}$  and show that  $\frac{d}{dx}x_-^z = -zx_-^{z-1}$  and
- iv) Suppose that  $u \in \mathcal{C}^{-\infty}(\mathbb{R})$  satisfies the distributional equation  $(x\frac{d}{dx}-z)u=0$  (meaning of course,  $x\frac{du}{dx}=zu$  where z is a constant). Show that

$$u\big|_{x>0} = c_+ x_-^z\big|_{x>0}$$
 and  $u\big|_{x<0} = c_- x_-^z\big|_{x<0}$ 

for some constants  $c_{\pm}$ . Deduce that  $v = u - c_{+}x_{+}^{z} - c_{-}x_{-}^{z}$  satisfies

(17.6) 
$$(x\frac{d}{dx} - z)v = 0 \text{ and } \operatorname{supp}(v) \subset \{0\}.$$

- v) Show that for each  $k \in \mathbb{N}$ ,  $(x\frac{d}{dx} + k + 1)\frac{d^k}{dx^k}\delta_0 = 0$ . vi) Using the fact that any  $v \in \mathcal{C}^{-\infty}(\mathbb{R})$  with  $\operatorname{supp}(v) \subset \{0\}$  is a finite sum of constant multiples of the  $\frac{d^k}{dx^k}\delta_0$ , show that, for  $z \notin -\mathbb{N}$ , the only solution of (17.6) is v = 0.
- vii) Conclude that for  $z \notin -\mathbb{N}$

(17.7) 
$$\left\{ u \in \mathcal{C}^{-\infty}(\mathbb{R}); (x\frac{d}{dx} - z)u = 0 \right\}$$

is a two-dimensional vector space.

Problem 50. [Negative integral order] To do the same thing for negative integral order we need to work a little differently. Fix  $k \in \mathbb{N}$ .

i) We define weak convergence of distributions by saying  $u_n \to u$  in  $\mathcal{C}_c^{\infty}(X)$ , where  $u_n, u \in \mathcal{C}^{-\infty}(X), X \subset \mathbb{R}^n$  being open, if  $u_n(\phi) \to$  $u(\phi)$  for each  $\phi \in \mathcal{C}_c^{\infty}(X)$ . Show that  $u_n \to u$  implies that  $\frac{\partial u_n}{\partial x_i} \to \frac{\partial u}{\partial x_i}$  for each  $j = 1, \dots, n$  and  $fu_n \to fu$  if  $f \in \mathcal{C}^{\infty}(X)$ .

ii) Show that  $(z+k)x_+^z$  is weakly continuous as  $z \to -k$  in the sense that for any sequence  $z_n \to -k$ ,  $z_n \notin -\mathbb{N}$ ,  $(z_n+k)x_+^{z_n} \to v_k$  where

$$v_k = \frac{1}{-1} \cdots \frac{1}{-k+1} \frac{d^{k+1}}{dx^{k+1}} x_+, \ x_+ = x_+^1.$$

- iii) Compute  $v_k$ , including the constant factor.
- iv) Do the same thing for  $(z+k)x_-^z$  as  $z \to -k$ .
- v) Show that there is a linear combination  $(k+z)(x_+^z+c(k)x_-^z)$  such that as  $z \to -k$  the limit is zero.
- vi) If you get this far, show that in fact  $x_+^z + c(k)x_-^z$  also has a weak limit,  $u_k$ , as  $z \to -k$ . [This may be the hardest part.]
- vii) Show that this limit distribution satisfies  $(x\frac{d}{dx} + k)u_k = 0$ .
- viii) Conclude that (17.7) does in fact hold for  $z \in -\mathbb{N}$  as well. [There are still some things to prove to get this.]

Problem 51. Show that for any set  $G \subset \mathbb{R}^n$ 

$$v^*(G) = \inf \sum_{i=1}^{\infty} v(A_i)$$

where the infimum is taken over coverings of G by rectangular sets (products of intervals).

*Problem* 52. Show that a  $\sigma$ -algebra is closed under countable intersections.

*Problem* 53. Show that compact sets are Lebesgue measurable and have finite volume and also show the inner regularity of the Lebesgue measure on open sets, that is if E is open then

(17.8) 
$$v(E) = \sup\{v(K); K \subset E, K \text{ compact}\}.$$

*Problem* 54. Show that a set  $B \subset \mathbb{R}^n$  is Lebesgue measurable if and only if

$$v^*(E) = v^*(E \cap B) + v^*(E \cap B^{\mathbf{C}}) \ \forall \text{ open } E \subset \mathbb{R}^n.$$

[The definition is this for all  $E \subset \mathbb{R}^n$ .]

Problem 55. Show that a real-valued continuous function  $f: U \longrightarrow \mathbb{R}$  on an open set, is Lebesgue measurable, in the sense that  $f^{-1}(I) \subset U \subset \mathbb{R}^n$  is measurable for each interval I.

Problem 56. Hilbert space and the Riesz representation theorem. If you need help with this, it can be found in lots of places – for instance [6] has a nice treatment.

i) A pre-Hilbert space is a vector space V (over  $\mathbb{C}$ ) with a 'positive definite sesquilinear inner product' i.e. a function

$$V \times V \ni (v, w) \mapsto \langle v, w \rangle \in \mathbb{C}$$

satisfying

- $\bullet \langle w, v \rangle = \overline{\langle v, w \rangle}$
- $\langle a_1v_1 + a_2v_2, w \rangle = a_1\langle v_1, w \rangle + a_2\langle v_2, w \rangle$
- $\bullet \langle v, v \rangle \geq 0$
- $\bullet \langle v, v \rangle = 0 \Rightarrow v = 0.$

Prove Schwarz' inequality, that

$$|\langle u, v \rangle| \le \langle u \rangle^{\frac{1}{2}} \langle v \rangle^{\frac{1}{2}} \ \forall \ u, v \in V.$$

Hint: Reduce to the case  $\langle v, v \rangle = 1$  and then expand

$$\langle u - \langle u, v \rangle v, u - \langle u, v \rangle v \rangle \ge 0.$$

ii) Show that  $||v|| = \langle v, v \rangle^{1/2}$  is a norm and that it satisfies the parallelogram law:

$$(17.9) ||v_1 + v_2||^2 + ||v_1 - v_2||^2 = 2||v_1||^2 + 2||v_2||^2 \ \forall \ v_1, v_2 \in V.$$

iii) Conversely, suppose that V is a linear space over  $\mathbb{C}$  with a norm which satisfies (17.9). Show that

$$4\langle v, w \rangle = \|v + w\|^2 - \|v - w\|^2 + i\|v + iw\|^2 - i\|v - iw\|^2$$

defines a pre-Hilbert inner product which gives the original norm.

iv) Let V be a Hilbert space, so as in (i) but complete as well. Let  $C \subset V$  be a closed non-empty convex subset, meaning  $v, w \in C \Rightarrow (v+w)/2 \in C$ . Show that there exists a unique  $v \in C$  minimizing the norm, i.e. such that

$$||v|| = \inf_{w \in C} ||w||.$$

*Hint:* Use the parallelogram law to show that a norm minimizing sequence is Cauchy.

v) Let  $u: H \to \mathbb{C}$  be a continuous linear functional on a Hilbert space, so  $|u(\varphi)| \leq C||\varphi|| \; \forall \; \varphi \in H$ . Show that  $N = \{\varphi \in H; u(\varphi) = 0\}$  is closed and that if  $v_0 \in H$  has  $u(v_0) \neq 0$  then each  $v \in H$  can be written uniquely in the form

$$v = cv_0 + w, \ c \in \mathbb{C}, \ w \in N.$$

vi) With u as in v), not the zero functional, show that there exists a unique  $f \in H$  with u(f) = 1 and  $\langle w, f \rangle = 0$  for all  $w \in N$ . Hint: Apply iv) to  $C = \{g \in V; u(g) = 1\}$ .

vii) Prove the Riesz Representation theorem, that every continuous linear functional on a Hilbert space is of the form

$$u_f: H \ni \varphi \mapsto \langle \varphi, f \rangle$$
 for a unique  $f \in H$ .

Problem 57. Density of  $\mathcal{C}_c^{\infty}(\mathbb{R}^n)$  in  $L^p(\mathbb{R}^n)$ .

- i) Recall in a few words why simple integrable functions are dense in  $L^1(\mathbb{R}^n)$  with respect to the norm  $||f||_{L^1} = \int_{\mathbb{R}^n} |f(x)| dx$ .
- ii) Show that simple functions  $\sum_{j=1}^{N} c_j \chi(U_j)$  where the  $U_j$  are open and bounded are also dense in  $L^1(\mathbb{R}^n)$ .
- iii) Show that if U is open and bounded then  $F(y) = v(U \cap U_y)$ , where  $U_y = \{z \in \mathbb{R}^n : z = y + y', y' \in U\}$  is continuous in  $y \in \mathbb{R}^n$ and that

$$v(U \cap U_y^{\complement}) + v(U^{\complement} \cap U_y) \to 0 \text{ as } y \to 0.$$

iv) If U is open and bounded and  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  show that

$$f(x) = \int_{U} \varphi(x - y) dy \in \mathcal{C}_{c}^{\infty}(\mathbb{R}^{n}).$$

v) Show that if U is open and bounded then

$$\sup_{|y|<\delta} \int |\chi_U(x) - \chi_U(x-y)| dx \to 0 \text{ as } \delta \downarrow 0.$$

vi) If U is open and bounded and  $\varphi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n), \ \varphi \geq 0, \ \int \varphi = 1$ 

$$f_{\delta} \to \chi_U$$
 in  $L^1(\mathbb{R}^n)$  as  $\delta \downarrow 0$ 

where

$$f_{\delta}(x) = \delta^{-n} \int \varphi\left(\frac{y}{\delta}\right) \chi_U(x-y) dy.$$

*Hint:* Write  $\chi_U(x) = \delta^{-n} \int \varphi\left(\frac{y}{\delta}\right) \chi_U(x)$  and use v).

- vii) Conclude that  $C_c^{\infty}(\mathbb{R}^n)$  is dense in  $L^1(\mathbb{R}^n)$ . viii) Show that  $C_c^{\infty}(\mathbb{R}^n)$  is dense in  $L^p(\mathbb{R}^n)$  for any  $1 \leq p < \infty$ .

Problem 58. Schwartz representation theorem. Here we (well you) come to grips with the general structure of a tempered distribution.

i) Recall briefly the proof of the Sobolev embedding theorem and the corresponding estimate

$$\sup_{x \in \mathbb{R}^n} |\phi(x)| \le C \|\phi\|_{H^m}, \ \frac{n}{2} < m \in \mathbb{R}.$$

ii) For m = n + 1 write down a(n equivalent) norm on the right in a form that does not involve the Fourier transform.

iii) Show that for any  $\alpha \in \mathbb{N}_0$ 

$$|D^{\alpha}((1+|x|^2)^N\phi)| \le C_{\alpha,N} \sum_{\beta \le \alpha} (1+|x|^2)^N |D^{\beta}\phi|.$$

iv) Deduce the general estimates

Seduce the general estimates
$$\sup_{\substack{|\alpha| \leq N \\ x \in \mathbb{R}^n}} (1 + |x|^2)^N |D^{\alpha} \phi(x)| \leq C_N ||(1 + |x|^2)^N \phi||_{H^{N+n+1}}.$$

v) Conclude that for each tempered distribution  $u \in \mathcal{S}'(\mathbb{R}^n)$  there is an integer N and a constant C such that

$$|u(\phi)| \le C ||(1+|x|^2)^N \phi||_{H^{2N}} \ \forall \ \phi \in \mathcal{S}(\mathbb{R}^n).$$

vi) Show that  $v = (1 + |x|^2)^{-N} u \in \mathcal{S}'(\mathbb{R}^n)$  satisfies

$$|v(\phi)| \le C \|(1+|D|^2)^N \phi\|_{L^2} \ \forall \ \phi \in \mathcal{S}(\mathbb{R}^n).$$

- vi) Recall (from class or just show it) that if v is a tempered distribution then there is a unique  $w \in \mathcal{S}'(\mathbb{R}^n)$  such that  $(1 + |D|^2)^N w = v$ .
- vii) Use the Riesz Representation Theorem to conclude that for each tempered distribution u there exists N and  $w \in L^2(\mathbb{R}^n)$  such that

(17.10) 
$$u = (1 + |D|^2)^N (1 + |x|^2)^N w.$$

viii) Use the Fourier transform on  $\mathcal{S}'(\mathbb{R}^n)$  (and the fact that it is an isomorphism on  $L^2(\mathbb{R}^n)$ ) to show that any tempered distribution can be written in the form

$$u = (1 + |x|^2)^N (1 + |D|^2)^N w$$
 for some N and some  $w \in L^2(\mathbb{R}^n)$ .

ix) Show that any tempered distribution can be written in the form

$$u = (1+|x|^2)^N (1+|D|^2)^{N+n+1} \tilde{w}$$
 for some N and some  $\tilde{w} \in H^{2(n+1)}(\mathbb{R}^n)$ .

x) Conclude that any tempered distribution can be written in the form

$$u = (1 + |x|^2)^N (1 + |D|^2)^M U$$
 for some  $N, M$ 

and a bounded continuous function U

*Problem* 59. Distributions of compact support.

i) Recall the definition of the support of a distribution, defined in terms of its complement

$$\mathbb{R}^n \backslash \mathrm{supp}(u) = \left\{ p \in \mathbb{R}^n; \exists \ U \subset \mathbb{R}^n, \text{ open, with } p \in U \text{ such that } u \big|_U = 0 \right\}$$

ii) Show that if  $u \in \mathcal{C}^{-\infty}(\mathbb{R}^n)$  and  $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  satisfy

$$\operatorname{supp}(u) \cap \operatorname{supp}(\phi) = \emptyset$$

then  $u(\phi) = 0$ .

iii) Consider the space  $C^{\infty}(\mathbb{R}^n)$  of all smooth functions on  $\mathbb{R}^n$ , without restriction on supports. Show that for each N

$$||f||_{(N)} = \sup_{|\alpha| \le N, |x| \le N} |D^{\alpha} f(x)|$$

is a seminorn on  $C^{\infty}(\mathbb{R}^n)$  (meaning it satisfies  $||f|| \geq 0$ , ||cf|| = |c|||f|| for  $c \in \mathbb{C}$  and the triangle inequality but that ||f|| = 0 does not necessarily imply that f = 0.)

- iv) Show that  $C_c^{\infty}(\mathbb{R}^n) \subset C^{\infty}(\mathbb{R}^n)$  is dense in the sense that for each  $f \in C^{\infty}(\mathbb{R}^n)$  there is a sequence  $f_n$  in  $C_c^{\infty}(\mathbb{R}^n)$  such that  $||f f_n||_{(N)} \to 0$  for each N.
- v) Let  $\mathcal{E}'(\mathbb{R}^n)$  temporarily (or permanantly if you prefer) denote the dual space of  $\mathcal{C}^{\infty}(\mathbb{R}^n)$  (which is also written  $\mathcal{E}(\mathbb{R}^n)$ ), that is,  $v \in \mathcal{E}'(\mathbb{R}^n)$  is a linear map  $v : \mathcal{C}^{\infty}(\mathbb{R}^n) \longrightarrow \mathbb{C}$  which is continuous in the sense that for some N

$$(17.11) |v(f)| \le C||f||_{(N)} \,\forall f \in \mathcal{C}^{\infty}(\mathbb{R}^n).$$

Show that such a v 'is' a distribution and that the map  $\mathcal{E}'(\mathbb{R}^n) \longrightarrow \mathcal{C}^{-\infty}(\mathbb{R}^n)$  is injective.

- vi) Show that if  $v \in \mathcal{E}'(\mathbb{R}^n)$  satisfies (17.11) and  $f \in \mathcal{C}^{\infty}(\mathbb{R}^n)$  has f = 0 in  $|x| < N + \epsilon$  for some  $\epsilon > 0$  then v(f) = 0.
- vii) Conclude that each element of  $\mathcal{E}'(\mathbb{R}^n)$  has compact support when considered as an element of  $\mathcal{C}^{-\infty}(\mathbb{R}^n)$ .
- viii) Show the converse, that each element of  $\mathcal{C}^{-\infty}(\mathbb{R}^n)$  with compact support is an element of  $\mathcal{E}'(\mathbb{R}^n) \subset \mathcal{C}^{-\infty}(\mathbb{R}^n)$  and hence conclude that  $\mathcal{E}'(\mathbb{R}^n)$  'is' the space of distributions of compact support.

I will denote the space of distributions of compact support by  $\mathcal{C}_c^{-\infty}(\mathbb{R})$ .

Problem 60. Hypoellipticity of the heat operator  $H = iD_t + \Delta = iD_t + \sum_{j=1}^n D_{x_j}^2$  on  $\mathbb{R}^{n+1}$ .

- (1) Using  $\tau$  to denote the 'dual variable' to t and  $\xi \in \mathbb{R}^n$  to denote the dual variables to  $x \in \mathbb{R}^n$  observe that  $H = p(D_t, D_x)$  where  $p = i\tau + |\xi|^2$ .
- (2) Show that  $|p(\tau,\xi)| > \frac{1}{2} (|\tau| + |\xi|^2)$ .

(3) Use an inductive argument to show that, in  $(\tau, \xi) \neq 0$  where it makes sense,

(17.12) 
$$D_{\tau}^{k} D_{\xi}^{\alpha} \frac{1}{p(\tau, \xi)} = \sum_{j=1}^{|\alpha|} \frac{q_{k,\alpha,j}(\xi)}{p(\tau, \xi)^{k+j+1}}$$

where  $q_{k,\alpha,j}(\xi)$  is a polynomial of degree (at most)  $2j - |\alpha|$ . (4) Conclude that if  $\phi \in \mathcal{C}_c^{\infty}(\mathbb{R}^{n+1})$  is identically equal to 1 in a neighbourhood of 0 then the function

$$g(\tau,\xi) = \frac{1 - \phi(\tau,\xi)}{i\tau + |\xi|^2}$$

is the Fourier transform of a distribution  $F \in \mathcal{S}'(\mathbb{R}^n)$  with  $\operatorname{sing} \operatorname{supp}(F) \subset \{0\}$ . [Remember that  $\operatorname{sing} \operatorname{supp}(F)$  is the complement of the largest open subset of  $\mathbb{R}^n$  the restriction of F to which is smooth.

- (5) Show that F is a parametrix for the heat operator.
- (6) Deduce that  $iD_t + \Delta$  is hypoelliptic that is, if  $U \subset \mathbb{R}^n$  is an open set and  $u \in \mathcal{C}^{-\infty}(U)$  satisfies  $(iD_t + \Delta)u \in \mathcal{C}^{\infty}(U)$  then  $u \in \mathcal{C}^{\infty}(U)$ .
- (7) Show that  $iD_t \Delta$  is also hypoelliptic.

*Problem* 61. Wavefront set computations and more – all pretty easy, especially if you use results from class.

- i) Compute WF( $\delta$ ) where  $\delta \in \mathcal{S}'(\mathbb{R}^n)$  is the Dirac delta function at the origin.
- ii) Compute WF(H(x)) where  $H(x) \in \mathcal{S}'(\mathbb{R})$  is the Heaviside function

$$H(x) = \begin{cases} 1 & x > 0 \\ 0 & x \le 0 \end{cases}.$$

Hint:  $D_x$  is elliptic in one dimension, hit H with it.

- iii) Compute WF(E),  $E = iH(x_1)\delta(x')$  which is the Heaviside in the first variable on  $\mathbb{R}^n$ , n > 1, and delta in the others.
- iv) Show that  $D_{x_1}E = \delta$ , so E is a fundamental solution of  $D_{x_1}$ .
- v) If  $f \in \mathcal{C}_c^{-\infty}(\mathbb{R}^n)$  show that  $u = E \star f$  solves  $D_{x_1}u = f$ .
- vi) What does our estimate on  $WF(E \star f)$  tell us about WF(u) in terms of WF(f)?

*Problem* 62. The wave equation in two variables (or one spatial variable).

i) Recall that the Riemann function

$$E(t,x) = \begin{cases} -\frac{1}{4} & \text{if } t > x \text{ and } t > -x \\ 0 & \text{otherwise} \end{cases}$$

is a fundamental solution of  $D_t^2 - D_x^2$  (check my constant).

- ii) Find the singular support of E.
- iii) Write the Fourier transform (dual) variables as  $\tau, \xi$  and show that

WF(E) 
$$\subset \{0\} \times \mathbb{S}^1 \cup \{(t, x, \tau, \xi); x = t > 0 \text{ and } \xi + \tau = 0\}$$
  
  $\cup \{(t, x, \tau, \xi); -x = t > 0 \text{ and } \xi = \tau\}.$ 

- iv) Show that if  $f \in \mathcal{C}_c^{-\infty}(\mathbb{R}^2)$  then  $u = E \star f$  satisfies  $(D_t^2 D_x^2)u = f$ .
- v) With u defined as in iv) show that

$$\operatorname{supp}(u) \subset \{(t, x); \exists (t', x') \in \operatorname{supp}(f) \text{ with } t' + x' \leq t + x \text{ and } t' - x' \leq t - x\}.$$

- vi) Sketch an illustrative example of v).
- vii) Show that, still with u given by iv),

$$\operatorname{sing supp}(u) \subset \{(t, x); \exists (t', x') \in \operatorname{sing supp}(f) \text{ with}$$
  
 $t \geq t' \text{ and } t + x = t' + x' \text{ or } t - x = t' - x'\}.$ 

viii) Bound WF(u) in terms of WF(f).

Problem 63. A little uniqueness theorems. Suppose  $u \in \mathcal{C}_c^{-\infty}(\mathbb{R}^n)$  recall that the Fourier transform  $\hat{u} \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ . Now, suppose  $u \in \mathcal{C}_c^{-\infty}(\mathbb{R}^n)$  satisfies P(D)u = 0 for some non-trivial polynomial P, show that u = 0.

*Problem* 64. Work out the elementary behavior of the heat equation.

i) Show that the function on  $\mathbb{R} \times \mathbb{R}^n$ , for  $n \geq 1$ ,

$$F(t,x) = \begin{cases} t^{-\frac{n}{2}} \exp\left(-\frac{|x|^2}{4t}\right) & t > 0\\ 0 & t \le 0 \end{cases}$$

is measurable, bounded on the any set  $\{|(t,x)| \geq R\}$  and is integrable on  $\{|(t,x)| \leq R\}$  for any R > 0.

- ii) Conclude that F defines a tempered distibution on  $\mathbb{R}^{n+1}$ .
- iii) Show that F is  $\mathcal{C}^{\infty}$  outside the origin.
- iv) Show that F satisfies the heat equation

$$(\partial_t - \sum_{j=1}^n \partial_{x_j}^2) F(t, x) = 0 \text{ in } (t, x) \neq 0.$$

 $\mathbf{v}$ ) Show that F satisfies

(17.13) 
$$F(s^2t, sx) = s^{-n}F(t, x) \text{ in } \mathcal{S}'(\mathbb{R}^{n+1})$$

where the left hand side is defined by duality " $F(s^2t, sx) = F_s$ " where

$$F_s(\phi) = s^{-n-2} F(\phi_{1/s}), \ \phi_{1/s}(t, x) = \phi(\frac{t}{s^2}, \frac{x}{s}).$$

vi) Conclude that

$$(\partial_t - \sum_{j=1}^n \partial_{x_j}^2) F(t, x) = G(t, x)$$

where G(t, x) satisfies

(17.14) 
$$G(s^{2}t, sx) = s^{-n-2}G(t, x) \text{ in } \mathcal{S}'(\mathbb{R}^{n+1})$$

in the same sense as above and has support at most  $\{0\}$ .

vii) Hence deduce that

(17.15) 
$$(\partial_t - \sum_{j=1}^n \partial_{x_j}^2) F(t, x) = c\delta(t)\delta(x)$$

for some real constant c.

Hint: Check which distributions with support at (0,0) satisfy (17.14).

- viii) If  $\psi \in \mathcal{C}_c^{\infty}(\mathbb{R}^{n+1})$  show that  $u = F \star \psi$  satisfies
- (17.16)  $u \in \mathcal{C}^{\infty}(\mathbb{R}^{n+1})$  and  $\sup_{x \in \mathbb{R}^n, \ t \in [-S,S]} (1+|x|)^N |D^{\alpha}u(t,x)| < \infty \ \forall \ S > 0, \alpha \in \mathbb{N}^{n+1}, \ N.$ 
  - ix) Supposing that u satisfies (17.16) and is a real-valued solution of

$$(\partial_t - \sum_{j=1}^n \partial_{x_j}^2) u(t, x) = 0$$

in  $\mathbb{R}^{n+1}$ , show that

$$v(t) = \int_{\mathbb{R}^n} u^2(t, x)$$

is a non-increasing function of t.

Hint: Multiply the equation by u and integrate over a slab  $[t_1, t_2] \times \mathbb{R}^n$ .

- x) Show that c in (17.15) is non-zero by arriving at a contradiction from the assumption that it is zero. Namely, show that if c=0 then u in viii) satisfies the conditions of ix) and also vanishes in t < T for some T (depending on  $\psi$ ). Conclude that u=0 for all  $\psi$ . Using properties of convolution show that this in turn implies that F=0 which is a contradiction.
- xi) So, finally, we know that  $E = \frac{1}{c}F$  is a fundamental solution of the heat operator which vanishes in t < 0. Explain why this allows us to show that for any  $\psi \in \mathcal{C}_c^{\infty}(\mathbb{R} \times \mathbb{R}^n)$  there is a solution of

(17.17) 
$$(\partial_t - \sum_{j=1}^n \partial_{x_j}^2) u = \psi, \ u = 0 \text{ in } t < T \text{ for some } T.$$

What is the largest value of T for which this holds?

xii) Can you give a heuristic, or indeed a rigorous, explanation of why

$$c = \int_{\mathbb{R}^n} \exp(-\frac{|x|^2}{4}) dx?$$

xiii) Explain why the argument we used for the wave equation to show that there is *only one* solution,  $u \in \mathcal{C}^{\infty}(\mathbb{R}^{n+1})$ , of (17.17) does not apply here. (Indeed such uniqueness does not hold without some growth assumption on u.)

*Problem* 65. (Poisson summation formula) As in class, let  $L \subset \mathbb{R}^n$  be an integral lattice of the form

$$L = \left\{ v = \sum_{j=1}^{n} k_j v_j, \ k_j \in \mathbb{Z} \right\}$$

where the  $v_j$  form a basis of  $\mathbb{R}^n$  and using the dual basis  $w_j$  (so  $w_j \cdot v_i = \delta_{ij}$  is 0 or 1 as  $i \neq j$  or i = j) set

$$L^{\circ} = \left\{ w = 2\pi \sum_{j=1}^{n} k_j w_j, \ k_j \in \mathbb{Z} \right\}.$$

Recall that we defined

$$(17.18) \quad \mathcal{C}^{\infty}(\mathbb{T}_L) = \{ u \in \mathcal{C}^{\infty}(\mathbb{R}^n); u(z+v) = u(z) \ \forall \ z \in \mathbb{R}^n, \ v \in L \}.$$

i) Show that summation over shifts by lattice points:

$$(17.19) A_L : \mathcal{S}(\mathbb{R}^n) \ni f \longmapsto A_L f(z) = \sum_{v \in L} f(z - v) \in \mathcal{C}^{\infty}(\mathbb{T}_L).$$

defines a map into smooth periodic functions.

- ii) Show that there exists  $f \in \mathcal{C}_c^{\infty}(\mathbb{R}^n)$  such that  $A_L f \equiv 1$  is the costant function on  $\mathbb{R}^n$ .
- iii) Show that the map (17.19) is surjective. Hint: Well obviously enough use the f in part ii) and show that if u is periodic then  $A_L(uf) = u$ .
- iv) Show that the infinite sum

(17.20) 
$$F = \sum_{v \in L} \delta(\cdot - v) \in \mathcal{S}'(\mathbb{R}^n)$$

does indeed define a tempered distribution and that F is Lperiodic and satisfies  $\exp(iw \cdot z)F(z) = F(z)$  for each  $w \in L^{\circ}$ with equality in  $\mathcal{S}'(\mathbb{R}^n)$ .

v) Deduce that  $\hat{F}$ , the Fourier transform of F, is  $L^{\circ}$  periodic, conclude that it is of the form

(17.21) 
$$\hat{F}(\xi) = c \sum_{w \in L^{\circ}} \delta(\xi - w)$$

- vi) Compute the constant c.
- vii) Show that  $A_L(f) = F \star f$ .
- viii) Using this, or otherwise, show that  $A_L(f) = 0$  in  $\mathcal{C}^{\infty}(\mathbb{T}_L)$  if and only if  $\hat{f} = 0$  on  $L^{\circ}$ .

Problem 66. For a measurable set  $\Omega \subset \mathbb{R}^n$ , with non-zero measure, set  $H = L^2(\Omega)$  and let  $\mathcal{B} = \mathcal{B}(H)$  be the algebra of bounded linear operators on the Hilbert space H with the norm on  $\mathcal{B}$  being

$$(17.22) ||B||_{\mathcal{B}} = \sup\{||Bf||_{H}; f \in H, ||f||_{H} = 1\}.$$

- i) Show that  $\mathcal{B}$  is complete with respect to this norm. Hint (probably not necessary!) For a Cauchy sequence  $\{B_n\}$  observe that  $B_n f$  is Cauchy for each  $f \in H$ .
- ii) If  $V \subset H$  is a finite-dimensional subspace and  $W \subset H$  is a closed subspace with a finite-dimensional complement (that is W+U=H for some finite-dimensional subspace U) show that there is a closed subspace  $Y \subset W$  with finite-dimensional complement (in H) such that  $V \perp Y$ , that is  $\langle v, y \rangle = 0$  for all  $v \in V$  and  $y \in Y$ .
- iii) If  $A \in \mathcal{B}$  has finite rank (meaning AH is a finite-dimensional vector space) show that there is a finite-dimensional space  $V \subset H$  such that  $AV \subset V$  and  $AV^{\perp} = \{0\}$  where

$$V^{\perp} = \{ f \in H; \langle f, v \rangle = 0 \ \forall \ v \in V \}.$$

Hint: Set R = AH, a finite dimensional subspace by hypothesis. Let N be the null space of A, show that  $N^{\perp}$  is finite dimensional. Try  $V = R + N^{\perp}$ .

- iv) If  $A \in \mathcal{B}$  has finite rank, show that  $(\operatorname{Id} zA)^{-1}$  exists for all but a finite set of  $\lambda \in \mathbb{C}$  (just quote some matrix theory). What might it mean to say in this case that  $(\operatorname{Id} zA)^{-1}$  is meromorphic in z? (No marks for this second part).
- v) Recall that  $\mathcal{K} \subset \mathcal{B}$  is the algebra of compact operators, defined as the closure of the space of finite rank operators. Show that  $\mathcal{K}$  is an ideal in  $\mathcal{B}$ .
- vi) If  $A \in \mathcal{K}$  show that

$$\operatorname{Id} + A = (\operatorname{Id} + B)(\operatorname{Id} + A')$$

where  $B \in \mathcal{K}$ ,  $(\mathrm{Id} + B)^{-1}$  exists and A' has finite rank. Hint: Use the invertibility of  $\mathrm{Id} + B$  when  $\|B\|_{\mathcal{B}} < 1$  proved in class.

vii) Conclude that if  $A \in \mathcal{K}$  then

$$\{f \in H; (\operatorname{Id} + A)f = 0\}$$
 and  $((\operatorname{Id} + A)H)^{\perp}$  are finite dimensional.

Problem 67. [Separable Hilbert spaces]

- i) (Gramm-Schmidt Lemma). Let  $\{v_i\}_{i\in\mathbb{N}}$  be a sequence in a Hilbert space H. Let  $V_j\subset H$  be the span of the first j elements and set  $N_j=\dim V_j$ . Show that there is an orthonormal sequence  $e_1,\ldots,e_j$  (finite if  $N_j$  is bounded above) such that  $V_j$  is the span of the first  $N_j$  elements. Hint: Proceed by induction over N such that the result is true for all j with  $N_j< N$ . So, consider what happens for a value of j with  $N_j=N_{j-1}+1$  and add element  $e_{N_j}\in V_j$  which is orthogonal to all the previous  $e_k$ 's.
- ii) A Hilbert space is separable if it has a countable dense subset (sometimes people say Hilbert space when they mean separable Hilbert space). Show that every separable Hilbert space has a complete orthonormal sequence, that is a sequence  $\{e_j\}$  such that  $\langle u, e_j \rangle = 0$  for all j implies u = 0.
- iii) Let  $\{e_j\}$  an orthonormal sequence in a Hilbert space, show that for any  $a_j \in \mathbb{C}$ ,

$$\|\sum_{j=1}^{N} a_j e_j\|^2 = \sum_{j=1}^{N} |a_j|^2.$$

iv) (Bessel's inequality) Show that if  $e_j$  is an orthormal sequence in a Hilbert space and  $u \in H$  then

$$\|\sum_{j=1}^{N} \langle u, e_j \rangle e_j \|^2 \le \|u\|^2$$

and conclude (assuming the sequence of  $e_j$ 's to be infinite) that the series

$$\sum_{j=1}^{\infty} \langle u, e_j \rangle e_j$$

converges in H.

v) Show that if  $e_j$  is a complete orthonormal basis in a separable Hilbert space then, for each  $u \in H$ ,

$$u = \sum_{j=1}^{\infty} \langle u, e_j \rangle e_j.$$

*Problem* 68. [Compactness] Let's agree that a compact set in a metric space is one for which every open cover has a finite subcover. You may use the compactness of closed bounded sets in a finite dimensional vector space.

- i) Show that a compact subset of a Hilbert space is closed and bounded.
- ii) If  $e_j$  is a complete orthonormal subspace of a separable Hilbert space and K is compact show that given  $\epsilon > 0$  there exists N such that

(17.23) 
$$\sum_{j>N} |\langle u, e_j \rangle|^2 \le \epsilon \ \forall \ u \in K.$$

- iii) Conversely show that any closed bounded set in a separable Hilbert space for which (17.23) holds for some orthonormal basis is indeed compact.
- iv) Show directly that any sequence in a compact set in a Hilbert space has a convergent subsequence.
- v) Show that a subspace of H which has a precompact unit ball must be finite dimensional.
- vi) Use the existence of a complete orthonormal basis to show that any bounded sequence  $\{u_j\}$ ,  $\|u_j\| \leq C$ , has a weakly convergent subsequence, meaning that  $\langle v, u_j \rangle$  converges in  $\mathbb C$  along the subsequence for each  $v \in H$ . Show that the subsequence can be chosen so that  $\langle e_k, u_j \rangle$  converges for each k, where  $e_k$  is the complete orthonormal sequence.

Problem 69. [Spectral theorem, compact case] Recall that a bounded operator A on a Hilbert space H is compact if  $A\{||u|| \leq 1\}$  is precompact (has compact closure). Throughout this problem A will be a compact operator on a separable Hilbert space, H.

i) Show that if  $0 \neq \lambda \in \mathbb{C}$  then

$$E_{\lambda} = \{ u \in H; Au = \lambda u \}.$$

is finite dimensional.

- ii) If A is self-adjoint show that all eigenvalues (meaning  $E_{\lambda} \neq \{0\}$ ) are real and that different eigenspaces are orthogonal.
- iii) Show that  $\alpha_A = \sup\{|\langle Au, u \rangle|^2\}; ||u|| = 1\}$  is attained. Hint: Choose a sequence such that  $|\langle Au_j, u_j \rangle|^2$  tends to the supremum, pass to a weakly convergent sequence as discussed above and then using the compactness to a further subsequence such that  $Au_j$  converges.
- iv) If v is such a maximum point and  $f \perp v$  show that  $\langle Av, f \rangle + \langle Af, v \rangle = 0$ .
- v) If A is also self-adjoint and u is a maximum point as in iii) deduce that  $Au = \lambda u$  for some  $\lambda \in \mathbb{R}$  and that  $\lambda = \pm \alpha$ .
- vi) Still assuming A to be self-adjoint, deduce that there is a finite-dimensional subspace  $M \subset H$ , the sum of eigenspaces with eigenvalues  $\pm \alpha$ , containing all the maximum points.
- vii) Continuing vi) show that A restricts to a self-adjoint bounded operator on the Hilbert space  $M^{\perp}$  and that the supremum in iii) for this new operator is smaller.
- viii) Deduce that for any compact self-adjoint operator on a separable Hilbert space there is a complete orthonormal basis of eigenvectors. Hint: Be careful about the null space it could be big.

Problem 70. Show that a (complex-valued) square-integrable function  $u \in L^2(\mathbb{R}^n)$  is continuous in the mean, in the sense that

(17.24) 
$$\lim_{\epsilon \downarrow 0} \sup_{|y| < \epsilon} \int |u(x+y) - u(x)|^2 dx = 0.$$

Hint: Show that it is enough to prove this for non-negative functions and then that it suffices to prove it for non-negative simple functions and finally that it is enough to check it for the characteristic function of an open set of finite measure. Then use Problem 57 to show that it is true in this case.

Problem 71. [Ascoli-Arzela] Recall the proof of the theorem of Ascoli and Arzela, that a subset of  $\mathcal{C}_0^0(\mathbb{R}^n)$  is precompact (with respect to the

supremum norm) if and only if it is equicontinuous and equi-small at infinity, i.e. given  $\epsilon>0$  there exists  $\delta>0$  such that for all elements  $u\in B$ 

(17.25)

$$|y| < \delta \Longrightarrow \sup_{x \in \mathbb{R}^n} |u(x+y) = u(x)| < \epsilon \text{ and } |x| > 1/\delta \Longrightarrow |u(x)| < \epsilon.$$

Problem 72. [Compactness of sets in  $L^2(\mathbb{R}^n)$ .] Show that a subset  $B \subset L^2(\mathbb{R}^n)$  is precompact in  $L^2(\mathbb{R}^n)$  if and only if it satisfies the following two conditions:

i) (Equi-continuity in the mean) For each  $\epsilon>0$  there exists  $\delta>0$  such that

(17.26) 
$$\int_{\mathbb{R}^n} |u(x+y) - u(x)|^2 dx < \epsilon \ \forall \ |y| < \delta, \ u \in B.$$

ii) (Equi-smallness at infinity) For each  $\epsilon > 0$  there exists R such that

(17.27) 
$$\int_{|x|>R} |u|^2 dx < \epsilon \ \forall \ u \in B.$$

Hint: Problem 70 shows that (17.26) holds for each  $u \in L^2(\mathbb{R}^n)$ ; check that (17.27) also holds for each function. Then use a covering argument to prove that both these conditions must hold for a compact subset of  $L^2(\mathbb{R})$  and hence for a precompact set. One method to prove the converse is to show that if (17.26) and (17.27) hold then B is bounded and to use this to extract a weakly convergent sequence from any given sequence in B. Next show that (17.26) is equivalent to (17.27) for the set  $\mathcal{F}(B)$ , the image of B under the Fourier transform. Show, possibly using Problem 71, that if  $\chi_R$  is cut-off to a ball of radius R then  $\chi_R \mathcal{G}(\chi_R \hat{u}_n)$  converges strongly if  $u_n$  converges weakly. Deduce from this that the weakly convergent subsequence in fact converges strongly so  $\bar{B}$  is sequently compact, and hence is compact.

Problem 73. Consider the space  $C_c(\mathbb{R}^n)$  of all continuous functions on  $\mathbb{R}^n$  with compact support. Thus each element vanishes in |x| > R for some R, depending on the function. We want to give this a toplogy in terms of which is complete. We will use the *inductive limit* topology. Thus the whole space can be written as a countable union (17.28)

$$C_{c}(\mathbb{R}^{n}) = \bigcup_{n} \{u : \mathbb{R}^{n}; u \text{ is continuous and } u(x) = 0 \text{ for } |x| > R\}.$$

Each of the space on the right is a Banach space for the supremum norm.

- (1) Show that the supreumum norm is not complete on the whole of this space.
- (2) Define a subset  $U \subset \mathcal{C}_{c}(\mathbb{R}^{n})$  to be open if its intersection with each of the subspaces on the right in (17.28) is open w.r.t. the supremum norm.
- (3) Show that this definition does yield a topology.
- (4) Show that any sequence  $\{f_n\}$  which is 'Cauchy' in the sense that for any open neighbourhood U of 0 there exists N such that  $f_n f_m \in U$  for all  $n, m \geq N$ , is convergent (in the corresponding sense that there exists f in the space such that  $f f_n \in U$  eventually).
- (5) If you are determined, discuss the corresponding issue for nets.

Problem 74. Show that the continuity of a linear functional  $u: \mathcal{C}_c^{\infty}(\mathbb{R}^n) \longrightarrow \mathbb{C}$  with respect to the inductive limit topology defined in (6.16) means precisely that for each  $n \in \mathbb{N}$  there exists k = k(n) and  $C = C_n$  such that

$$(17.29) |u(\varphi)| \le C ||\varphi||_{\mathcal{C}^k}, \ \forall \ \varphi \in \dot{\mathcal{C}}^{\infty}(B(n)).$$

The point of course is that the 'order' k and the constnat C can both increase as n, measuring the size of the support, increases.

Problem 75. [Restriction from Sobolev spaces] The Sobolev embedding theorem shows that a function in  $H^m(\mathbb{R}^n)$ , for m > n/2 is continuous – and hence can be restricted to a subspace of  $\mathbb{R}^n$ . In fact this works more generally. Show that there is a well defined restriction map

(17.30) 
$$H^{m}(\mathbb{R}^{n}) \longrightarrow H^{m-\frac{1}{2}}(\mathbb{R}^{n}) \text{ if } m > \frac{1}{2}$$

with the following properties:

- (1) On  $\mathcal{S}(\mathbb{R}^n)$  it is given by  $u \longmapsto u(0, x'), x' \in \mathbb{R}^{n-1}$ .
- (2) It is continuous and linear.

Hint: Use the usual method of finding a weak version of the map on smooth Schwartz functions; namely show that in terms of the Fourier transforms on  $\mathbb{R}^n$  and  $\mathbb{R}^{n-1}$ 

(17.31) 
$$\widehat{u(0,\cdot)}(\xi') = (2\pi)^{-1} \int_{\mathbb{R}} \hat{u}(\xi_1, \xi') d\xi_1, \ \forall \ \xi' \in \mathbb{R}^{n-1}.$$

Use Cauchy's inequality to show that this is continuous as a map on Sobolev spaces as indicated and then the density of  $\mathcal{S}(\mathbb{R}^n)$  in  $H^m(\mathbb{R}^n)$  to conclude that the map is well-defined and unique.

Problem 76. [Restriction by WF] From class we know that the product of two distributions, one with compact support, is defined provided

they have no 'opposite' directions in their wavefront set:

$$(17.32) \quad (x,\omega) \in \mathrm{WF}(u) \Longrightarrow (x,-\omega) \notin \mathrm{WF}(v) \text{ then } uv \in \mathcal{C}_c^{-\infty}(\mathbb{R}^n).$$

Show that this product has the property that f(uv) = (fu)v = u(fv) if  $f \in \mathcal{C}^{\infty}(\mathbb{R}^n)$ . Use this to define a restriction map to  $x_1 = 0$  for distributions of compact support satisfying  $((0, x'), (\omega_1, 0)) \notin WF(u)$  as the product

$$(17.33) u_0 = u\delta(x_1).$$

[Show that  $u_0(f)$ ,  $f \in \mathcal{C}^{\infty}(\mathbb{R}^n)$  only depends on  $f(0,\cdot) \in \mathcal{C}^{\infty}(\mathbb{R}^{n-1})$ .

Problem 77. [Stone's theorem] For a bounded self-adjoint operator A show that the spectral measure can be obtained from the resolvent in the sense that for  $\phi, \psi \in H$ 

(17.34) 
$$\lim_{\epsilon \downarrow 0} \frac{1}{2\pi i} \langle [(A - t - i\epsilon)^{-1} - (A + t + i\epsilon)^{-1}] \phi, \psi \rangle \longrightarrow \mu_{\phi,\psi}$$

in the sense of distributions – or measures if you are prepared to work harder!

Problem 78. If  $u \in \mathcal{S}(\mathbb{R}^n)$  and  $\psi' = \psi_R + \mu$  is, as in the proof of Lemma 12.5, such that

$$\operatorname{supp}(\psi') \cap \operatorname{Css}(u) = \emptyset$$

show that

$$S(\mathbb{R}^n) \ni \phi \longmapsto \phi \psi' u \in S(\mathbb{R}^n)$$

is continuous and hence (or otherwise) show that the functional  $u_1u_2$  defined by (12.20) is an element of  $\mathcal{S}'(\mathbb{R}^n)$ .

*Problem* 79. Under the conditions of Lemma 12.10 show that (17.35)

$$Css(u*v) \cap \mathbb{S}^{n-1} \subset \{ \frac{sx + ty}{|sx + ty|}, |x| = |y| = 1, x \in Css(u), y \in Css(v), 0 \le s, t \le 1 \}.$$

Notice that this make sense exactly because sx + ty = 0 implies that t/s = 1 but  $x + y \neq 0$  under these conditions by the assumption of Lemma 12.10.

Problem 80. Show that the pairing u(v) of two distributions  $u, v \in {}^{\mathrm{b}}S'(\mathbb{R}^n)$  may be defined under the hypothesis (12.50).

Problem 81. Show that under the hypothesis (12.51)

(17.36)

$$WF_{sc}(u*v) \subset \{(x+y,p); (x,p) \in WF_{sc}(u) \cap (\mathbb{R}^n \times \mathbb{S}^{n-1}), (y,p) \in WF_{sc}(v) \cap (\mathbb{R}^n \times \mathbb{S}^{n-1})\}$$

$$\cup \{(\theta,q) \in \mathbb{S}^{n-1} \times \mathbb{B}^n; \theta = \frac{s'\theta' + s''\theta''}{|s'\theta' + s''\theta''|}, 0 \leq s', s'' \leq 1,$$

$$(\theta',q) \in WF_{sc}(u) \cap (\mathbb{S}^{n-1} \times \mathbb{B}^n), (\theta'',q) \in WF_{sc}(v) \cap (\mathbb{S}^{n-1} \times \mathbb{B}^n)\}.$$

Problem 82. Formulate and prove a bound similar to (17.36) for WF<sub>sc</sub>(uv) when  $u, v \in \mathcal{S}'(\mathbb{R}^n)$  satisfy (12.50).

*Problem* 83. Show that for convolution u \* v defined under condition (12.51) it is still true that

(17.37) 
$$P(D)(u * v) = (P(D)u) * v = u * (P(D)v).$$

*Problem* 84. Using Problem 80 (or otherwise) show that integration is defined as a functional

$$\{u \in \mathcal{S}'(\mathbb{R}^n); (\mathbb{S}^{n-1} \times \{0\}) \cap \operatorname{WF}_{\operatorname{sc}}(u) = \emptyset\} \longrightarrow \mathbb{C}.$$

If u satisfies this condition, show that  $\int P(D)u = c \int u$  where c is the constant term in P(D), i.e. P(D)1 = c.

Problem 85. Compute  $WF_{sc}(E)$  where E = C/|x-y| is the standard fundamental solution for the Laplacian on  $\mathbb{R}^3$ . Using Problem 83 give a condition on  $WF_{sc}(f)$  under which u = E \* f is defined and satisfies  $\Delta u = f$ . Show that under this condition  $\int f$  is defined using Problem 84. What can you say about  $WF_{sc}(u)$ ? Why is it not the case that  $\int \Delta u = 0$ , even though this is true if u has compact support?

# 18. Solutions to (some of) the problems

Solution 18.1 (To Problem 10). (by Matjaž Konvalinka).

Since the topology on  $\mathbb{N}$ , inherited from  $\mathbb{R}$ , is discrete, a set is compact if and only if it is finite. If a sequence  $\{x_n\}$  (i.e. a function  $\mathbb{N} \to \mathbb{C}$ ) is in  $\mathcal{C}_0(\mathbb{N})$  if and only if for any  $\epsilon > 0$  there exists a compact (hence finite) set  $F_{\epsilon}$  so that  $|x_n| < \epsilon$  for any n not in  $F_{\epsilon}$ . We can assume that  $F_{\epsilon} = \{1, \ldots, n_{\epsilon}\}$ , which gives us the condition that  $\{x_n\}$  is in  $\mathcal{C}_0(\mathbb{N})$  if and only if it converges to 0. We denote this space by  $c_0$ , and the supremum norm by  $\|\cdot\|_0$ . A sequence  $\{x_n\}$  will be abbreviated to x.

Let  $l^1$  denote the space of (real or complex) sequences x with a finite 1-norm

$$||x||_1 = \sum_{n=1}^{\infty} |x_n|.$$

We can define pointwise summation and multiplication with scalars, and  $(l^1, \|\cdot\|_1)$  is a normed (in fact Banach) space. Because the functional

$$y \mapsto \sum_{n=1}^{\infty} x_n y_n$$

is linear and bounded  $(|\sum_{n=1}^{\infty} x_n y_n| \le \sum_{n=1}^{\infty} |x_n| |y_n| \le ||x||_0 ||y||_1)$  by  $||x||_0$ , the mapping

$$\Phi \colon l^1 \longmapsto c_0^*$$

defined by

$$x \mapsto \left( y \mapsto \sum_{n=1}^{\infty} x_n y_n \right)$$

is a (linear) well-defined mapping with norm at most 1. In fact,  $\Phi$  is an isometry because if  $|x_j| = ||x||_0$  then  $|\Phi(x)(e_j)| = 1$  where  $e_j$  is the j-th unit vector. We claim that  $\Phi$  is also surjective (and hence an isometric isomorphism). If  $\varphi$  is a functional on  $c_0$  let us denote  $\varphi(e_j)$  by  $x_j$ . Then  $\Phi(x)(y) = \sum_{n=1}^{\infty} \varphi(e_n)y_n = \sum_{n=1}^{\infty} \varphi(y_n e_n) = \varphi(y)$  (the last equality holds because  $\sum_{n=1}^{\infty} y_n e_n$  converges to y in  $c_0$  and  $\varphi$  is continuous with respect to the topology in  $c_0$ , so  $\Phi(x) = \varphi$ .

Solution 18.2 (To Problem 29). (Matjaž Konvalinka) Since

$$D_x H(\varphi) = H(-D_x \varphi) = i \int_{-\infty}^{\infty} H(x) \varphi'(x) dx = i \int_{0}^{\infty} \varphi'(x) dx = i (0 - \varphi(0)) = -i \delta(\varphi),$$

we get  $D_x H = C\delta$  for C = -i.

Solution 18.3 (To Problem 40). (Matjaž Konvalinka) Let us prove this in the case where n=1. Define (for  $b \neq 0$ )

$$U(x) = u(b) - u(x) - (b - x)u'(x) - \dots - \frac{(b - x)^{k-1}}{(k-1)!}u^{(k-1)}(x);$$

then

$$U'(x) = -\frac{(b-x)^{k-1}}{(k-1)!}u^{(k)}(x).$$

For the continuously differentiable function  $V(x) = U(x) - (1-x/b)^k U(0)$  we have V(0) = V(b) = 0, so by Rolle's theorem there exists  $\zeta$  between 0 and b with

$$V'(\zeta) = U'(\zeta) + \frac{k(b-\zeta)^{k-1}}{b^k}U(0) = 0$$

Then

$$U(0) = -\frac{b^k}{k(b-\zeta)^{k-1}}U'(\zeta),$$

$$u(b) = u(0) + u'(0)b + \ldots + \frac{u^{(k-1)}(0)}{(k-1)!}b^{k-1} + \frac{u^{(k)}(\zeta)}{k!}b^{k}.$$

The required decomposition is u(x) = p(x) + v(x) for

$$p(x) = u(0) + u'(0)x + \frac{u''(0)}{2}x^2 + \dots + \frac{u^{(k-1)}(0)}{(k-1)!}x^{k-1} + \frac{u^{(k)}(0)}{k!}x^k,$$
$$v(x) = u(x) - p(x) = \frac{u^{(k)}(\zeta) - u^{(k)}(0)}{k!}x^k$$

for  $\zeta$  between 0 and x, and since  $u^{(k)}$  is continuous,  $(u(x) - p(x))/x^k$  tends to 0 as x tends to 0.

The proof for general n is not much more difficult. Define the function  $w_x \colon I \to \mathbb{R}$  by  $w_x(t) = u(tx)$ . Then  $w_x$  is k-times continuously differentiable,

$$w_x'(t) = \sum_{i=1}^n \frac{\partial u}{\partial x_i}(tx)x_i,$$

$$w_x''(t) = \sum_{i,j=1}^n \frac{\partial^2 u}{\partial x_i \partial x_j}(tx)x_i x_j,$$

$$w_x^{(l)}(t) = \sum_{l_1+l_2+\dots+l_i=l} \frac{l!}{l_1! l_2! \cdots l_i!} \frac{\partial^l u}{\partial x_1^{l_1} \partial x_2^{l_2} \cdots \partial x_i^{l_i}}(tx)x_1^{l_1} x_2^{l_2} \cdots x_i^{l_i}$$

so by above  $u(x) = w_x(1)$  is the sum of some polynomial p (od degree k), and we have

$$\frac{u(x) - p(x)}{|x|^k} = \frac{v_x(1)}{|x|^k} = \frac{w_x^{(k)}(\zeta_x) - w_x^{(k)}(0)}{k!|x|^k},$$

so it is bounded by a positive combination of terms of the form

$$\left| \frac{\partial^l u}{\partial x_1^{l_1} \partial x_2^{l_2} \cdots \partial x_i^{l_i}} (\zeta_x x) - \frac{\partial^l u}{\partial x_1^{l_1} \partial x_2^{l_2} \cdots \partial x_i^{l_i}} (0) \right|$$

with  $l_1 + \ldots + l_i = k$  and  $0 < \zeta_x < 1$ . This tends to zero as  $x \to 0$ because the derivative is continuous.

Solution 18.4 (Solution to Problem 41). (Matjž Konvalinka) Obviously the map  $\mathcal{C}_0(\mathbb{B}^n) \to \mathcal{C}(\mathbb{B}^n)$  is injective (since it is just the inclusion map), and  $f \in \mathcal{C}(\mathbb{B}^n)$  is in  $\mathcal{C}_0(\mathbb{B}^n)$  if and only if it is zero on  $\partial \mathbb{B}^n$ , ie. if and only if  $f|_{\mathbb{S}^{n-1}}=0$ . It remains to prove that any map g on  $\mathbb{S}^{n-1}$  is the restriction of a continuous function on  $\mathbb{B}^n$ . This is clear since

$$f(x) = \begin{cases} |x|g(x/|x|) & x \neq 0\\ 0 & x = 0 \end{cases}$$

is well-defined, coincides with f on  $\mathbb{S}^{n-1}$ , and is continuous: if M is the maximum of |g| on  $\mathbb{S}^{n-1}$ , and  $\epsilon > 0$  is given, then  $|f(x)| < \epsilon$  for  $|x| < \epsilon/M$ .

Solution 18.5. (partly Matjaž Konvalinka) For any  $\varphi \in \mathcal{S}(\mathbb{R})$  we have

$$\left| \int_{-\infty}^{\infty} \varphi(x)dx \right| \le \int_{-\infty}^{\infty} |\varphi(x)|dx \le \sup((1+x|^2)|\varphi(x)|) \int_{-\infty}^{\infty} (1+|x|^2)^{-1}dx$$
$$\le C \sup((1+x|^2)|\varphi(x)|).$$

Thus  $\mathcal{S}(\mathbb{R}) \ni \varphi \longmapsto \int_{\mathbb{R}} \varphi dx$  is continous. Now, choose  $\phi \in \mathcal{C}_{c}^{\circ}(\mathbb{R})$  with  $\int_{\mathbb{R}} \phi(x) dx = 1$ . Then, for  $\psi \in \mathcal{S}(\mathbb{R})$ , set

(18.1) 
$$A\psi(x) = \int_{-\infty}^{x} (\psi(t) - c(\psi)\phi(t)) \ dt, \ c(\psi) = \int_{-\infty}^{\infty} \psi(s) \ ds.$$

Note that the assumption on  $\phi$  means that

(18.2) 
$$A\psi(x) = -\int_{x}^{\infty} (\psi(t) - c(\psi)\phi(t)) dt$$

Clearly  $A\psi$  is smooth, and in fact it is a Schwartz function since

(18.3) 
$$\frac{d}{dx}(A\psi(x)) = \psi(x) - c\phi(x) \in \mathcal{S}(\mathbb{R})$$

so it suffices to show that  $x^k A \psi$  is bounded for any k as  $|x| \to \pm \infty$ . Since  $\psi(t) - c\phi(t) \le C_k t^{-k-1}$  in  $t \ge 1$  it follows from (18.2) that

$$|x^k A \psi(x)| \le C x^k \int_x^\infty t^{-k-1} dt \le C', \ k > 1, \ \text{in } x > 1.$$

A similar estimate as  $x \to -\infty$  follows from (18.1). Now, A is clearly linear, and it follows from the estimates above, including that on the integral, that for any k there exists C and j such that

$$\sup_{\alpha,\beta \le k} |x^{\alpha} D^{\beta} A \psi| \le C \sum_{\alpha',\beta' \le j} \sup_{x \in \mathbb{R}} |x^{\alpha'} D^{\beta'} \psi|.$$

Finally then, given  $u \in \mathcal{S}'(\mathbb{R})$  define  $v(\psi) = -u(A\psi)$ . From the continuity of  $A, v \in \mathcal{S}(\mathbb{R})$  and from the definition of  $A, A(\psi') = \psi$ . Thus

$$dv/dx(\psi) = v(-\psi') = u(A\psi') = u(\psi) \Longrightarrow \frac{dv}{dx} = u.$$

Solution 18.6. We have to prove that  $\langle \xi \rangle^{m+m'} \widehat{u} \in L_2(\mathbb{R}^n)$ , in other words, that

$$\int_{\mathbb{R}^n} \langle \xi \rangle^{2(m+m')} |\widehat{u}|^2 \, d\xi < \infty.$$

But that is true since

$$\int_{\mathbb{R}^n} \langle \xi \rangle^{2(m+m')} |\widehat{u}|^2 d\xi = \int_{\mathbb{R}^n} \langle \xi \rangle^{2m'} (1 + \xi_1^2 + \dots + \xi_n^2)^m |\widehat{u}|^2 d\xi =$$

$$= \int_{\mathbb{R}^n} \langle \xi \rangle^{2m'} \left( \sum_{|\alpha| \le m} C_\alpha \xi^{2\alpha} \right) |\widehat{u}|^2 d\xi = \sum_{|\alpha| \le m} C_\alpha \left( \int_{\mathbb{R}^n} \langle \xi \rangle^{2m'} \xi^{2\alpha} |\widehat{u}|^2 d\xi \right)$$

and since  $\langle \xi \rangle^{m'} \xi^{\alpha} \widehat{u} = \langle \xi \rangle^{m'} \widehat{D^{\alpha} u}$  is in  $L^{2}(\mathbb{R}^{n})$  (note that  $u \in H^{m}(\mathbb{R}^{n})$  follows from  $D^{\alpha}u \in H^{m'}(\mathbb{R}^{n})$ ,  $|\alpha| \leq m$ ). The converse is also true since  $C_{\alpha}$  in the formula above are strictly positive.

Solution 18.7. Take  $v \in L^2(\mathbb{R}^n)$ , and define subsets of  $\mathbb{R}^n$  by

$$E_0 = \{x \colon |x| \le 1\},\$$

$$E_i = \{x \colon |x| \ge 1, |x_i| = \max_j |x_j|\}.$$

Then obviously we have  $1 = \sum_{i=0}^{n} \chi_{E_j}$  a.e., and  $v = \sum_{j=0}^{n} v_j$  for  $v_j = \chi_{E_j} v$ . Then  $\langle x \rangle$  is bounded by  $\sqrt{2}$  on  $E_0$ , and  $\langle x \rangle v_0 \in L^2(\mathbb{R}^n)$ ; and on  $E_j$ ,  $1 \leq j \leq n$ , we have

$$\frac{\langle x \rangle}{|x_j|} \le \frac{(1+n|x_j|^2)^{1/2}}{|x_j|} = (n+1/|x_j|^2)^{1/2} \le (2n)^{1/2},$$

so  $\langle x \rangle v_j = x_j w_j$  for  $w_j \in L^2(\mathbb{R}^n)$ . But that means that  $\langle x \rangle v = w_0 + \sum_{j=1}^n x_j w_j$  for  $w_j \in L^2(\mathbb{R}^n)$ .

If u is in  $L^2(\mathbb{R}^n)$  then  $\widehat{u} \in L^2(\mathbb{R}^n)$ , and so there exist  $w_0, \ldots, w_n \in L^2(\mathbb{R}^n)$  so that

$$\langle \xi \rangle \widehat{u} = w_0 + \sum_{j=1}^n \xi_j w_j,$$

in other words

$$\widehat{u} = \widehat{u}_0 + \sum_{i=1}^n \xi_i \widehat{u}_i$$

where  $\langle \xi \rangle \widehat{u}_i \in L^2(\mathbb{R}^n)$ . Hence

$$u = u_0 + \sum_{j=1}^{n} D_j u_j$$

where  $u_i \in H^1(\mathbb{R}^n)$ .

Solution 18.8. Since

$$D_x H(\varphi) = H(-D_x \varphi) = i \int_{-\infty}^{\infty} H(x) \varphi'(x) dx = i \int_{0}^{\infty} \varphi'(x) dx = i(0 - \varphi(0)) = -i\delta(\varphi),$$
 we get  $D_x H = C\delta$  for  $C = -i$ .

Solution 18.9. It is equivalent to ask when  $\langle \xi \rangle^m \widehat{\delta_0}$  is in  $L^2(\mathbb{R}^n)$ . Since

$$\widehat{\delta_0}(\psi) = \delta_0(\widehat{\psi}) = \widehat{\psi}(0) = \int_{\mathbb{R}^n} \psi(x) \, dx = 1(\psi),$$

this is equivalent to finding m such that  $\langle \xi \rangle^{2m}$  has a finite integral over  $\mathbb{R}^n$ . One option is to write  $\langle \xi \rangle = (1+r^2)^{1/2}$  in spherical coordinates, and to recall that the Jacobian of spherical coordinates in n dimensions has the form  $r^{n-1}\Psi(\varphi_1,\ldots,\varphi_{n-1})$ , and so  $\langle \xi \rangle^{2m}$  is integrable if and only if

$$\int_0^\infty \frac{r^{n-1}}{(1+r^2)^m} \, dr$$

converges. It is obvious that this is true if and only if n-1-2m<-1, ie. if and only if m>n/2.

Solution 18.10 (Solution to Problem31). We know that  $\delta \in H^m(\mathbb{R}^n)$  for any m < -n/1. Thus is just because  $\langle \xi \rangle^p \in L^2(\mathbb{R}^n)$  when p < -n/2. Now, divide  $\mathbb{R}^n$  into n+1 regions, as above, being  $A_0 = \{\xi; |\xi| \leq 1 \text{ and } A_i = \{\xi; |\xi_i| = \sup_j |\xi_j|, |\xi| \geq 1\}$ . Let  $v_0$  have Fourier transform  $\chi_{A_0}$  and for  $i = 1, \ldots, n, v_i \in \mathcal{S}$ ; ( $\mathbb{R}^n$ ) have Fourier transforms  $\xi_i^{-n-1}\chi_{A_i}$ . Since  $|\xi_i| > c\langle \xi \rangle$  on the support of  $\widehat{v_i}$  for each  $i = 1, \ldots, n$ , each term

is in  $H^m$  for any m < 1 + n/2 so, by the Sobolev embedding theorem, each  $v_i \in \mathcal{C}^0_0(\mathbb{R}^n)$  and

(18.4) 
$$1 = \hat{v}_0 \sum_{i=1}^n \xi_i^{n+1} \hat{v}_i \Longrightarrow \delta = v_0 + \sum_i D_i^{n+1} v_i.$$

How to see that this cannot be done with n or less derivatives? For the moment I do not have a proof of this, although I believe it is true. Notice that we are actually proving that  $\delta$  can be written

(18.5) 
$$\delta = \sum_{|\alpha| < n+1} D^{\alpha} u_{\alpha}, \ u_{\alpha} \in H^{n/2}(\mathbb{R}^n).$$

This cannot be improved to n from n+1 since this would mean that  $\delta \in H^{-n/2}(\mathbb{R}^n)$ , which it isn't. However, what I am asking is a little more subtle than this.

### References

- [1] G.B. Folland, Real analysis, Wiley, 1984.
- [2] F. G. Friedlander, *Introduction to the theory of distributions*, second ed., Cambridge University Press, Cambridge, 1998, With additional material by M. Joshi. MR **2000g**:46002
- [3] J. Hadamard, Le problème de Cauchy et les èquatons aux dérivées partielles linéaires hyperboliques, Hermann, Paris, 1932.
- [4] L. Hörmander, *The analysis of linear partial differential operators*, vol. 3, Springer-Verlag, Berlin, Heidelberg, New York, Tokyo, 1985.
- [5] W. Rudin, Real and complex analysis, third edition ed., McGraw-Hill, 1987.
- [6] George F. Simmons, Introduction to topology and modern analysis, Robert E. Krieger Publishing Co. Inc., Melbourne, Fla., 1983, Reprint of the 1963 original. MR 84b:54002