# 18.175: Lecture 1 Probability spaces and $\sigma$ -algebras

Scott Sheffield

MIT

Probability spaces and  $\sigma\text{-algebras}$ 

Distributions on  $\ensuremath{\mathbb{R}}$ 

Probability spaces and  $\sigma\text{-algebras}$ 

Distributions on **P** 

#### Probability space notation

- ▶ **Probability space** is triple  $(\Omega, \mathcal{F}, P)$  where  $\Omega$  is sample space,  $\mathcal{F}$  is set of events (the  $\sigma$ -algebra) and  $P : \mathcal{F} \to [0,1]$  is the probability function.
- $\sigma$ -algebra is collection of subsets closed under complementation and countable unions. Call  $(\Omega, \mathcal{F})$  a measure space.
- ▶ **Measure** is function  $\mu : \mathcal{F} \to \mathbb{R}$  satisfying  $\mu(A) \ge \mu(\emptyset) = 0$  for all  $A \in \mathcal{F}$  and countable additivity:  $\mu(\cup_i A_i) = \sum_i \mu(A_i)$  for disjoint  $A_i$ .
- Measure  $\mu$  is **probability measure** if  $\mu(\Omega) = 1$ .


## Basic consequences of definitions

- ▶ monotonicity:  $A \subset B$  implies  $\mu(A) \leq \mu(B)$
- ▶ subadditivity:  $A \subset \bigcup_{m=1}^{\infty} A_m$  implies  $\mu(A) \leq \sum_{m=1}^{\infty} \mu(A_m)$ .
- ▶ **continuity from below:** measures of sets  $A_i$  in increasing sequence converge to measure of limit  $\bigcup_i A_i$
- ▶ **continuity from above:** measures of sets  $A_i$  in decreasing sequence converge to measure of intersection  $\cap_i A_i$

18.175 Lecture 1 5

# Why can't $\sigma$ -algebra be all subsets of $\Omega$ ?

- ▶ Uniform probability measure on [0,1) should satisfy **translation invariance:** If *B* and a horizontal translation of *B* are both subsets [0,1), their probabilities should be equal.
- ▶ Consider wrap-around translations  $\tau_r(x) = (x + r) \mod 1$ .
- ▶ By translation invariance,  $\tau_r(B)$  has same probability as B.
- ▶ Call x, y "equivalent modulo rationals" if x y is rational (e.g.,  $x = \pi 3$  and  $y = \pi 9/4$ ). An **equivalence class** is the set of points in [0,1) equivalent to some given point.
- ▶ There are uncountably many of these classes.
- Let  $A \subset [0,1)$  contain **one** point from each class. For each  $x \in [0,1)$ , there is **one**  $a \in A$  such that r = x a is rational.
- ▶ Then each x in [0,1) lies in  $\tau_r(A)$  for **one** rational  $r \in [0,1)$ .
- ▶ Thus  $[0,1) = \cup \tau_r(A)$  as r ranges over rationals in [0,1).
- ▶ If P(A) = 0, then  $P(S) = \sum_{r} P(\tau_r(A)) = 0$ . If P(A) > 0 then  $P(S) = \sum_{r} P(\tau_r(A)) = \infty$ . Contradicts P(S) = 1 axiom.

#### Three ways to get around this

- ▶ 1. Re-examine axioms of mathematics: the very existence of a set A with one element from each equivalence class is consequence of so-called axiom of choice. Removing that axiom makes paradox goes away, since one can just suppose (pretend?) these kinds of sets don't exist.
- ▶ 2. **Re-examine axioms of probability:** Replace *countable additivity* with *finite additivity*? (Look up Banach-Tarski.)
- 3. Keep the axiom of choice and countable additivity but don't define probabilities of all sets: Restrict attention to some σ-algebra of measurable sets.
- Most mainstream probability and analysis takes the third approach. But good to be aware of alternatives (e.g., axiom of determinacy which implies that all sets are Lebesgue measurable).

18.175 Lecture 1

### Borel $\sigma$ -algebra

- ▶ The **Borel**  $\sigma$ -algebra  $\mathcal{B}$  is the smallest  $\sigma$ -algebra containing all open intervals.
- $\blacktriangle$  Say that  ${\cal B}$  is "generated" by the collection of open intervals.
- ▶ Why does this notion make sense? If  $\mathcal{F}_i$  are  $\sigma$ -fields (for i in possibly uncountable index set I) does this imply that  $\bigcap_{i \in I} \mathcal{F}_i$  is a  $\sigma$ -field?

18.175 Lecture 1

Probability spaces and  $\sigma\text{-algebras}$ 

Distributions on  ${\mathbb R}$ 

18.175 Lecture 1 9

Probability spaces and  $\sigma$ -algebras

Distributions on  ${\mathbb R}$ 

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.175: Lecture 2

# Extension theorems: a tool for constructing measures

Scott Sheffield

MIT

Extension theorems

Distributions on  ${\mathbb R}$ 

Extension theorems

Distributions on R

#### Recall the dilemma

- ▶ Want, a priori, to define measure of *any* subsets of [0, 1).
- ▶ Find that if we allow the axiom of choice and require measures to be countably additive (as we do) then we run into trouble. No valid translation invariant way to assign a finite measure to all subsets of [0, 1).
- ▶ Could toss out the axiom of choice... but we don't want to. Instead we will only define measure for certain "measurable sets". We will construct a  $\sigma$ -algebra of measurable sets and let probability measure be function from  $\sigma$ -algebra to [0,1].
- Price to this decision: for the rest of our lives, whenever we talk about a measure on any space (a Euclidean space, a space of differentiable functions, a space of fractal curves embedded in a plane, etc.), we have to worry about what the  $\sigma$ -algebra might be.

#### Recall the dilemma

- ▶ On the other hand: always have to ensure that any measure we produce assigns actual number to every measurable set. A bigger  $\sigma$ -algebra means more sets whose measures have to be defined. So if we want to make it easy to construct measures, maybe it's a good thing if our  $\sigma$ -algebra doesn't have too many elements... unless it's easier to...
- Come to think of it, how do we define a measure anyway?
- ▶ If the  $\sigma$ -algebra is something like the Borel  $\sigma$ -algebra (smallest  $\sigma$ -algebra containing all open sets) it's a pretty big collection of sets. How do we go about producing a measure (any measure) that's defined for every set in this family?

Answer: use extension theorems.

#### Recall definitions

- ▶ **Probability space** is triple  $(\Omega, \mathcal{F}, P)$  where  $\Omega$  is sample space,  $\mathcal{F}$  is set of events (the  $\sigma$ -algebra) and  $P: \mathcal{F} \to [0,1]$  is the probability function.
- $\rightharpoonup \sigma$ -algebra is collection of subsets closed under complementation and countable unions. Call  $(\Omega, \mathcal{F})$  a measure space.
- ▶ Measure is function  $\mu : \mathcal{F} \to \mathbb{R}$  satisfying  $\mu(A) \ge \mu(\emptyset) = 0$  for all  $A \in \mathcal{F}$  and countable additivity:  $\mu(\cup_i A_i) = \sum_i \mu(A_i)$  for disjoint  $A_i$ .
- ▶ Measure  $\mu$  is **probability measure** if  $\mu(\Omega) = 1$ .
- ▶ The **Borel**  $\sigma$ -algebra  $\mathcal{B}$  on a topological space is the smallest  $\sigma$ -algebra containing all open sets.


Extension theorems

Distributions on  ${\mathbb R}$ 

Extension theorems

Distributions on  ${\mathbb R}$ 

# How do we produce measures on $\mathbb{R}$ ?

- ▶ Write  $F(a) = P((-\infty, a])$ .
- ▶ **Theorem:** for each right continuous, non-decreasing function F, tending to 0 at  $-\infty$  and to 1 at  $\infty$ , there is a unique measure defined on the Borel sets of  $\mathbb{R}$  with P((a, b]) = F(b) - F(a).
- ▶ If we're given such a function F, then we know how to compute the measure of any set of the form (a, b].
- We would like to extend the measure defined for these subsets to a measure defined for the whole  $\sigma$  algebra generated by these subsets.
- Seems clear how to define measure of countable union of disjoint intervals of the form (a, b] (just using countable additivity). But are we confident we can extend the definition to all Borel measurable sets in a consistent way?

Extension theorems

Distributions on  ${\mathbb R}$ 

Extension theorems

Distributions on R

# Algebras and semi-algebras

- ▶ algebra: collection A of sets closed under finite unions and complementation.
- ▶ measure on algebra: Have  $\mu(A) \ge \mu(\emptyset) = 0$  for all A in A, and for disjoint  $A_i$  with union in A we have  $\mu(\bigcup_{i=1}^{\infty} A_i) = \sum_{i=1}^{\infty} \mu(A_i)$  (countable additivity).
- ▶ Measure  $\mu$  on  $\mathcal{A}$  is  $\sigma$ -**finite** if exists countable collection  $A_n \in \mathcal{A}$  with  $\mu(A_n) < \infty$  and  $\cup A_n = \Omega$ .
- ▶ **semi-algebra**: collection S of sets closed under intersection and such that  $S \in S$  implies that  $S^c$  is a finite disjoint union of sets in S. (Example: empty set plus sets of form  $(a_1, b_1] \times \ldots \times (a_d, b_d] \in \mathbb{R}^d$ .)
- ▶ One lemma: If S is a semialgebra, then the set  $\overline{S}$  of finite disjoint unions of sets in S is an algebra, called the **algebra** generated by S.

## $\pi$ -systems and $\lambda$ -systems

- ▶ Say collection of sets  $\mathcal{P}$  is a  $\pi$ -system if closed under intersection.
- ▶ Say collection of sets  $\mathcal{L}$  is a  $\lambda$ -system if
  - $\rightharpoonup \Omega \in \mathcal{L}$
  - ▶ If  $A, B \in \mathcal{L}$  and  $A \subset B$ , then  $B A \in \mathcal{L}$ .
  - ▶ If  $A_n \in \mathcal{L}$  and  $A_n \uparrow A$  then  $A \in \mathcal{L}$ .
- ▶ THEOREM: If  $\mathcal{P}$  is a  $\pi$ -system and  $\mathcal{L}$  is a  $\lambda$ -system that contains  $\mathcal{P}$ , then  $\sigma(\mathcal{P}) \subset \mathcal{L}$ , where  $\sigma(\mathcal{A})$  denotes smallest  $\sigma$ -algebra containing  $\mathcal{A}$ .

# Caratheéodory Extension Theorem

- ▶ **Theorem:** If  $\mu$  is a  $\sigma$ -finite measure on an algebra  $\mathcal{A}$  then  $\mu$  has a unique extension to the  $\sigma$  algebra generated by  $\mathcal{A}$ .
- Detailed proof is somewhat involved, but let's take a look at it.
- We can use this extension theorem prove existence of a unique translation invariant measure (Lebesgue measure) on the Borel sets of  $\mathbb{R}^d$  that assigns unit mass to a unit cube. (Borel  $\sigma$ -algebra  $\mathcal{R}^d$  is the smallest one containing all open sets of  $\mathbb{R}^d$ . Given any space with a topology, we can define a  $\sigma$ -algebra this way.)


MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 3 Random variables and distributions

Scott Sheffield

MIT

Characterizing measures on  $\mathbb{R}^d$ 

Characterizing measures on  $\mathbb{R}^d$ 

### Recall definitions

- ▶ **Probability space** is triple  $(\Omega, \mathcal{F}, P)$  where  $\Omega$  is sample space,  $\mathcal{F}$  is set of events (the  $\sigma$ -algebra) and  $P: \mathcal{F} \to [0,1]$  is the probability function.
- $\rightharpoonup \sigma$ -algebra is collection of subsets closed under complementation and countable unions. Call  $(\Omega, \mathcal{F})$  a measure space.
- ▶ Measure is function  $\mu : \mathcal{F} \to \mathbb{R}$  satisfying  $\mu(A) \ge \mu(\emptyset) = 0$  for all  $A \in \mathcal{F}$  and countable additivity:  $\mu(\cup_i A_i) = \sum_i \mu(A_i)$  for disjoint  $A_i$ .
- ▶ Measure  $\mu$  is **probability measure** if  $\mu(\Omega) = 1$ .
- ▶ The **Borel**  $\sigma$ -algebra  $\mathcal{B}$  on a topological space is the smallest  $\sigma$ -algebra containing all open sets.

## Recall $\sigma$ -algebra story

- $\triangleright$  Want, a priori, to define measure of any subsets of [0,1).
- ▶ Find that if we allow the axiom of choice and require measures to be countably additive (as we do) then we run into trouble. No valid translation invariant way to assign a finite measure to all subsets of [0,1).
- Could toss out the axiom of choice... but we don't want to. Instead we only define measure for certain "measurable sets". We construct a  $\sigma$ -algebra of measurable sets and let probability measure be function from  $\sigma$ -algebra to [0,1].
- ▶ Borel  $\sigma$ -algebra is generated by open sets. Sometimes consider "completion" formed by tossing in measure zero sets.
- ▶ Caratheéodory Extension Theorem tells us that if we want to construct a measure on a  $\sigma$ -algebra, it is enough to construct the measure on an algebra that generates it.

## Recall construction of measures on $\mathbb{R}$

- Write  $F(a) = P((-\infty, a])$ .
- ▶ **Theorem:** for each right continuous, non-decreasing function F, tending to 0 at  $-\infty$  and to 1 at  $\infty$ , there is a unique measure defined on the Borel sets of  $\mathbb{R}$  with P((a,b]) = F(b) F(a).
- ▶ Proved using Caratheéodory Extension Theorem.


# Characterizing probability measures on $\mathbb{R}^d$

- ▶ Want to have  $F(x) = \mu(-\infty, x_1] \times (\infty, x_2] \times \ldots \times (-\infty, x_n]$ .
- ▶ Given such an F, can compute  $\mu$  of any finite rectangle of form  $\prod(a_i, b_i]$  by taking differences of F applied to vertices.
- ► Theorem: Given F, there is a unique measure whose values on finite rectangles are determined this way (provided that F is non-decreasing, right continuous, and assigns a non-negative value to each rectangle).


► Also proved using Caratheéodory Extension Theorem.

Characterizing measures on  $\mathbb{R}^d$ 

Characterizing measures on  $\mathbb{R}^{c}$ 

# Defining random variables

- ▶ Random variable is a *measurable* function from  $(\Omega, \mathcal{F})$  to  $(\mathbb{R}, \mathcal{B})$ . That is, a function  $X : \Omega \to \mathbb{R}$  such that the preimage of every set in  $\mathcal{B}$  is in  $\mathcal{F}$ . Say X is  $\mathcal{F}$ -measurable.
- ▶ Question: to prove X is measurable, is it enough to show that the pre-image of every open set is in  $\mathcal{F}$ ?
- ▶ **Theorem:** If  $X^{-1}(A) \in \mathcal{F}$  for all  $A \in \mathcal{A}$  and  $\mathcal{A}$  generates  $\mathcal{S}$ , then X is a measurable map from  $(\Omega, \mathcal{F})$  to  $(\mathcal{S}, \mathcal{S})$ .
- Example of random variable: indicator function of a set. Or sum of finitely many indicator functions of sets.
- ▶ Let  $F(x) = F_X(x) = P(X \le x)$  be distribution function for X. Write  $f = f_X = F_X'$  for density function of X.
- ▶ What functions can be distributions of random variables?
- Non-decreasing, right-continuous, with  $\lim_{x\to\infty} F(x)=1$  and  $\lim_{x\to-\infty} F(x)=0$ .

# Examples of possible random variable laws

- ▶ Other examples of distribution functions: uniform on [0,1], exponential with rate  $\lambda$ , standard normal, Cantor set measure.
- ▶ Can also define distribution functions for random variables that are a.s. integers (like Poisson or geometric or binomial random variables, say). How about for a ratio of two independent Poisson random variables? (This is a random rational with a dense support on  $[0, \infty)$ .)
- ► Higher dimensional density functions analogously defined.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 4 Integration

Scott Sheffield

MIT

Integration

Integration

## Recall definitions

- ▶ **Probability space** is triple  $(\Omega, \mathcal{F}, P)$  where  $\Omega$  is sample space,  $\mathcal{F}$  is set of events (the  $\sigma$ -algebra) and  $P: \mathcal{F} \to [0,1]$  is the probability function.
- $\rightharpoonup \sigma$ -algebra is collection of subsets closed under complementation and countable unions. Call  $(\Omega, \mathcal{F})$  a measure space.
- ▶ Measure is function  $\mu : \mathcal{F} \to \mathbb{R}$  satisfying  $\mu(A) \ge \mu(\emptyset) = 0$  for all  $A \in \mathcal{F}$  and countable additivity:  $\mu(\cup_i A_i) = \sum_i \mu(A_i)$  for disjoint  $A_i$ .
- ▶ Measure  $\mu$  is **probability measure** if  $\mu(\Omega) = 1$ .
- ▶ The **Borel**  $\sigma$ -algebra  $\mathcal{B}$  on a topological space is the smallest  $\sigma$ -algebra containing all open sets.

18.175 Lecture 4

## Recall definitions

- ▶ Real random variable is function  $X : \Omega \to \mathbb{R}$  such that the preimage of every Borel set is in  $\mathcal{F}$ .
- Note: to prove X is measurable, it is enough to show that the pre-image of every open set is in  $\mathcal{F}$ .
- ▶ Can talk about  $\sigma$ -algebra generated by random variable(s): smallest  $\sigma$ -algebra that makes a random variable (or a collection of random variables) measurable.


18.175 Lecture 4

## Lebesgue integration

- Lebesgue: If you can measure, you can integrate.
- In more words: if  $(\Omega, \mathcal{F})$  is a measure space with a measure  $\mu$  with  $\mu(\Omega) < \infty$ ) and  $f: \Omega \to \mathbb{R}$  is  $\mathcal{F}$ -measurable, then we can define  $\int f d\mu$  (for non-negative f, also if both  $f \lor 0$  and  $-f \land 0$  and have finite integrals...)
- Idea: define integral, verify linearity and positivity (a.e. non-negative functions have non-negative integrals) in 4 cases:
  - f takes only finitely many values.
  - f is bounded (hint: reduce to previous case by rounding down or up to nearest multiple of  $\epsilon$  for  $\epsilon \to 0$ ).
  - ▶ f is non-negative (hint: reduce to previous case by taking  $f \wedge N$  for  $N \to \infty$ ).
  - ▶ f is any measurable function (hint: treat positive/negative parts separately, difference makes sense if both integrals finite).

18.175 Lecture 4

## Lebesgue integration

- ▶ Can we extend previous discussion to case  $\mu(\Omega) = \infty$ ?
- ▶ **Theorem:** if *f* and *g* are integrable then:

```
If f \geq 0 a.s. then \int f d\mu \geq 0.
For a,b \in \mathbb{R}, have \int (af+bg)d\mu = a\int f d\mu + b\int g d\mu.
If g \leq f a.s. then \int g d\mu \leq \int f d\mu.
If g = f a.e. then \int g d\mu = \int f d\mu.
|\int f d\mu| < \int |f| d\mu.
```

▶ When  $(\Omega, \mathcal{F}, \mu) = (\mathbb{R}^d, \mathcal{R}^d, \lambda)$ , write  $\int_E f(x) dx = \int 1_E f d\lambda$ .


Integration

Integration

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 5 More integration and expectation

Scott Sheffield

MIT

Integration

Integration

## Recall Lebesgue integration

- ▶ Lebesgue: If you can measure, you can integrate.
- ▶ In more words: if  $(\Omega, \mathcal{F})$  is a measure space with a measure  $\mu$  with  $\mu(\Omega) < \infty$ ) and  $f: \Omega \to \mathbb{R}$  is  $\mathcal{F}$ -measurable, then we can define  $\int f d\mu$  (for non-negative f, also if both  $f \lor 0$  and  $-f \land 0$  and have finite integrals...)
- Idea: define integral, verify linearity and positivity (a.e. non-negative functions have non-negative integrals) in 4 cases:
  - f takes only finitely many values.
  - f is bounded (hint: reduce to previous case by rounding down or up to nearest multiple of  $\epsilon$  for  $\epsilon \to 0$ ).
  - ▶ f is non-negative (hint: reduce to previous case by taking  $f \wedge N$  for  $N \to \infty$ ).
  - ▶ f is any measurable function (hint: treat positive/negative parts separately, difference makes sense if both integrals finite).

18.175 Lecture 5

#### Lebesgue integration

- ▶ **Theorem:** if *f* and *g* are integrable then:
  - ▶ If  $f \ge 0$  a.s. then  $\int f d\mu \ge 0$ .
  - ▶ For  $a, b \in \mathbb{R}$ , have  $\int (af + bg)d\mu = a \int fd\mu + b \int gd\mu$ .
  - ▶ If  $g \le f$  a.s. then  $\int g d\mu \le \int f d\mu$ .
  - ▶ If g = f a.e. then  $\int g d\mu = \int f d\mu$ .
  - ▶  $|\int f d\mu| \le \int |f| d\mu$ .
- ▶ When  $(\Omega, \mathcal{F}, \mu) = (\mathbb{R}^d, \mathcal{R}^d, \lambda)$ , write  $\int_E f(x) dx = \int 1_E f d\lambda$ .

Integration

Integration

#### Expectation

- ▶ Given probability space  $(\Omega, \mathcal{F}, P)$  and random variable X, we write  $EX = \int XdP$ . Always defined if  $X \geq 0$ , or if integrals of  $\max\{X,0\}$  and  $\min\{X,0\}$  are separately finite.
- ►  $EX^k$  is called kth moment of X. Also, if m = EX then  $E(X m)^2$  is called the **variance** of X.


# Properties of expectation/integration

- ▶ **Jensen's inequality:** If  $\mu$  is probability measure and  $\phi : \mathbb{R} \to \mathbb{R}$  is convex then  $\phi(\int f d\mu) \leq \int \phi(f) d\mu$ . If X is random variable then  $E\phi(X) \geq \phi(EX)$ .
- ▶ Main idea of proof: Approximate  $\phi$  below by linear function L that agrees with  $\phi$  at EX.
- ▶ **Applications:** Utility, hedge fund payout functions.
- ▶ Hölder's inequality: Write  $||f||_p = (\int |f|^p d\mu)^{1/p}$  for  $1 \le p < \infty$ . If 1/p + 1/q = 1, then  $\int |fg| d\mu \le ||f||_p ||g||_q$ .
- ▶ Main idea of proof: Rescale so that  $||f||_p ||g||_q = 1$ . Use some basic calculus to check that for any positive x and y we have  $xy \le x^p/p + y^q/p$ . Write x = |f|, y = |g| and integrate to get  $\int |fg| d\mu \le \frac{1}{p} + \frac{1}{q} = 1 = ||f||_p ||g||_q$ .
- ▶ Cauchy-Schwarz inequality: Special case p = q = 2. Gives  $\int |fg|d\mu \le ||f||_2 ||g||_2$ . Says that dot product of two vectors is at most product of vector lengths.

18.175 Lecture 5

## Bounded convergence theorem

▶ **Bounded convergence theorem:** Consider *probability* measure  $\mu$  and suppose  $|f_n| \leq M$  a.s. for all n and some fixed M > 0, and that  $f_n \to f$  in probability (i.e.,  $\lim_{n \to \infty} \mu\{x : |f_n(x) - f(x)| > \epsilon\} = 0$  for all  $\epsilon > 0$ ). Then

$$\int f d\mu = \lim_{n \to \infty} \int f_n d\mu.$$

(Build counterexample for infinite measure space using wide and short rectangles?...)

▶ Main idea of proof: for any  $\epsilon$ ,  $\delta$  can take n large enough so  $\int |f_n - f| d\mu < M\delta + \epsilon.$ 

18.175 Lecture 5 10

#### Fatou's lemma

▶ **Fatou's lemma:** If  $f_n \ge 0$  then

$$\liminf_{n\to\infty} f_n d\mu \geq (\liminf_{n\to\infty} f_n) d\mu.$$

(Counterexample for opposite-direction inequality using thin and tall rectangles?)

▶ Main idea of proof: first reduce to case that the  $f_n$  are increasing by writing  $g_n(x) = \inf_{m \geq n} f_m(x)$  and observing that  $g_n(x) \uparrow g(x) = \liminf_{n \to \infty} f_n(x)$ . Then truncate, used bounded convergence, take limits.

18.175 Lecture 5

## More integral properties

▶ Monotone convergence: If  $f_n \ge 0$  and  $f_n \uparrow f$  then

$$\int f_n d\mu \uparrow \int f d\mu.$$

- ▶ Main idea of proof: one direction obvious, Fatou gives other.
- ▶ **Dominated convergence:** If  $f_n \to f$  a.e. and  $|f_n| \le g$  for all n and g is integrable, then  $\int f_n d\mu \to \int f d\mu$ .
- ▶ Main idea of proof: Fatou for functions  $g + f_n \ge 0$  gives one side. Fatou for  $g f_n \ge 0$  gives other.

18.175 Lecture 5 12

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### 18.175: Lecture 6

# Laws of large numbers and independence

Scott Sheffield

MIT

**Definitions** 

Background results

**Definitions** 

Background results

### Recall expectation definition

- ▶ Given probability space  $(\Omega, \mathcal{F}, P)$  and random variable X (i.e., measurable function X from  $\Omega$  to  $\mathbb{R}$ ), we write  $EX = \int XdP$ .
- ▶ Expectation is always defined if  $X \ge 0$  a.s., or if integrals of  $\max\{X,0\}$  and  $\min\{X,0\}$  are separately finite.

## Strong law of large numbers

- ▶ **Theorem (strong law):** If  $X_1, X_2, ...$  are i.i.d. real-valued random variables with expectation m and  $A_n := n^{-1} \sum_{i=1}^n X_i$  are the *empirical means* then  $\lim_{n\to\infty} A_n = m$  almost surely.
- ▶ What does i.i.d. mean?
- Answer: independent and identically distributed.
- Now do you even define an infinite sequence of independent random variables? Is that even possible? It's kind of an empty theorem if it turns out that the hypotheses are never satisfied. And by the way, what measure space and  $\sigma$ -algebra are we using? And is the event that the limit exists even measurable in this  $\sigma$ -algebra? Because if it's not, what does it mean to say it has probability one? Also, why do they call it the strong law? Is there also a weak law?

### Independence of two events/random variables/ $\sigma$ -algebras

- ▶ **Probability space** is triple  $(\Omega, \mathcal{F}, P)$  where  $\Omega$  is sample space,  $\mathcal{F}$  is set of events (the  $\sigma$ -algebra) and  $P: \mathcal{F} \to [0,1]$  is the probability function.
- ► Two events A and B are independent if  $P(A \cap B) = P(A)P(B)$ .
- ▶ Random variables X and Y are independent if for all  $C, D \in \mathcal{R}$ , we have  $P(X \in C, Y \in D) = P(X \in C)P(Y \in D)$ , i.e., the events  $\{X \in C\}$  and  $\{Y \in D\}$  are independent.
- ▶ Two  $\sigma$ -fields  $\mathcal F$  and  $\mathcal G$  are independent if A and B are independent whenever  $A \in \mathcal F$  and  $B \in \mathcal G$ . (This definition also makes sense if  $\mathcal F$  and  $\mathcal G$  are arbitrary algebras, semi-algebras, or other collections of measurable sets.)

# Independence of multiple events/random variables/ $\sigma$ -algebras

- ▶ Say events  $A_1, A_2, ..., A_n$  are independent if for each  $I \subset \{1, 2, ..., n\}$  we have  $P(\cap_{i \in I} A_i) = \prod_{i \in I} P(A_i)$ .
- Question: does pairwise independence imply independence?
- Say random variables  $X_1, X_2, \ldots, X_n$  are independent if for any measurable sets  $B_1, B_2, \ldots, B_n$ , the events that  $X_i \in B_i$  are independent.
- ▶ Say  $\sigma$ -algebras  $\mathcal{F}_1, \mathcal{F}_2, \ldots, \mathcal{F}_n$  if any collection of events (one from each  $\sigma$ -algebra) are independent. (This definition also makes sense if the  $\mathcal{F}_i$  are algebras, semi-algebras, or other collections of measurable sets.)

**Definitions** 

Background results

Definitions

 ${\sf Background}\ {\sf results}$ 

### Extending to $\sigma$ -algebras

- ▶ **Theorem:** If  $A_1, A_2, ..., A_n$  are independent, and each  $A_i$  is a  $\pi$ -system, then  $\sigma(A_1), ..., \sigma(A_n)$  are independent.
- ▶ Main idea of proof: Apply the  $\pi$ - $\lambda$  theorem.

# Kolmogorov's Extension Theorem

- ▶ Task: make sense of this statement. Let  $\Omega$  be the set of all countable sequences  $\omega = (\omega_1, \omega_2, \omega_3 \ldots)$  of real numbers. Let  $\mathcal F$  be the smallest  $\sigma$ -algebra that makes the maps  $\omega \to \omega_i$  measurable. Let P be the probability measure that makes the  $\omega_i$  independent identically distributed normals with mean zero, variance one.
- We could also ask about i.i.d. sequences of coin tosses or i.i.d. samples from some other space.
- ▶ The  $\mathcal{F}$  described above is the natural product  $\sigma$ -algebra: smallest  $\sigma$ -algebra generated by the "finite dimensional rectangles" of form  $\{\omega: \omega_i \in (a_i,b_i], 1 \leq i \leq n\}$ .
- ▶ Question: what things are in this  $\sigma$ -algebra? How about the event that the  $\omega_i$  converge to a limit?

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 7 Sums of random variables

Scott Sheffield

MIT

**Definitions** 

Sums of random variables

**Definitions** 

Sums of random variables

## Recall expectation definition

- ▶ Given probability space  $(\Omega, \mathcal{F}, P)$  and random variable X (i.e., measurable function X from  $\Omega$  to  $\mathbb{R}$ ), we write  $EX = \int XdP$ .
- ▶ Expectation is always defined if  $X \ge 0$  a.s., or if integrals of  $\max\{X,0\}$  and  $\min\{X,0\}$  are separately finite.

# Strong law of large numbers

- ▶ **Theorem (strong law):** If  $X_1, X_2, ...$  are i.i.d. real-valued random variables with expectation m and  $A_n := n^{-1} \sum_{i=1}^n X_i$  are the *empirical means* then  $\lim_{n\to\infty} A_n = m$  almost surely.
- Last time we defined independent. We showed how to use Kolmogorov to construct infinite i.i.d. random variables on a measure space with a natural σ-algebra (in which the existence of a limit of the X<sub>i</sub> is a measurable event). So we've come far enough to say that the statement makes sense.

#### Recall some definitions

- ► Two events A and B are independent if  $P(A \cap B) = P(A)P(B)$ .
- ▶ Random variables X and Y are independent if for all  $C, D \in \mathcal{R}$ , we have  $P(X \in C, Y \in D) = P(X \in C)P(Y \in D)$ , i.e., the events  $\{X \in C\}$  and  $\{Y \in D\}$  are independent.
- ▶ Two  $\sigma$ -fields  $\mathcal F$  and  $\mathcal G$  are independent if A and B are independent whenever  $A \in \mathcal F$  and  $B \in \mathcal G$ . (This definition also makes sense if  $\mathcal F$  and  $\mathcal G$  are arbitrary algebras, semi-algebras, or other collections of measurable sets.)

#### Recall some definitions

- Say events  $A_1, A_2, \ldots, A_n$  are independent if for each  $I \subset \{1, 2, \ldots, n\}$  we have  $P(\cap_{i \in I} A_i) = \prod_{i \in I} P(A_i)$ .
- ▶ Say random variables  $X_1, X_2, ..., X_n$  are independent if for any measurable sets  $B_1, B_2, ..., B_n$ , the events that  $X_i \in B_i$  are independent.
- Say  $\sigma$ -algebras  $\mathcal{F}_1, \mathcal{F}_2, \ldots, \mathcal{F}_n$  if any collection of events (one from each  $\sigma$ -algebra) are independent. (This definition also makes sense if the  $\mathcal{F}_i$  are algebras, semi-algebras, or other collections of measurable sets.)

## Recall Kolmogorov

- ▶ Kolmogorov extension theorem: If we have consistent probability measures on  $(\mathbb{R}^n, \mathcal{R}^n)$ , then we can extend them uniquely to a probability measure on  $\mathcal{R}^{\mathbb{N}}$ .
- Proved using semi-algebra variant of Carathéeodory's extension theorem.

## Extend Kolmogorov

- ▶ Kolmogorov extension theorem not generally true if replace  $(\mathbb{R}, \mathcal{R})$  with any measure space.
- ▶ But okay if we use **standard Borel spaces**. Durrett calls such spaces nice: a set (S, S) is **nice** if have 1-1 map from S to  $\mathbb{R}$  so that  $\phi$  and  $\phi^{-1}$  are both measurable.
- Are there any interesting nice measure spaces?
- ▶ **Theorem:** Yes, lots. In fact, if S is a complete separable metric space M (or a Borel subset of such a space) and S is the set of Borel subsets of S, then (S, S) is nice.
- **separable** means containing a countable dense set.

## Standard Borel spaces

- ▶ Main idea of proof: Reduce to case that diameter less than one (e.g., by replacing d(x,y) with d(x,y)/(1+d(x,y))). Then map M continuously into  $[0,1]^{\mathbb{N}}$  by considering countable dense set  $q_1,q_2,\ldots$  and mapping x to  $(d(q_1,x),d(q_2,x),\ldots)$ . Then give measurable one-to-one map from  $[0,1]^{\mathbb{N}}$  to [0,1] via binary expansion (to send  $\mathbb{N} \times \mathbb{N}$ -indexed matrix of 0's and 1's to an  $\mathbb{N}$ -indexed sequence of 0's and 1's).
- In practice: say I want to let  $\Omega$  be set of closed subsets of a disc, or planar curves, or functions from one set to another, etc. If I want to construct natural  $\sigma$ -algebra  $\mathcal{F}$ , I just need to produce metric that makes  $\Omega$  complete and separable (and if I have to enlarge  $\Omega$  to make it complete, that might be okay). Then I check that the events I care about belong to this  $\sigma$ -algebra.

#### Fubini's theorem

- ▶ Consider  $\sigma$ -finite measure spaces  $(X, \mathcal{A}, \mu_1)$  and  $(Y, \mathcal{B}, \mu_2)$ .
- ▶ Let  $\Omega = X \times Y$  and  $\mathcal{F}$  be product  $\sigma$ -algebra.
- ▶ Check: unique measure  $\mu$  on  $\mathcal{F}$  with  $\mu(A \times B) = \mu_1(A)\mu_2(B)$ .
- ▶ **Fubini's theorem:** If  $f \ge 0$  or  $\int |f| d\mu < \infty$  then

$$\int_{X} \int_{Y} f(x,y)\mu_{2}(dy)\mu_{1}(dx) = \int_{X\times Y} fd\mu =$$

$$\int_{Y} \int_{X} f(x,y)\mu_{1}(dx)\mu_{2}(dy).$$

Main idea of proof: Check definition makes sense: if f measurable, show that restriction of f to slice  $\{(x,y): x=x_0\}$  is measurable as function of y, and the integral over slice is measurable as function of  $x_0$ . Check Fubini for indicators of rectangular sets, use  $\pi-\lambda$  to extend to measurable indicators. Extend to simple, bounded,  $L^1$  (or non-negative) functions.


# Non-measurable Fubini counterexample

▶ What if we take total ordering  $\prec$  or reals in [0,1] (such that for each y the set  $\{x: x \prec y\}$  is countable) and consider indicator function of  $\{(x,y): x \prec y\}$ ?

#### More observations

- ▶ If  $X_i$  are independent with distributions  $\mu_i$ , then  $(X_1, \ldots, X_n)$  has distribution  $\mu_1 \times \ldots \mu_n$ .
- ▶ If  $X_i$  are independent and satisfy either  $X_i \ge 0$  for all i or  $E|X_i| < \infty$  for all i then

$$E\prod_{i=1}^n X_i = \prod_{i=1}^n X_i.$$

**Definitions** 

Sums of random variables


Definitions

Sums of random variables

# Summing two random variables

- ▶ Say we have independent random variables X and Y with density functions  $f_X$  and  $f_Y$ .
- ▶ Now let's try to find  $F_{X+Y}(a) = P\{X + Y \le a\}$ .
- ► This is the integral over  $\{(x,y): x+y \le a\}$  of  $f(x,y)=f_X(x)f_Y(y)$ . Thus,

$$P\{X + Y \le a\} = \int_{-\infty}^{\infty} \int_{-\infty}^{a-y} f_X(x) f_Y(y) dx dy$$
$$= \int_{-\infty}^{\infty} F_X(a-y) f_Y(y) dy.$$

- ▶ Differentiating both sides gives  $f_{X+Y}(a) = \frac{d}{da} \int_{-\infty}^{\infty} F_X(a-y) f_Y(y) dy = \sum_{-\infty}^{\infty} f_X(a-y) f_Y(y) dy.$
- Latter formula makes some intuitive sense. We're integrating over the set of x, y pairs that add up to a.
- ▶ Can also write  $P(X + Y \le z) = \int F(z y) dG(y)$ .

# Summing i.i.d. uniform random variables

- ▶ Suppose that X and Y are i.i.d. and uniform on [0,1]. So  $f_X = f_Y = 1$  on [0,1].
- ▶ What is the probability density function of X + Y?
- ►  $f_{X+Y}(a) = \int_{-\infty}^{\infty} f_X(a-y) f_Y(y) dy = \int_0^1 f_X(a-y)$  which is the length of  $[0,1] \cap [a-1,a]$ .
- ▶ That's a when  $a \in [0,1]$  and 2-a when  $a \in [0,2]$  and 0 otherwise.

# Summing two normal variables

- ▶ X is normal with mean zero, variance  $\sigma_1^2$ , Y is normal with mean zero, variance  $\sigma_2^2$ .
- $f_X(x) = \frac{1}{\sqrt{2\pi}\sigma_1} e^{\frac{-x^2}{2\sigma_1^2}}$  and  $f_Y(y) = \frac{1}{\sqrt{2\pi}\sigma_2} e^{\frac{-y^2}{2\sigma_2^2}}$ .
- ▶ We just need to compute  $f_{X+Y}(a) = \int_{-\infty}^{\infty} f_X(a-y) f_Y(y) dy$ .
- ▶ We could compute this directly.
- ▶ Or we could argue with a multi-dimensional bell curve picture that if X and Y have variance 1 then  $f_{\sigma_1X+\sigma_2Y}$  is the density of a normal random variable (and note that variances and expectations are additive).
- ▶ Or use fact that if  $A_i \in \{-1,1\}$  are i.i.d. coin tosses then  $\frac{1}{\sqrt{N}} \sum_{i=1}^{\sigma^2 N} A_i$  is approximately normal with variance  $\sigma^2$  when N is large.
- ▶ Generally: if independent random variables  $X_j$  are normal  $(\mu_j, \sigma_i^2)$  then  $\sum_{j=1}^n X_j$  is normal  $(\sum_{j=1}^n \mu_j, \sum_{j=1}^n \sigma_i^2)$ .

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.175: Lecture 8

# Weak laws and moment-generating/characteristic functions

Scott Sheffield

MIT

Moment generating functions

Weak law of large numbers: Markov/Chebyshev approach

Weak law of large numbers: characteristic function approach


#### Moment generating functions

Weak law of large numbers:  $\mathsf{Markov}/\mathsf{Chebyshev}$  approach

Weak law of large numbers: characteristic function approach

# Moment generating functions

- ▶ Let X be a random variable.
- ▶ The **moment generating function** of X is defined by  $M(t) = M_X(t) := E[e^{tX}].$
- ▶ When X is discrete, can write  $M(t) = \sum_{x} e^{tx} p_X(x)$ . So M(t) is a weighted average of countably many exponential functions.
- ▶ When X is continuous, can write  $M(t) = \int_{-\infty}^{\infty} e^{tx} f(x) dx$ . So M(t) is a weighted average of a continuum of exponential functions.
- We always have M(0) = 1.
- ▶ If b > 0 and t > 0 then  $E[e^{tX}] \ge E[e^{t\min\{X,b\}}] \ge P\{X \ge b\}e^{tb}.$
- ▶ If X takes both positive and negative values with positive probability then M(t) grows at least exponentially fast in |t| as  $|t| \to \infty$ .


# Moment generating functions actually generate moments

- ▶ Let X be a random variable and  $M(t) = E[e^{tX}]$ .
- ▶ Then  $M'(t) = \frac{d}{dt}E[e^{tX}] = E[\frac{d}{dt}(e^{tX})] = E[Xe^{tX}].$
- ▶ in particular, M'(0) = E[X].
- Also  $M''(t) = \frac{d}{dt}M'(t) = \frac{d}{dt}E[Xe^{tX}] = E[X^2e^{tX}].$
- ▶ So  $M''(0) = E[X^2]$ . Same argument gives that nth derivative of M at zero is  $E[X^n]$ .
- ▶ Interesting: knowing all of the derivatives of M at a single point tells you the moments  $E[X^k]$  for all integer  $k \ge 0$ .
- Another way to think of this: write  $e^{tX} = 1 + tX + \frac{t^2X^2}{2!} + \frac{t^3X^3}{3!} + \dots$
- ▶ Taking expectations gives  $E[e^{tX}] = 1 + tm_1 + \frac{t^2m_2}{2!} + \frac{t^3m_3}{3!} + \dots$ , where  $m_k$  is the kth moment. The kth derivative at zero is  $m_k$ .


# Moment generating functions for independent sums

- Let X and Y be independent random variables and Z = X + Y.
- Write the moment generating functions as  $M_X(t) = E[e^{tX}]$  and  $M_Y(t) = E[e^{tY}]$  and  $M_Z(t) = E[e^{tZ}]$ .
- ▶ If you knew  $M_X$  and  $M_Y$ , could you compute  $M_Z$ ?
- ▶ By independence,  $M_Z(t) = E[e^{t(X+Y)}] = E[e^{tX}e^{tY}] = E[e^{tX}]E[e^{tY}] = M_X(t)M_Y(t)$  for all t.
- In other words, adding independent random variables corresponds to multiplying moment generating functions.

# Moment generating functions for sums of i.i.d. random variables

- ▶ We showed that if Z = X + Y and X and Y are independent, then  $M_Z(t) = M_X(t)M_Y(t)$
- ▶ If  $X_1 ... X_n$  are i.i.d. copies of X and  $Z = X_1 + ... + X_n$  then what is  $M_Z$ ?
- ▶ Answer:  $M_X^n$ . Follows by repeatedly applying formula above.
- This a big reason for studying moment generating functions. It helps us understand what happens when we sum up a lot of independent copies of the same random variable.

#### Other observations

- ▶ If Z = aX then can I use  $M_X$  to determine  $M_Z$ ?
- ▶ Answer: Yes.  $M_Z(t) = E[e^{tZ}] = E[e^{taX}] = M_X(at)$ .
- ▶ If Z = X + b then can I use  $M_X$  to determine  $M_Z$ ?
- Answer: Yes.  $M_Z(t) = E[e^{tZ}] = E[e^{tX+bt}] = e^{bt}M_X(t)$ .
- Latter answer is the special case of  $M_Z(t) = M_X(t)M_Y(t)$  where Y is the constant random variable b.


#### Existence issues

- ▶ Seems that unless  $f_X(x)$  decays superexponentially as x tends to infinity, we won't have  $M_X(t)$  defined for all t.
- ▶ What is  $M_X$  if X is standard Cauchy, so that  $f_X(x) = \frac{1}{\pi(1+x^2)}$ .
- ▶ Answer:  $M_X(0) = 1$  (as is true for any X) but otherwise  $M_X(t)$  is infinite for all  $t \neq 0$ .
- ▶ Informal statement: moment generating functions are not defined for distributions with fat tails.

Moment generating functions

Weak law of large numbers: Markov/Chebyshev approach

Weak law of large numbers: characteristic function approach

Moment generating functions

Weak law of large numbers: Markov/Chebyshev approach

Weak law of large numbers: characteristic function approach

# Markov's and Chebyshev's inequalities

- ▶ Markov's inequality: Let X be non-negative random variable. Fix a > 0. Then  $P\{X \ge a\} \le \frac{E[X]}{a}$ .
- ▶ **Proof:** Consider a random variable Y defined by  $Y = \begin{cases} a & X \geq a \\ 0 & X < a \end{cases}$ . Since  $X \geq Y$  with probability one, it follows that  $E[X] \geq E[Y] = aP\{X \geq a\}$ . Divide both sides by a to get Markov's inequality.
- ► Chebyshev's inequality: If X has finite mean  $\mu$ , variance  $\sigma^2$ , and k > 0 then

$$P\{|X - \mu| \ge k\} \le \frac{\sigma^2}{k^2}.$$

▶ **Proof:** Note that  $(X - \mu)^2$  is a non-negative random variable and  $P\{|X - \mu| \ge k\} = P\{(X - \mu)^2 \ge k^2\}$ . Now apply Markov's inequality with  $a = k^2$ .

# Markov and Chebyshev: rough idea

- ▶ Markov's inequality: Let X be non-negative random variable with finite mean. Fix a constant a > 0. Then  $P\{X \ge a\} \le \frac{E[X]}{a}$ .
- ► Chebyshev's inequality: If X has finite mean  $\mu$ , variance  $\sigma^2$ , and k > 0 then

$$P\{|X-\mu| \ge k\} \le \frac{\sigma^2}{k^2}.$$

- ▶ Inequalities allow us to deduce limited information about a distribution when we know only the mean (Markov) or the mean and variance (Chebyshev).
- ▶ **Markov:** if E[X] is small, then it is not too likely that X is large.
- ▶ **Chebyshev:** if  $\sigma^2 = \text{Var}[X]$  is small, then it is not too likely that X is far from its mean.

# Statement of weak law of large numbers

- ▶ Suppose  $X_i$  are i.i.d. random variables with mean  $\mu$ .
- ► Then the value  $A_n := \frac{X_1 + X_2 + ... + X_n}{n}$  is called the *empirical average* of the first n trials.
- ▶ We'd guess that when n is large,  $A_n$  is typically close to  $\mu$ .
- ▶ Indeed, weak law of large numbers states that for all  $\epsilon > 0$  we have  $\lim_{n\to\infty} P\{|A_n \mu| > \epsilon\} = 0$ .
- ► Example: as *n* tends to infinity, the probability of seeing more than .50001*n* heads in *n* fair coin tosses tends to zero.

# Proof of weak law of large numbers in finite variance case

- As above, let  $X_i$  be i.i.d. random variables with mean  $\mu$  and write  $A_n := \frac{X_1 + X_2 + ... + X_n}{n}$ .
- ▶ By additivity of expectation,  $\mathbb{E}[A_n] = \mu$ .
- ► Similarly,  $Var[A_n] = \frac{n\sigma^2}{n^2} = \sigma^2/n$ .
- ▶ By Chebyshev  $P\{|A_n \mu| \ge \epsilon\} \le \frac{\operatorname{Var}[A_n]}{\epsilon^2} = \frac{\sigma^2}{n\epsilon^2}$ .
- No matter how small  $\epsilon$  is, RHS will tend to zero as n gets large.

 $L^2$  weak law of large numbers

- ▶ Say  $X_i$  and  $X_i$  are uncorrelated if  $E(X_iX_i) = EX_iEX_i$ .
- ► Chebyshev/Markov argument works whenever variables are uncorrelated (does not actually require independence).

# What else can you do with just variance bounds?

- ▶ Having "almost uncorrelated"  $X_i$  is sometimes enough: just need variance of  $A_n$  to go to zero.
- ▶ Toss  $\alpha n$  bins into n balls. How many bins are filled?
- ▶ When n is large, the number of balls in the first bin is approximately a Poisson random variable with expectation  $\alpha$ .
- ▶ Probability first bin contains no ball is  $(1 1/n)^{\alpha n} \approx e^{-\alpha}$ .
- ▶ We can explicitly compute variance of the number of bins with no balls. Allows us to show that fraction of bins with no balls concentrates about its expectation, which is  $e^{-\alpha}$ .

## How do you extend to random variables without variance?

- Assume X<sub>n</sub> are i.i.d. non-negative instances of random variable X with finite mean. Can one prove law of large numbers for these?
- ▶ Try truncating. Fix large N and write  $A = X1_{X>N}$  and  $B = X1_{X\leq N}$  so that X = A + B. Choose N so that EB is very small. Law of large numbers holds for A.

Moment generating functions

Weak law of large numbers: Markov/Chebyshev approach

Weak law of large numbers: characteristic function approach

Moment generating functions

Weak law of large numbers:  $\mathsf{Markov}/\mathsf{Chebyshev}$  approach

Weak law of large numbers: characteristic function approach

#### Extent of weak law

- ▶ Question: does the weak law of large numbers apply no matter what the probability distribution for *X* is?
- ▶ Is it always the case that if we define  $A_n := \frac{X_1 + X_2 + ... + X_n}{n}$  then  $A_n$  is typically close to some fixed value when n is large?
- What if X is Cauchy?
- ▶ In this strange and delightful case  $A_n$  actually has the same probability distribution as X.
- ▶ In particular, the  $A_n$  are not tightly concentrated around any particular value even when n is very large.
- ▶ But weak law holds as long as E[|X|] is finite, so that  $\mu$  is well defined.
- ▶ One standard proof uses characteristic functions.

#### Characteristic functions

- Let X be a random variable.
- ▶ The **characteristic function** of X is defined by  $\phi(t) = \phi_X(t) := E[e^{itX}]$ . Like M(t) except with i thrown in.
- ▶ Recall that by definition  $e^{it} = \cos(t) + i\sin(t)$ .
- Characteristic functions are similar to moment generating functions in some ways.
- ▶ For example,  $\phi_{X+Y} = \phi_X \phi_Y$ , just as  $M_{X+Y} = M_X M_Y$ , if X and Y are independent.
- ▶ And  $\phi_{aX}(t) = \phi_X(at)$  just as  $M_{aX}(t) = M_X(at)$ .
- ▶ And if X has an mth moment then  $E[X^m] = i^m \phi_X^{(m)}(0)$ .
- ▶ But characteristic functions have an advantage: they are well defined at all *t* for all random variables *X*.

## Continuity theorems

18.175 Lecture 8

- Let X be random variable,  $X_n$  a sequence of random variables.
- Say  $X_n$  converge in distribution or converge in law to X if  $\lim_{n\to\infty} F_{X_n}(x) = F_X(x)$  at all  $x\in\mathbb{R}$  at which  $F_X$  is continuous.
- ▶ The weak law of large numbers can be rephrased as the statement that  $A_n$  converges in law to  $\mu$  (i.e., to the random variable that is equal to  $\mu$  with probability one).
- Lévy's continuity theorem (coming later): if

$$\lim_{n\to\infty}\phi_{X_n}(t)=\phi_X(t)$$

for all t, then  $X_n$  converge in law to X.

- By this theorem, we can prove weak law of large numbers by showing  $\lim_{n\to\infty}\phi_{A_n}(t)=\phi_\mu(t)=e^{it\mu}$  for all t. When  $\mu=0$ , amounts to showing  $\lim_{n\to\infty}\phi_{A_n}(t)=1$  for all t.
- **Moment generating analog:** if moment generating functions  $M_{X_n}(t)$  are defined for all t and n and, for all t,  $\lim_{n\to\infty} M_{X_n}(t) = M_X(t)$ , then  $X_n$  converge in law to X.

# Proof sketch for weak law of large numbers, finite mean case

- As above, let  $X_i$  be i.i.d. instances of random variable X with mean zero. Write  $A_n := \frac{X_1 + X_2 + ... + X_n}{n}$ . Weak law of large numbers holds for i.i.d. instances of X if and only if it holds for i.i.d. instances of  $X \mu$ . Thus it suffices to prove the weak law in the mean zero case.
- ▶ Consider the characteristic function  $\phi_X(t) = E[e^{itX}]$ .
- ▶ Since E[X] = 0, we have  $\phi'_X(0) = E[\frac{\partial}{\partial t}e^{itX}]_{t=0} = iE[X] = 0$ .
- ▶ Write  $g(t) = \log \phi_X(t)$  so  $\phi_X(t) = e^{g(t)}$ . Then g(0) = 0 and (by chain rule)  $g'(0) = \lim_{\epsilon \to 0} \frac{g(\epsilon) g(0)}{\epsilon} = \lim_{\epsilon \to 0} \frac{g(\epsilon)}{\epsilon} = 0$ .
- Now  $\phi_{A_n}(t) = \phi_X(t/n)^n = e^{ng(t/n)}$ . Since g(0) = g'(0) = 0 we have  $\lim_{n\to\infty} ng(t/n) = \lim_{n\to\infty} t\frac{g(\frac{t}{n})}{\frac{t}{n}} = 0$  if t is fixed. Thus  $\lim_{n\to\infty} e^{ng(t/n)} = 1$  for all t.
- By Lévy's continuity theorem, the  $A_n$  converge in law to 0 (i.e., to the random variable that is 0 with probability one).

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 9 Borel-Cantelli and strong law

Scott Sheffield

MIT

Laws of large numbers: Borel-Cantelli applications

Strong law of large numbers

Laws of large numbers: Borel-Cantelli applications


Strong law of large numbers

#### Borel-Cantelli lemmas

- ▶ First Borel-Cantelli lemma: If  $\sum_{n=1}^{\infty} P(A_n) < \infty$  then  $P(A_n \text{ i.o.}) = 0.$
- **Second Borel-Cantelli lemma:** If  $A_n$  are independent, then  $\sum_{n=1}^{\infty} P(A_n) = \infty \text{ implies } P(A_n \text{ i.o.}) = 1.$

### Convergence in probability subsequential a.s. convergence

- ▶ **Theorem:**  $X_n \to X$  in probability if and only if for every subsequence of the  $X_n$  there is a further subsequence converging a.s. to X.
- ▶ Main idea of proof: Consider event  $E_n$  that  $X_n$  and X differ by  $\epsilon$ . Do the  $E_n$  occur i.o.? Use Borel-Cantelli.


# Pairwise independence example

- ▶ **Theorem:** Suppose  $A_1, A_2, ...$  are pairwise independent and  $\sum P(A_n) = \infty$ , and write  $S_n = \sum_{i=1}^n 1_{A_i}$ . Then the ratio  $S_n/ES_n$  tends a.s. to 1.
- ▶ Main idea of proof: First, pairwise independence implies that variances add. Conclude (by checking term by term) that  $VarS_n \leq ES_n$ . Then Chebyshev implies

$$P(|S_n - ES_n| > \delta ES_n) \le Var(S_n)/(\delta ES_n)^2 \to 0,$$

which gives us convergence in probability.

▶ Second, take a smart subsequence. Let  $n_k = \inf\{n : ES_n \ge k^2\}$ . Use Borel Cantelli to get a.s. convergence along this subsequence. Check that convergence along this subsequence deterministically implies the non-subsequential convergence.

Laws of large numbers: Borel-Cantelli applications

Strong law of large numbers


Laws of large numbers: Borel-Cantelli applications

Strong law of large numbers

# General strong law of large numbers

▶ **Theorem (strong law):** If  $X_1, X_2, ...$  are i.i.d. real-valued random variables with expectation m and  $A_n := n^{-1} \sum_{i=1}^n X_i$  are the *empirical means* then  $\lim_{n\to\infty} A_n = m$  almost surely.


# Proof of strong law assuming $E[X^4] < \infty$

- ▶ Assume  $K := E[X^4] < \infty$ . Not necessary, but simplifies proof.
- ▶ Note:  $Var[X^2] = E[X^4] E[X^2]^2 \ge 0$ , so  $E[X^2]^2 \le K$ .
- ▶ The strong law holds for i.i.d. copies of X if and only if it holds for i.i.d. copies of  $X \mu$  where  $\mu$  is a constant.
- ▶ So we may as well assume E[X] = 0.
- ▶ Key to proof is to bound fourth moments of  $A_n$ .
- $E[A_n^4] = n^{-4} E[S_n^4] = n^{-4} E[(X_1 + X_2 + \ldots + X_n)^4].$
- ▶ Expand  $(X_1 + ... + X_n)^4$ . Five kinds of terms:  $X_i X_j X_k X_l$  and  $X_i X_j X_k^2$  and  $X_i X_j^3$  and  $X_i^2 X_j^2$  and  $X_i^4$ .
- ▶ The first three terms all have expectation zero. There are  $\binom{n}{2}$  of the fourth type and n of the last type, each equal to at most K. So  $E[A_n^4] \leq n^{-4} \Big( 6\binom{n}{2} + n \Big) K$ .
- ▶ Thus  $E[\sum_{n=1}^{\infty} A_n^4] = \sum_{n=1}^{\infty} E[A_n^4] < \infty$ . So  $\sum_{n=1}^{\infty} A_n^4 < \infty$  (and hence  $A_n \to 0$ ) with probability 1.

## General proof of strong law

- Suppose  $X_k$  are i.i.d. with finite mean. Let  $Y_k = X_k 1_{|X_k| \le k}$ . Write  $T_n = Y_1 + \ldots + Y_n$ . Claim:  $X_k = Y_k$  all but finitely often a.s. so suffices to show  $T_n/n \to \mu$ . (Borel Cantelli, expectation of positive r.v. is area between cdf and line y = 1)
- ▶ Claim:  $\sum_{k=1}^{\infty} \text{Var}(Y_k)/k^2 \le 4E|X_1| < \infty$ . How to prove it?
- ▶ **Observe:**  $Var(Y_k) \le E(Y_k^2) = \int_0^\infty 2y P(|Y_k| > y) dy \le \int_0^k 2y P(|X_1| > y) dy$ . Use Fubini (interchange sum/integral, since everything positive)

$$\sum_{k=1}^{\infty} E(Y_k^2)/k^2 \le \sum_{k=1}^{\infty} k^{-2} \int_0^{\infty} 1_{(y< k)} 2y P(|X_1| > y) dy =$$
$$\int_0^{\infty} \left(\sum_{k=1}^{\infty} k^{-2} 1_{(y< k)}\right) 2y P(|X_1| > y) dy.$$

Since  $E|X_1| = \int_0^\infty P(|X_1| > y) dy$ , complete proof of claim by showing that if  $y \ge 0$  then  $2y \sum_{k>y} k^{-2} \le 4$ .

# General proof of strong law

- ▶ Claim:  $\sum_{k=1}^{\infty} \text{Var}(Y_k)/k^2 \le 4E|X_1| < \infty$ . How to use it?
- ► Consider subsequence  $k(n) = [\alpha^n]$  for arbitrary  $\alpha > 1$ . Using Chebyshev, if  $\epsilon > 0$  then

$$\sum_{n=1}^{\infty} P |T_{k(n)} - ET_{k(n)}| > \epsilon k(n)) \le \epsilon^{-1} \sum_{n=1}^{\infty} \operatorname{Var}(T_{k(n)}) / k(n)^{2}$$

$$= \epsilon^{-2} \sum_{n=1}^{\infty} k(n)^{-2} \sum_{m=1}^{\kappa(n)} \text{Var}(Y_m) = \epsilon^{-2} \sum_{m=1}^{\infty} \text{Var}(Y_m) \sum_{n: k(n) > m} k(n)^{-2}.$$

Sum series:

$$\sum_{n:\alpha^n > m} [\alpha^n]^{-2} \le 4 \sum_{n:\alpha^n > m} \alpha^{-2n} \le 4(1 - \alpha^{-2})^{-1} m^{-2}.$$

► Combine computations (observe RHS below is finite):

$$\sum_{k=0}^{\infty} P(|T_{k(n)} - ET_k(n)| > \epsilon k(n)) \le 4(1 - \alpha^{-2})^{-1} \epsilon^{-2} \sum_{k=0}^{\infty} E(Y_m^2) m^{-2}.$$

▶ Since  $\epsilon$  is arbitrary, get  $(T_{k(n)} - ET_{k(n)})/k(n) \rightarrow 0$  a.s.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### 18.175: Lecture 10

# Zero-one laws and maximal inequalities

Scott Sheffield

MIT

Recollections

Kolmogorov zero-one law and three-series theorem

Recollections

Kolmogorov zero-one law and three-series theorem


#### Recall Borel-Cantelli lemmas

- ▶ First Borel-Cantelli lemma: If  $\sum_{n=1}^{\infty} P(A_n) < \infty$  then  $P(A_n \text{ i.o.}) = 0$ .
- ▶ Second Borel-Cantelli lemma: If  $A_n$  are independent, then  $\sum_{n=1}^{\infty} P(A_n) = \infty$  implies  $P(A_n \text{ i.o.}) = 1$ .


## Recall strong law of large numbers

▶ **Theorem (strong law):** If  $X_1, X_2, ...$  are i.i.d. real-valued random variables with expectation m and  $A_n := n^{-1} \sum_{i=1}^n X_i$  are the *empirical means* then  $\lim_{n\to\infty} A_n = m$  almost surely.

Recollections

Kolmogorov zero-one law and three-series theorem


Recollections

Kolmogorov zero-one law and three-series theorem

# Kolmogorov zero-one law

- ► Consider sequence of random variables  $X_n$  on some probability space. Write  $\mathcal{F}'_n = \sigma(X_n, X_{n_1}, \ldots)$  and  $\mathcal{T} = \cap_n \mathcal{F}'_n$ .
- $\rightharpoonup \mathcal{T}$  is called the **tail**  $\sigma$ -**algebra**. It contains the information you can observe by looking only at stuff arbitrarily far into the future. Intuitively, membership in tail event doesn't change when finitely many  $X_n$  are changed.
- ▶ Event that  $X_n$  converge to a limit is example of a tail event. Other examples?
- ▶ **Theorem:** If  $X_1, X_2, ...$  are independent and  $A \in \mathcal{T}$  then  $P(A) \in \{0, 1\}$ .

## Kolmogorov zero-one law proof idea

- ▶ **Theorem:** If  $X_1, X_2, ...$  are independent and  $A \in \mathcal{T}$  then  $P(A) \in \{0, 1\}$ .
- ▶ Main idea of proof: Statement is equivalent to saying that A is independent of itself, i.e.,  $P(A) = P(A \cap A) = P(A)^2$ . How do we prove that?
- ▶ Recall theorem that if  $A_i$  are independent  $\pi$ -systems, then  $\sigma A_i$  are independent.
- ▶ Deduce that  $\sigma(X_1, X_2, \ldots, X_n)$  and  $\sigma(X_{n+1}, X_{n+1}, \ldots)$  are independent. Then deduce that  $\sigma(X_1, X_2, \ldots)$  and  $\mathcal{T}$  are independent, using fact that  $\cup_k \sigma(X_1, \ldots, X_k)$  and  $\mathcal{T}$  are  $\pi$ -systems.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 11 Independent sums and large deviations

Scott Sheffield

MIT

Recollections

Recollections

#### Recall Borel-Cantelli lemmas

- ▶ First Borel-Cantelli lemma: If  $\sum_{n=1}^{\infty} P(A_n) < \infty$  then  $P(A_n \text{ i.o.}) = 0$ .
- ▶ Second Borel-Cantelli lemma: If  $A_n$  are independent, then  $\sum_{n=1}^{\infty} P(A_n) = \infty$  implies  $P(A_n \text{ i.o.}) = 1$ .

# Kolmogorov zero-one law

- ► Consider sequence of random variables  $X_n$  on some probability space. Write  $\mathcal{F}'_n = \sigma(X_n, X_{n_1}, \ldots)$  and  $\mathcal{T} = \cap_n \mathcal{F}'_n$ .
- $\rightharpoonup \mathcal{T}$  is called the **tail**  $\sigma$ -**algebra**. It contains the information you can observe by looking only at stuff arbitrarily far into the future. Intuitively, membership in tail event doesn't change when finitely many  $X_n$  are changed.
- ▶ Event that  $X_n$  converge to a limit is example of a tail event. Other examples?
- ▶ **Theorem:** If  $X_1, X_2, ...$  are independent and  $A \in \mathcal{T}$  then  $P(A) \in \{0, 1\}$ .


# Kolmogorov maximal inequality

▶ **Thoerem:** Suppose  $X_i$  are independent with mean zero and finite variances, and  $S_n = \sum_{i=1}^n X_i$ . Then

$$P(\max_{1\leq k\leq n}|S_k|\geq x)\leq x^{-2}\mathrm{Var}(S_n)=x^{-2}E|S_n|^2.$$

► Main idea of proof: Consider first time maximum is exceeded. Bound below the expected square sum on that event.


#### Kolmogorov three-series theorem

- ▶ **Theorem:** Let  $X_1, X_2, ...$  be independent and fix A > 0. Write  $Y_i = X_i 1_{(|X_i| \le A)}$ . Then  $\sum X_i$  converges a.s. if and only if the following are all true:

  - $\sum_{n=1}^{\infty} EY_n$  converges
  - $\sum_{n=1}^{\infty} \operatorname{Var}(Y_n) < \infty$
- ▶ Main ideas behind the proof: Kolmogorov zero-one law implies that  $\sum X_i$  converges with probability  $p \in \{0,1\}$ . We just have to show that p=1 when all hypotheses are satisfied (sufficiency of conditions) and p=0 if any one of them fails (necessity).
- ▶ To prove sufficiency, apply Borel-Cantelli to see that probability that  $X_n \neq Y_n$  i.o. is zero. Subtract means from  $Y_n$ , reduce to case that each  $Y_n$  has mean zero. Apply Kolmogorov maximal inequality.

18.175 Lecture 11

Recollections

Recollections

#### Recall: moment generating functions

- ▶ Let *X* be a random variable.
- ▶ The **moment generating function** of X is defined by  $M(t) = M_X(t) := E[e^{tX}].$
- When X is discrete, can write  $M(t) = \sum_{x} e^{tx} p_X(x)$ . So M(t) is a weighted average of countably many exponential functions.
- ▶ When X is continuous, can write  $M(t) = \int_{-\infty}^{\infty} e^{tx} f(x) dx$ . So M(t) is a weighted average of a continuum of exponential functions.
- We always have M(0) = 1.
- ▶ If b > 0 and t > 0 then  $E[e^{tX}] \ge E[e^{t\min\{X,b\}}] \ge P\{X \ge b\}e^{tb}.$
- ▶ If X takes both positive and negative values with positive probability then M(t) grows at least exponentially fast in |t| as  $|t| \to \infty$ .


18.175 Lecture 11

#### Recall: moment generating functions for i.i.d. sums

- ▶ We showed that if Z = X + Y and X and Y are independent, then  $M_Z(t) = M_X(t)M_Y(t)$
- ▶ If  $X_1 ... X_n$  are i.i.d. copies of X and  $Z = X_1 + ... + X_n$  then what is  $M_Z$ ?
- ▶ Answer:  $M_X^n$ . Follows by repeatedly applying formula above.
- This a big reason for studying moment generating functions. It helps us understand what happens when we sum up a lot of independent copies of the same random variable.

18.175 Lecture 11 11

#### Large deviations

- ▶ Consider i.i.d. random variables  $X_i$ . Want to show that if  $\phi(\theta) := M_{X_i}(\theta) = E \exp(\theta X_i)$  is less than infinity for some  $\theta > 0$ , then  $P(S_n \ge na) \to 0$  exponentially fast when  $a > E[X_i]$ .
- ▶ Kind of a quantitative form of the weak law of large numbers. The empirical average  $A_n$  is *very* unlikely to  $\epsilon$  away from its expected value (where "very" means with probability less than some exponentially decaying function of n).
- ▶ Write  $\gamma(a) = \lim_{n\to\infty} \frac{1}{n} \log P(S_n \ge na)$ . It gives the "rate" of exponential decay as a function of a.

18.175 Lecture 11 12

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

#### 18.175: Lecture 12

# **DeMoivre-Laplace and weak convergence**

Scott Sheffield

MIT

DeMoivre-Laplace limit theorem

Weak convergence

DeMoivre-Laplace limit theorem

Weak convergence

# DeMoivre-Laplace limit theorem

- ▶ Let  $X_i$  be i.i.d. random variables. Write  $S_n = \sum_{i=1}^n X_i$ .
- Suppose each  $X_i$  is 1 with probability p and 0 with probability q = 1 p.
- DeMoivre-Laplace limit theorem:

$$\lim_{n\to\infty} P\{a \leq \frac{S_n - np}{\sqrt{npq}} \leq b\} \to \Phi(b) - \Phi(a).$$

- ► Here  $\Phi(b) \Phi(a) = P\{a \le Z \le b\}$  when Z is a standard normal random variable.
- ▶  $\frac{S_n np}{\sqrt{npq}}$  describes "number of standard deviations that  $S_n$  is above or below its mean".
- ▶ **Proof idea:** use binomial coefficients and Stirling's formula.
- ▶ Question: Does similar statement hold if *X<sub>i</sub>* are i.i.d. from some other law?
- ▶ Central limit theorem: Yes, if they have finite variance.

# Local p = 1/2 DeMoivre-Laplace limit theorem

▶ **Stirling:**  $n! \sim n^n e^{-n} \sqrt{2\pi n}$  where  $\sim$  means ratio tends to one.


► **Theorem:** If  $2k/\sqrt{2n} \to x$  then  $P(S_{2n} = 2k) \sim (\pi n)^{-1/2} e^{-x^2/2}$ .

DeMoivre-Laplace limit theorem

Weak convergence

DeMoivre-Laplace limit theorem

Weak convergence

## Weak convergence

- Let X be random variable,  $X_n$  a sequence of random variables.
- ▶ Say  $X_n$  converge in distribution or converge in law to X if  $\lim_{n\to\infty} F_{X_n}(x) = F_X(x)$  at all  $x \in \mathbb{R}$  at which  $F_X$  is continuous.
- ▶ Also say that the  $F_n = F_{X_n}$  converge weakly to  $F = F_X$ .
- ▶ **Example:**  $X_i$  chosen from  $\{-1,1\}$  with i.i.d. fair coin tosses: then  $n^{-1/2} \sum_{i=1}^{n} X_i$  converges in law to a normal random variable (mean zero, variance one) by Demoivre-Laplace.
- **Example:** If  $X_n$  is equal to 1/n a.s. then  $X_n$  converge weakly to an X equal to 0 a.s. Note that  $\lim_{n\to\infty} F_n(0) \neq F(0)$  in this case.
- **Example:** If  $X_i$  are i.i.d. then the empirical distributions converge a.s. to law of  $X_1$  (Glivenko-Cantelli).
- **Example:** Let  $X_n$  be the *n*th largest of 2n + 1 points chosen i.i.d. from fixed law.


## Convergence results

- ▶ **Theorem:** If  $F_n \to F_\infty$ , then we can find corresponding random variables  $Y_n$  on a common measure space so that  $Y_n \to Y_\infty$  almost surely.
- ▶ **Proof idea:** Take  $\Omega = (0,1)$  and  $Y_n = \sup\{y : F_n(y) < x\}$ .
- ▶ **Theorem:**  $X_n \Longrightarrow X_\infty$  if and only if for every bounded continuous g we have  $Eg(X_n) \to Eg(X_\infty)$ .
- ▶ **Proof idea:** Define  $X_n$  on common sample space so converge a.s., use bounded convergence theorem.
- ▶ **Theorem:** Suppose g is measurable and its set of discontinuity points has  $\mu_X$  measure zero. Then  $X_n \Longrightarrow X_\infty$  implies  $g(X_n) \Longrightarrow g(X)$ .
- ▶ **Proof idea:** Define  $X_n$  on common sample space so converge a.s., use bounded convergence theorem.

## Compactness

- ▶ **Theorem:** Every sequence  $F_n$  of distribution has subsequence converging to right continuous nondecreasing F so that  $\lim F_{n(k)}(y) = F(y)$  at all continuity points of F.
- Limit may not be a distribution function.
- Need a "tightness" assumption to make that the case. Say  $\mu_n$  are **tight** if for every  $\epsilon$  we can find an M so that  $\mu_n[-M,M]<\epsilon$  for all n. Define tightness analogously for corresponding real random variables or distributions functions.
- ▶ **Theorem:** Every subsequential limit of the  $F_n$  above is the distribution function of a probability measure if and only if the  $F_n$  are tight.

18.175 Lecture 12 10

#### Total variation norm

- ▶ If we have two probability measures  $\mu$  and  $\nu$  we define the **total variation distance** between them is  $||\mu \nu|| := \sup_{B} |\mu(B) \nu(B)|$ .
- Intuitively, it two measures are close in the total variation sense, then (most of the time) a sample from one measure looks like a sample from the other.
- Convergence in total variation norm is much stronger than weak convergence.

DeMoivre-Laplace limit theorem

Weak convergence

DeMoivre-Laplace limit theorem

Weak convergence

#### Characteristic functions

- Let X be a random variable.
- ▶ The **characteristic function** of X is defined by  $\phi(t) = \phi_X(t) := E[e^{itX}]$ . Like M(t) except with i thrown in.
- Recall that by definition  $e^{it} = \cos(t) + i\sin(t)$ .
- Characteristic functions are similar to moment generating functions in some ways.
- For example,  $\phi_{X+Y} = \phi_X \phi_Y$ , just as  $M_{X+Y} = M_X M_Y$ , if X and Y are independent.
- And  $\phi_{aX}(t) = \phi_X(at)$  just as  $M_{aX}(t) = M_X(at)$ .
- And if X has an mth moment then  $E[X^m] = i^m \phi_X^{(m)}(0)$ .
- ▶ But characteristic functions have an advantage: they are well defined at all *t* for all random variables *X*.

# Continuity theorems

► Lévy's continuity theorem: if

$$\lim_{n\to\infty}\phi_{X_n}(t)=\phi_X(t)$$

for all t, then  $X_n$  converge in law to X.

- ▶ By this theorem, we can prove the weak law of large numbers by showing  $\lim_{n\to\infty}\phi_{A_n}(t)=\phi_{\mu}(t)=e^{it\mu}$  for all t. In the special case that  $\mu=0$ , this amounts to showing  $\lim_{n\to\infty}\phi_{A_n}(t)=1$  for all t.
- ▶ Moment generating analog: if moment generating functions  $M_{X_n}(t)$  are defined for all t and n and  $\lim_{n\to\infty} M_{X_n}(t) = M_X(t)$  for all t, then  $X_n$  converge in law to X.

18.175 Lecture 12 15

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 13 More large deviations

Scott Sheffield

MIT

Legendre transform

Large deviations

Legendre transform

Large deviations

#### Legendre transform

▶ Define **Legendre transform** (or Legendre dual) of a function  $\Lambda : \mathbb{R}^d \to \mathbb{R}$  by

$$\Lambda^*(x) = \sup_{\lambda \in \mathbb{R}^d} \{(\lambda, x) - \Lambda(\lambda)\}.$$

- Let's describe the Legendre dual geometrically if d=1:  $\Lambda^*(x)$  is where tangent line to  $\Lambda$  of slope x intersects the real axis. We can "roll" this tangent line around the convex hull of the graph of  $\Lambda$ , to get all  $\Lambda^*$  values.
- ▶ Is the Legendre dual always convex?
- ▶ What is the Legendre dual of  $x^2$ ? Of the function equal to 0 at 0 and  $\infty$  everywhere else?
- ▶ How are derivatives of  $\Lambda$  and  $\Lambda$ \* related?
- ▶ What is the Legendre dual of the Legendre dual of a convex function?
- ► What's the higher dimensional analog of rolling the tangent line?

Legendre transform

Large deviations

Legendre transform

Large deviations

### Recall: moment generating functions

- ▶ Let *X* be a random variable.
- ▶ The **moment generating function** of X is defined by  $M(t) = M_X(t) := E[e^{tX}].$
- ▶ When X is discrete, can write  $M(t) = \sum_{x} e^{tx} p_X(x)$ . So M(t) is a weighted average of countably many exponential functions.
- ▶ When X is continuous, can write  $M(t) = \int_{-\infty}^{\infty} e^{tx} f(x) dx$ . So M(t) is a weighted average of a continuum of exponential functions.
- We always have M(0) = 1.
- ▶ If b > 0 and t > 0 then  $E[e^{tX}] \ge E[e^{t\min\{X,b\}}] \ge P\{X \ge b\}e^{tb}.$
- ▶ If X takes both positive and negative values with positive probability then M(t) grows at least exponentially fast in |t| as  $|t| \to \infty$ .


18.175 Lecture 13

## Recall: moment generating functions for i.i.d. sums

- ▶ We showed that if Z = X + Y and X and Y are independent, then  $M_Z(t) = M_X(t)M_Y(t)$
- ▶ If  $X_1 ... X_n$  are i.i.d. copies of X and  $Z = X_1 + ... + X_n$  then what is  $M_Z$ ?
- ▶ Answer:  $M_X^n$ .

### Large deviations

- ▶ Consider i.i.d. random variables  $X_i$ . Can we show that  $P(S_n \ge na) \to 0$  exponentially fast when  $a > E[X_i]$ ?
- ▶ Kind of a quantitative form of the weak law of large numbers. The empirical average  $A_n$  is *very* unlikely to  $\epsilon$  away from its expected value (where "very" means with probability less than some exponentially decaying function of n).

# General large deviation principle

- More general framework: a *large deviation principle* describes limiting behavior as  $n \to \infty$  of family  $\{\mu_n\}$  of measures on measure space  $(\mathcal{X}, \mathcal{B})$  in terms of a *rate function I*.
- ▶ The **rate function** is a lower-semicontinuous map  $I: \mathcal{X} \to [0, \infty]$ . (The sets  $\{x: I(x) \le a\}$  are closed rate function called "good" if these sets are compact.)
- ▶ **DEFINITION:**  $\{\mu_n\}$  satisfy LDP with rate function I and speed n if for all  $\Gamma \in \mathcal{B}$ ,

$$-\inf_{x\in\Gamma^0}I(x)\leq \liminf_{n\to\infty}\frac{1}{n}\log\mu_n(\Gamma)\leq \limsup_{n\to\infty}\frac{1}{n}\log\mu_n(\Gamma)\leq -\inf_{x\in\overline{\Gamma}}I(x).$$

- ▶ **INTUITION:** when "near x" the probability density function for  $\mu_n$  is tending to zero like  $e^{-l(x)n}$ , as  $n \to \infty$ .
- **Simple case:** I is continuous,  $\Gamma$  is closure of its interior.
- ▶ **Question:** How would *I* change if we replaced the measures  $\mu_n$  by weighted measures  $e^{(\lambda n, \cdot)}\mu_n$ ?
- ▶ Replace I(x) by  $I(x) (\lambda, x)$ ? What is  $\inf_{x} I(x) (\lambda, x)$ ?

#### Cramer's theorem

- Let  $\mu_n$  be law of empirical mean  $A_n = \frac{1}{n} \sum_{j=1}^n X_j$  for i.i.d. vectors  $X_1, X_2, \dots, X_n$  in  $\mathbb{R}^d$  with same law as X.
- ▶ Define **log moment generating function** of *X* by

$$\Lambda(\lambda) = \Lambda_X(\lambda) = \log M_X(\lambda) = \log \mathbb{E}e^{(\lambda,X)},$$

where  $(\cdot, \cdot)$  is inner product on  $\mathbb{R}^d$ .

Define Legendre transform of Λ by

$$\Lambda^*(x) = \sup_{\lambda \in \mathbb{R}^d} \{(\lambda, x) - \Lambda(\lambda)\}.$$

▶ **CRAMER'S THEOREM:**  $\mu_n$  satisfy LDP with convex rate function  $\Lambda^*$ .

# Thinking about Cramer's theorem

- Let  $\mu_n$  be law of empirical mean  $A_n = \frac{1}{n} \sum_{j=1}^n X_j$ .
- ▶ **CRAMER'S THEOREM:**  $\mu_n$  satisfy LDP with convex rate function

$$I(x) = \Lambda^*(x) = \sup_{\lambda \in \mathbb{R}^d} \{(\lambda, x) - \Lambda(\lambda)\},$$

where  $\Lambda(\lambda) = \log M(\lambda) = \mathbb{E}e^{(\lambda, X_1)}$ .

▶ This means that for all  $\Gamma \in \mathcal{B}$  we have this **asymptotic lower** bound on probabilities  $\mu_n(\Gamma)$ 

$$-\inf_{x\in\Gamma^0}I(x)\leq \liminf_{n\to\infty}\frac{1}{n}\log\mu_n(\Gamma),$$

so (up to sub-exponential error)  $\mu_n(\Gamma) \geq e^{-n\inf_{x \in \Gamma^0} I(x)}$ .

▶ and this **asymptotic upper bound** on the probabilities  $\mu_n(\Gamma)$ 

$$\limsup_{n\to\infty}\frac{1}{n}\log\mu_n(\Gamma)\leq -\inf_{x\in\overline{\Gamma}}I(x),$$

which says (up to subexponential error)  $\mu_n(\Gamma) \leq e^{-n \inf_{x \in \Gamma} I(x)}$ .

# Proving Cramer upper bound

- ► Recall that  $I(x) = \Lambda^*(x) = \sup_{\lambda \in \mathbb{R}^d} \{(\lambda, x) \Lambda(\lambda)\}.$
- For simplicity, assume that  $\Lambda$  is defined for all x (which implies that X has moments of all orders and  $\Lambda$  and  $\Lambda^*$  are strictly convex, and the derivatives of  $\Lambda$  and  $\Lambda'$  are inverses of each other). It is also enough to consider the case X has mean zero, which implies that  $\Lambda(0) = 0$  is a minimum of  $\Lambda$ , and  $\Lambda^*(0) = 0$  is a minimum of  $\Lambda^*$ .
- ▶ We aim to show (up to subexponential error) that  $\mu_n(\Gamma) \leq e^{-n\inf_{x \in \overline{\Gamma}} I(x)}$ .
- ▶ If  $\Gamma$  were singleton set  $\{x\}$  we could find the  $\lambda$  corresponding to x, so  $\Lambda^*(x) = (x, \lambda) \Lambda(\lambda)$ . Note then that

$$\mathbb{E}e^{(n\lambda,A_n)}=\mathbb{E}e^{(\lambda,S_n)}=M_X^n(\lambda)=e^{n\Lambda(\lambda)},$$

and also  $\mathbb{E}e^{(n\lambda,A_n)} \geq e^{n(\lambda,x)}\mu_n\{x\}$ . Taking logs and dividing by n gives  $\Lambda(\lambda) \geq \frac{1}{n}\log\mu_n + (\lambda,x)$ , so that  $\frac{1}{n}\log\mu_n(\Gamma) \leq -\Lambda^*(x)$ , as desired.

General Γ: cut into finitely many pieces, bound each piece?

1:

# Proving Cramer lower bound

- ▶ Recall that  $I(x) = \Lambda^*(x) = \sup_{\lambda \in \mathbb{R}^d} \{(\lambda, x) \Lambda(\lambda)\}.$
- ▶ We aim to show that asymptotically  $\mu_n(\Gamma) \ge e^{-n\inf_{x \in \Gamma^0} I(x)}$ .
- ▶ It's enough to show that for each given  $x \in \Gamma^0$ , we have that asymptotically  $\mu_n(\Gamma) \ge e^{-n\inf_{x \in \Gamma^0} I(x)}$ .
- ▶ Idea is to weight the law of X by  $e^{(\lambda,x)}$  for some  $\lambda$  and normalize to get a new measure whose expectation is this point x. In this new measure,  $A_n$  is "typically" in  $\Gamma$  for large  $\Gamma$ , so the probability is of order 1.
- ▶ But by how much did we have to modify the measure to make this typical? Not more than by factor  $e^{-n\inf_{x\in\Gamma^0}I(x)}$ .

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 14

# Weak convergence and characteristic functions

Scott Sheffield

MIT

Weak convergence

Characteristic functions


Weak convergence

Characteristic functions

## Convergence results

- ▶ **Theorem:** If  $F_n \to F_\infty$ , then we can find corresponding random variables  $Y_n$  on a common measure space so that  $Y_n \to Y_\infty$  almost surely.
- ▶ **Proof idea:** Take  $\Omega = (0,1)$  and  $Y_n = \sup\{y : F_n(y) < x\}$ .
- ▶ **Theorem:**  $X_n \Longrightarrow X_\infty$  if and only if for every bounded continuous g we have  $Eg(X_n) \to Eg(X_\infty)$ .
- ▶ **Proof idea:** Define  $X_n$  on common sample space so converge a.s., use bounded convergence theorem.
- ▶ **Theorem:** Suppose g is measurable and its set of discontinuity points has  $\mu_X$  measure zero. Then  $X_n \Longrightarrow X_\infty$  implies  $g(X_n) \Longrightarrow g(X)$ .
- ▶ **Proof idea:** Define  $X_n$  on common sample space so converge a.s., use bounded convergence theorem.


# Compactness

- ▶ **Theorem:** Every sequence  $F_n$  of distribution has subsequence converging to right continuous nondecreasing F so that  $\lim F_{n(k)}(y) = F(y)$  at all continuity points of F.
- ▶ Limit may not be a distribution function.
- Need a "tightness" assumption to make that the case. Say  $\mu_n$  are **tight** if for every  $\epsilon$  we can find an M so that  $\mu_n[-M,M]<\epsilon$  for all n. Define tightness analogously for corresponding real random variables or distributions functions.
- ▶ **Theorem:** Every subsequential limit of the  $F_n$  above is the distribution function of a probability measure if and only if the  $F_n$  are tight.


#### Total variation norm

- ▶ If we have two probability measures  $\mu$  and  $\nu$  we define the **total variation distance** between them is  $||\mu \nu|| := \sup_{B} |\mu(B) \nu(B)|$ .
- Intuitively, it two measures are close in the total variation sense, then (most of the time) a sample from one measure looks like a sample from the other.
- ► Corresponds to *L*<sub>1</sub> distance between density functions when these exist.
- Convergence in total variation norm is much stronger than weak convergence. Discrete uniform random variable  $U_n$  on  $(1/n, 2/n, 3/n, \ldots, n/n)$  converges weakly to uniform random variable U on [0,1]. But total variation distance between  $U_n$  and U is 1 for all n.

18.175 Lecture 14

Weak convergence

Characteristic functions

Weak convergence

Characteristic functions

#### Characteristic functions

- Let X be a random variable.
- ► The **characteristic function** of X is defined by  $\phi(t) = \phi_X(t) := E[e^{itX}].$
- ▶ Recall that by definition  $e^{it} = \cos(t) + i\sin(t)$ .
- ▶ Characteristic function  $\phi_X$  similar to moment generating function  $M_X$ .
- $\phi_{X+Y} = \phi_X \phi_Y$ , just as  $M_{X+Y} = M_X M_Y$ , if X and Y are independent.
- ▶ And  $\phi_{aX}(t) = \phi_X(at)$  just as  $M_{aX}(t) = M_X(at)$ .
- ▶ And if X has an mth moment then  $E[X^m] = i^m \phi_X^{(m)}(0)$ .
- Characteristic functions are well defined at all t for all random variables X.

18.175 Lecture 14

# Characteristic function properties

- $\phi(0) = 1$
- $\qquad \phi(-t) = \overline{\phi(t)}$
- $|\phi(t)| = |Ee^{itX}| \le E|e^{itX}| = 1.$
- ▶  $|\phi(t+h) \phi(t)| \le E|e^{ihX} 1|$ , so  $\phi(t)$  uniformly continuous on  $(-\infty, \infty)$
- $\rightharpoonup Ee^{it(aX+b)} = e^{itb}\phi(at)$

# Characteristic function examples

- ▶ Coin: If P(X = 1) = P(X = -1) = 1/2 then  $\phi_{X}(t) = (e^{it} + e^{-it})/2 = \cos t$ .
- ► That's periodic. Do we always have periodicity if X is a random integer?
- **Poisson:** If X is Poisson with parameter  $\lambda$  then  $\phi_X(t) = \sum_{k=0}^{\infty} e^{-\lambda} \frac{\lambda^k e^{itk}}{k!} = \exp(\lambda(e^{it} - 1)).$
- Why does doubling  $\lambda$  amount to squaring  $\phi_X$ ?
- ▶ **Normal:** If X is standard normal, then  $\phi_X(t) = e^{-t^2/2}$ .
- ls  $\phi_X$  always real when the law of X is symmetric about zero?
- **Exponential:** If X is standard exponential (density  $e^{-x}$  on  $(0,\infty)$ ) then  $\phi_X(t) = 1/(1-it)$ .


▶ Bilateral exponential: if  $f_X(t) = e^{-|x|}/2$  on  $\mathbb R$  then  $\phi_X(t) = 1/(1+t^2)$ . Use linearity of  $f_X \to \phi_X$ .

18.175 Lecture 14

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.175: Lecture 15

# Characteristic functions and central limit theorem

Scott Sheffield

MIT

# Outline

Characteristic functions

# Outline

Characteristic functions

#### Characteristic functions

- Let X be a random variable.
- ► The **characteristic function** of X is defined by  $\phi(t) = \phi_X(t) := E[e^{itX}].$
- ▶ Recall that by definition  $e^{it} = \cos(t) + i\sin(t)$ .
- ▶ Characteristic function  $\phi_X$  similar to moment generating function  $M_X$ .
- $\phi_{X+Y} = \phi_X \phi_Y$ , just as  $M_{X+Y} = M_X M_Y$ , if X and Y are independent.
- ▶ And  $\phi_{aX}(t) = \phi_X(at)$  just as  $M_{aX}(t) = M_X(at)$ .
- ▶ And if X has an mth moment then  $E[X^m] = i^m \phi_X^{(m)}(0)$ .
- Characteristic functions are well defined at all t for all random variables X.

# Characteristic function properties

- $\phi(0) = 1$
- $\qquad \phi(-t) = \overline{\phi(t)}$
- $|\phi(t)| = |Ee^{itX}| \le E|e^{itX}| = 1.$
- ▶  $|\phi(t+h) \phi(t)| \le E|e^{ihX} 1|$ , so  $\phi(t)$  uniformly continuous on  $(-\infty, \infty)$
- $Ee^{it(aX+b)} = e^{itb}\phi(at)$

## Characteristic function examples

- ► Coin: If P(X = 1) = P(X = -1) = 1/2 then  $\phi_X(t) = (e^{it} + e^{-it})/2 = \cos t$ .
- ► That's periodic. Do we always have periodicity if *X* is a random integer?
- ▶ **Poisson:** If X is Poisson with parameter  $\lambda$  then  $\phi_X(t) = \sum_{k=0}^{\infty} e^{-\lambda} \frac{\lambda^k e^{itk}}{k!} = \exp(\lambda(e^{it} 1)).$
- ▶ Why does doubling  $\lambda$  amount to squaring  $\phi_X$ ?
- ▶ **Normal:** If X is standard normal, then  $\phi_X(t) = e^{-t^2/2}$ .
- ▶ Is  $\phi_X$  always real when the law of X is symmetric about zero?
- **Exponential:** If X is standard exponential (density  $e^{-x}$  on  $(0,\infty)$ ) then  $\phi_X(t)=1/(1-it)$ .
- ▶ Bilateral exponential: if  $f_X(t) = e^{-|x|}/2$  on  $\mathbb{R}$  then  $\phi_X(t) = 1/(1+t^2)$ . Use linearity of  $f_X \to \phi_X$ .

#### Fourier inversion formula

- ▶ If  $f : \mathbb{R} \to \mathbb{C}$  is in  $L^1$ , write  $\hat{f}(t) := \int_{-\infty}^{\infty} f(x)e^{-itx}dx$ .
- ► Fourier inversion: If f is nice:  $f(x) = \frac{1}{2\pi} \int \hat{f}(t)e^{itx}dt$ .
- Easy to check this when f is density function of a Gaussian. Use linearity of  $f \to \hat{f}$  to extend to linear combinations of Gaussians, or to convolutions with Gaussians.
- ▶ Show  $f \to \hat{f}$  is an isometry of Schwartz space (endowed with  $L^2$  norm). Extend definition to  $L^2$  completion.
- ► Convolution theorem: If

$$h(x) = (f * g)(x) = \int_{-\infty}^{\infty} f(y)g(x - y)dy,$$

then

$$\hat{h}(t) = \hat{f}(t)\hat{g}(t).$$

Possible application?

$$\int 1_{[a,b]}(x)f(x)dx = \widehat{(1_{[a,b]}f)}(0) = \widehat{(f*1_{[a,b]})}(0) = \int \widehat{f}(t)\widehat{1_{[a,b]}}(-t)dx.$$

## Characteristic function inversion formula

- ▶ If the map  $\mu_X \to \phi_X$  is linear, is the map  $\phi \to \mu[a,b]$  (for some fixed [a,b]) a linear map? How do we recover  $\mu[a,b]$  from  $\phi$ ?
- Say  $\phi(t) = \int e^{itx} \mu(x)$ .
- Inversion theorem:

$$\lim_{T\to\infty}(2\pi)^{-1}\int_{-T}^T\frac{e^{-ita}-e^{itb}}{it}\phi(t)dt=\mu(a,b)+\frac{1}{2}\mu(\{a,b\})$$

► Main ideas of proof: Write

$$I_T = \int \frac{e^{-ita} - e^{-itb}}{it} \phi(t) dt = \int_{-T}^T \int \frac{e^{-ita} - e^{-itb}}{it} e^{itx} \mu(x) dt.$$

- ▶ Observe that  $\frac{e^{-ita}-e^{-itb}}{it} = \int_a^b e^{-ity} dy$  has modulus bounded by b-a.
- $\triangleright$  That means we can use Fubini to compute  $I_T$ .

#### Bochner's theorem

- ▶ Given any function  $\phi$  and any points  $x_1, \ldots, x_n$ , we can consider the matrix with i, j entry given by  $\phi(x_i x_j)$ . Call  $\phi$  **positive definite** if this matrix is always positive semidefinite Hermitian.
- ▶ Bochner's theorem: a continuous function from  $\mathbb R$  to  $\mathbb R$  with  $\phi(1)=1$  is a characteristic function of a some probability measure on  $\mathbb R$  if and only if it is positive definite.
- Positive definiteness kind of comes from fact that variances of random variables are non-negative.
- ► The set of all possible characteristic functions is a pretty nice set.

## Continuity theorems

Lévy's continuity theorem: if

$$\lim_{n\to\infty}\phi_{X_n}(t)=\phi_X(t)$$

for all t, then  $X_n$  converge in law to X.

- ▶ Slightly stronger theorem: If  $\mu_n \implies \mu_\infty$  then  $\phi_n(t) \to \phi_\infty(t)$  for all t. Conversely, if  $\phi_n(t)$  converges to a limit that is continuous at 0, then the associated sequence of distributions  $\mu_n$  is tight and converges weakly to measure  $\mu$  with characteristic function  $\phi$ .
- ▶ **Proof ideas:** First statement easy (since  $X_n \Longrightarrow X$  implies  $Eg(X_n) \to Eg(X)$  for any bounded continuous g). To get second statement, first play around with Fubini and establish tightness of the  $\mu_n$ . Then note that any subsequential limit of the  $\mu_n$  must be equal to  $\mu$ . Use this to argue that  $\int f d\mu_n$  converges to  $\int f d\mu$  for every bounded continuous f.

## Moments, derivatives, CLT

- ▶ If  $\int |x|^n \mu(x) < \infty$  then the characteristic function  $\phi$  of  $\mu$  has a continuous derivative of order n given by  $\phi^{(n)}(t) = \int (ix)^n e^{itx} \mu(dx)$ .
- ▶ Indeed, if  $E|X|^2 < \infty$  and EX = 0 then  $\phi(t) = 1 t^2 E(X^2)/2o(t^2)$ .
- This and the continuity theorem together imply the central limit theorem.
- ▶ **Theorem:** Let  $X_1, X_2, ...$  by i.i.d. with  $EX_i = \mu$ ,  $Var(X_i) = \sigma^2 \in (0, \infty)$ . If  $S_n = X_1 + ... + X_n$  then  $(S_n n\mu)/(\sigma n^{1/2})$  converges in law to a standard normal.

MIT OpenCourseWare http://ocw.mit.edu

### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 16 Central limit theorem variants

Scott Sheffield

MIT

CLT idea

CLT idea

#### Recall Fourier inversion formula

- ▶ If  $f : \mathbb{R} \to \mathbb{C}$  is in  $L^1$ , write  $\hat{f}(t) := \int_{-\infty}^{\infty} f(x)e^{-itx}dx$ .
- ► Fourier inversion: If f is nice:  $f(x) = \frac{1}{2\pi} \int \hat{f}(t)e^{itx}dt$ .
- Easy to check this when f is density function of a Gaussian. Use linearity of  $f \to \hat{f}$  to extend to linear combinations of Gaussians, or to convolutions with Gaussians.
- ▶ Show  $f \to \hat{f}$  is an isometry of Schwartz space (endowed with  $L^2$  norm). Extend definition to  $L^2$  completion.
- Convolution theorem: If

$$h(x) = (f * g)(x) = \int_{-\infty}^{\infty} f(y)g(x - y)dy,$$

then

$$\hat{h}(t) = \hat{f}(t)\hat{g}(t).$$

► **Observation:** can define Fourier transforms of generalized functions. Can interpret finite measure as generalized

#### Recall Bochner's theorem

- ▶ Given any function  $\phi$  and any points  $x_1, \ldots, x_n$ , we can consider the matrix with i, j entry given by  $\phi(x_i x_j)$ . Call  $\phi$  **positive definite** if this matrix is always positive semidefinite Hermitian.
- ▶ Bochner's theorem: a continuous function from  $\mathbb{R}$  to  $\mathbb{R}$  with  $\phi(1)=1$  is a characteristic function of a some probability measure on  $\mathbb{R}$  if and only if it is positive definite.
- Positive definiteness kind of comes from fact that variances of random variables are non-negative.
- ► The set of all possible characteristic functions is a pretty nice set.
- ▶ The Fourier transform is a natural map from set of all probability measures on  $\mathbb{R}$  (which can be described by their distribution functions F) to the set of possible characteristic functions.

18.175 Lecture 16

# Recall continuity theorem

▶ Strong continuity theorem: If  $\mu_n \implies \mu_\infty$  then  $\phi_n(t) \to \phi_\infty(t)$  for all t. Conversely, if  $\phi_n(t)$  converges to a limit that is continuous at 0, then the associated sequence of distributions  $\mu_n$  is tight and converges weakly to a measure  $\mu$  with characteristic function  $\phi$ .

#### Recall CLT idea

- Let X be a random variable.
- ► The **characteristic function** of X is defined by  $\phi(t) = \phi_X(t) := E[e^{itX}].$
- ▶ And if X has an mth moment then  $E[X^m] = i^m \phi_X^{(m)}(0)$ .
- ▶ In particular, if E[X] = 0 and  $E[X^2] = 1$  then  $\phi_X(0) = 1$  and  $\phi_X'(0) = 0$  and  $\phi_X''(0) = -1$ .
- ▶ Write  $L_X := -\log \phi_X$ . Then  $L_X(0) = 0$  and  $L_X'(0) = -\phi_X'(0)/\phi_X(0) = 0$  and  $L_X'' = -(\phi_X''(0)\phi_X(0) \phi_X'(0)^2)/\phi_X(0)^2 = 1$ .
- If  $V_n = n^{-1/2} \sum_{i=1}^n X_i$  where  $X_i$  are i.i.d. with law of X, then  $L_{V_n}(t) = nL_X(n^{-1/2}t)$ .
- When we zoom in on a twice differentiable function near zero (scaling vertically by n and horizontally by  $\sqrt{n}$ ) the picture looks increasingly like a parabola.

18.175 Lecture 16

CLT idea

**CLT** idea

# Lindeberg-Feller theorem

- CLT is pretty special. What other kinds of sums are approximately Gaussian?
- ▶ **Triangular arrays:** Suppose  $X_{n,m}$  are independent expectation-zero random variables when  $1 \le m \le n$ .
- ▶ Suppose  $\sum_{m=1}^{n} EX_{n,m}^2 \to \sigma^2 > 0$  and for all  $\epsilon$ ,  $\lim_{n\to\infty} E(|X_{n,m}|^2; |X_{n,m}| > \epsilon) = 0$ .
- ▶ Then  $S_n = X_{n,1} + X_{n,2} + \ldots + X_{n,n} \implies \sigma \chi$  (where  $\chi$  is standard normal) as  $n \to \infty$ .
- ▶ **Proof idea:** Use characteristic functions  $\phi_{n,m} = \phi_{X_{n,m}}$ . Try to get some uniform handle on how close they are to their quadratic approximations.

18.175 Lecture 16

#### Berry-Esseen theorem

- ▶ If  $X_i$  are i.i.d. with mean zero, variance  $\sigma^2$ , and  $E|X_i|^3 = \rho < \infty$ , and  $F_n(x)$  is distribution of  $(X_1 + \ldots + X_n)/(\sigma\sqrt{n})$  and  $\Phi(x)$  is standard normal distribution, then  $|F_n(x) \Phi(x)| \leq 3\rho/(\sigma^3\sqrt{n})$ .
- Provided one has a third moment, CLT convergence is very quick.
- Proof idea: You can convolve with something that has a characteristic function with compact support. Play around with Fubini, error estimates.

#### Local limit theorems for walks on $\mathbb Z$

- ▶ Suppose  $X \in b + h\mathbb{Z}$  a.s. for some fixed constants b and h.
- Observe that if  $\phi_X(\lambda) = 1$  for some  $\lambda \neq 0$  then X is supported on (some translation of)  $(2\pi/\lambda)\mathbb{Z}$ . If this holds for all  $\lambda$ , then X is a.s. some constant. When the former holds but not the latter (i.e.,  $\phi_X$  is periodic but not identically 1) we call X a **lattice random variable**.
- Write  $p_n(x) = P(S_n/\sqrt{n} = x)$  for  $x \in \mathcal{L}_n := (nb + h\mathbb{Z})/\sqrt{n}$  and  $n(x) = (2\pi\sigma^2)^{-1/2} \exp(-x^2/2\sigma^2)$ .
- Assume  $X_i$  are i.i.d. lattice with  $EX_i = 0$  and  $EX_i^2 = \sigma^2 \in (0, \infty)$ . Theorem: As  $n \to \infty$ ,

$$\left|\sup_{x\in\mathcal{L}^n}|n^{1/2}/hp_n(x)-n(x)|\to 0.$$

**Proof idea:** Use characteristic functions, reduce to periodic integral problem. Note that for Y supported on  $a+\theta\mathbb{Z}$ , we have  $P(Y=x)=\frac{1}{2\pi/\theta}\int_{-\pi/\theta}^{\pi/\theta}e^{-itx}\phi_Y(t)dt$ .

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 17

### Poisson random variables

Scott Sheffield

MIT

More on random walks and local CLT

Poisson random variable convergence

More on random walks and local CLT

Poisson random variable convergence

### Recall local CLT for walks on $\mathbb Z$

- ▶ Suppose  $X \in b + h\mathbb{Z}$  a.s. for some fixed constants b and h.
- ▶ Observe that if  $\phi_X(\lambda) = 1$  for some  $\lambda \neq 0$  then X is supported on (some translation of)  $(2\pi/\lambda)\mathbb{Z}$ . If this holds for all  $\lambda$ , then X is a.s. some constant. When the former holds but not the latter (i.e.,  $\phi_X$  is periodic but not identically 1) we call X a **lattice random variable**.
- Write  $p_n(x) = P(S_n/\sqrt{n} = x)$  for  $x \in \mathcal{L}_n := (nb + h\mathbb{Z})/\sqrt{n}$  and  $n(x) = (2\pi\sigma^2)^{-1/2} \exp(-x^2/2\sigma^2)$ .
- Assume  $X_i$  are i.i.d. lattice with  $EX_i = 0$  and  $EX_i^2 = \sigma^2 \in (0, \infty)$ . **Theorem:** As  $n \to \infty$ ,

$$\left|\sup_{x\in\mathcal{L}^n}|n^{1/2}/hp_n(x)-n(x)|\to 0.$$

### Recall local CLT for walks on $\mathbb Z$

▶ **Proof idea:** Use characteristic functions, reduce to periodic integral problem. Look up "Fourier series". Note that for Y supported on  $a + \theta \mathbb{Z}$ , we have

$$P(Y = x) = \frac{1}{2\pi/\theta} \int_{-\pi/\theta}^{\pi/\theta} e^{-itx} \phi_Y(t) dt.$$

# Extending this idea to higher dimensions

- ► Example: suppose we have random walk on  $\mathbb{Z}$  that at each step tosses fair 4-sided coin to decide whether to go 1 unit left, 1 unit right, 2 units left, or 2 units right?
- ▶ What is the probability that the walk is back at the origin after one step? Two steps? Three steps?
- Let's compute this in Mathematica by writing out the characteristic function  $\phi_X$  for one-step increment X and calculating  $\int_0^{2\pi} \phi_X^k(t) dt/2\pi$ .
- ▶ How about a random walk on  $\mathbb{Z}^2$ ?
- ▶ Can one use this to establish when a random walk on  $\mathbb{Z}^d$  is recurrent versus transient?

More on random walks and local CLT

Poisson random variable convergence

More on random walks and local CLT

Poisson random variable convergence

# Poisson random variables: motivating questions

- ► How many raindrops hit a given square inch of sidewalk during a ten minute period?
- ▶ How many people fall down the stairs in a major city on a given day?
- ▶ How many plane crashes in a given year?
- ► How many radioactive particles emitted during a time period in which the expected number emitted is 5?
- ▶ How many calls to call center during a given minute?
- ▶ How many goals scored during a 90 minute soccer game?
- ► How many notable gaffes during 90 minute debate?
- ▶ **Key idea for all these examples:** Divide time into large number of small increments. Assume that during each increment, there is some small probability of thing happening (independently of other increments).

# Bernoulli random variable with n large and $np = \lambda$

- Let  $\lambda$  be some moderate-sized number. Say  $\lambda=2$  or  $\lambda=3$ . Let n be a huge number, say  $n=10^6$ .
- Suppose I have a coin that comes up heads with probability  $\lambda/n$  and I toss it n times.
- ► How many heads do I expect to see?
- Answer:  $np = \lambda$ .
- Let k be some moderate sized number (say k = 4). What is the probability that I see exactly k heads?
- ▶ Binomial formula:  $\binom{n}{k} p^k (1-p)^{n-k} = \frac{n(n-1)(n-2)...(n-k+1)}{k!} p^k (1-p)^{n-k}$ .
- ▶ This is approximately  $\frac{\lambda^k}{k!}(1-p)^{n-k} \approx \frac{\lambda^k}{k!}e^{-\lambda}$ .
- ▶ A **Poisson random variable** X with parameter  $\lambda$  satisfies  $P\{X = k\} = \frac{\lambda^k}{k!}e^{-\lambda}$  for integer  $k \ge 0$ .

#### Probabilities sum to one

- ▶ A **Poisson random variable** X with parameter  $\lambda$  satisfies  $p(k) = P\{X = k\} = \frac{\lambda^k}{k!}e^{-\lambda}$  for integer  $k \ge 0$ .
- ▶ How can we show that  $\sum_{k=0}^{\infty} p(k) = 1$ ?
- Use Taylor expansion  $e^{\lambda} = \sum_{k=0}^{\infty} \frac{\lambda^k}{k!}$ .

## Expectation

- ▶ A **Poisson random variable** X with parameter  $\lambda$  satisfies  $P\{X=k\}=\frac{\lambda^k}{k!}e^{-\lambda}$  for integer  $k\geq 0$ .
- ▶ What is *E*[*X*]?
- ▶ We think of a Poisson random variable as being (roughly) a Bernoulli (n, p) random variable with n very large and  $p = \lambda/n$ .
- ▶ This would suggest  $E[X] = \lambda$ . Can we show this directly from the formula for  $P\{X = k\}$ ?
- By definition of expectation

$$E[X] = \sum_{k=0}^{\infty} P\{X = k\} k = \sum_{k=0}^{\infty} k \frac{\lambda^k}{k!} e^{-\lambda} = \sum_{k=1}^{\infty} \frac{\lambda^k}{(k-1)!} e^{-\lambda}.$$

▶ Setting j = k - 1, this is  $\lambda \sum_{j=0}^{\infty} \frac{\lambda^j}{j!} e^{-\lambda} = \lambda$ .

#### **Variance**

- ▶ Given  $P\{X = k\} = \frac{\lambda^k}{k!} e^{-\lambda}$  for integer  $k \ge 0$ , what is Var[X]?
- ▶ Think of X as (roughly) a Bernoulli (n, p) random variable with n very large and  $p = \lambda/n$ .
- ► This suggests  $\operatorname{Var}[X] \approx npq \approx \lambda$  (since  $np \approx \lambda$  and  $q = 1 p \approx 1$ ). Can we show directly that  $\operatorname{Var}[X] = \lambda$ ?
- Compute

$$E[X^{2}] = \sum_{k=0}^{\infty} P\{X = k\} k^{2} = \sum_{k=0}^{\infty} k^{2} \frac{\lambda^{k}}{k!} e^{-\lambda} = \lambda \sum_{k=1}^{\infty} k \frac{\lambda^{k-1}}{(k-1)!} e^{-\lambda}.$$

▶ Setting j = k - 1, this is

$$\lambda\left(\sum_{j=0}^{\infty}(j+1)\frac{\lambda^{j}}{j!}e^{-\lambda}\right)=\lambda E[X+1]=\lambda(\lambda+1).$$

► Then  $Var[X] = E[X^2] - E[X]^2 = \lambda(\lambda + 1) - \lambda^2 = \lambda$ .

# Poisson convergence

- ▶ Idea: if we have lots of independent random events, each with very small probability to occur, and expected number to occur is  $\lambda$ , then total number that occur is roughly Poisson  $\lambda$ .
- ▶ **Theorem:** Let  $X_{n,m}$  be independent  $\{0,1\}$ -valued random variables with  $P(X_{n,m}=1)=p_{n,m}$ . Suppose  $\sum_{m=1}^{n}p_{n,m}\to\lambda$  and  $\max_{1\leq m\leq n}p_{n,m}\to 0$ . Then  $S_n=X_{n,1}+\ldots+X_{n,n}\implies Z$  were Z is  $Poisson(\lambda)$ .
- ▶ **Proof idea:** Just write down the log characteristic functions for Bernoulli and Poisson random variables. Check the conditions of the continuity theorem.

More on random walks and local CLT

Poisson random variable convergence

More on random walks and local CLT

Poisson random variable convergence

# Recall continuity theorem

▶ Strong continuity theorem: If  $\mu_n \implies \mu_\infty$  then  $\phi_n(t) \to \phi_\infty(t)$  for all t. Conversely, if  $\phi_n(t)$  converges to a limit that is continuous at 0, then the associated sequence of distributions  $\mu_n$  is tight and converges weakly to a measure  $\mu$  with characteristic function  $\phi$ .

#### Recall CLT idea

- Let X be a random variable.
- ▶ The **characteristic function** of X is defined by  $\phi(t) = \phi_X(t) := E[e^{itX}].$
- ▶ And if X has an mth moment then  $E[X^m] = i^m \phi_X^{(m)}(0)$ .
- ▶ In particular, if E[X] = 0 and  $E[X^2] = 1$  then  $\phi_X(0) = 1$  and  $\phi_X'(0) = 0$  and  $\phi_X''(0) = -1$ .
- ▶ Write  $L_X := -\log \phi_X$ . Then  $L_X(0) = 0$  and  $L_X'(0) = -\phi_X'(0)/\phi_X(0) = 0$  and  $L_X'' = -(\phi_X''(0)\phi_X(0) \phi_X'(0)^2)/\phi_X(0)^2 = 1$ .
- If  $V_n = n^{-1/2} \sum_{i=1}^n X_i$  where  $X_i$  are i.i.d. with law of X, then  $L_{V_n}(t) = nL_X(n^{-1/2}t)$ .
- When we zoom in on a twice differentiable function near zero (scaling vertically by n and horizontally by  $\sqrt{n}$ ) the picture looks increasingly like a parabola.

#### Stable laws

- ▶ Question? Is it possible for something like a CLT to hold if X has infinite variance? Say we write  $V_n = n^{-a} \sum_{i=1}^n X_i$  for some a. Could the law of these guys converge to something non-Gaussian?
- ▶ What if the  $L_{V_n}$  converge to something else as we increase n, maybe to some other power of |t| instead of  $|t|^2$ ?
- ▶ The the appropriately normalized sum should be converge in law to something with characteristic function  $e^{-|t|^{\alpha}}$  instead of  $e^{-|t|^2}$ .
- ► We already saw that this should work for Cauchy random variables. What's the characteristic function in that case?
- Let's look up stable distributions.

# Infinitely divisible laws

- ▶ Say a random variable *X* is **infinitely divisible**, for each *n*, there is a random variable *Y* such that *X* has the same law as the sum of *n* i.i.d. copies of *Y*.
- What random variables are infinitely divisible?
- ▶ Poisson, Cauchy, normal, stable, etc.
- ▶ Let's look at the characteristic functions of these objects. What about compound Poisson random variables (linear combinations of Poisson random variables)? What are their characteristic functions like?
- More general constructions are possible via Lévy Khintchine representation.

18.175 Lecture 16 20

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.175: Lecture 18

### Poisson random variables

Scott Sheffield

MIT

### Outline

Extend CLT idea to stable random variables

### Outline

Extend CLT idea to stable random variables

## Recall continuity theorem

▶ Strong continuity theorem: If  $\mu_n \implies \mu_\infty$  then  $\phi_n(t) \to \phi_\infty(t)$  for all t. Conversely, if  $\phi_n(t)$  converges to a limit that is continuous at 0, then the associated sequence of distributions  $\mu_n$  is tight and converges weakly to a measure  $\mu$  with characteristic function  $\phi$ .

#### Recall CLT idea

- Let X be a random variable.
- ▶ The **characteristic function** of X is defined by  $\phi(t) = \phi_X(t) := E[e^{itX}].$
- ▶ And if X has an mth moment then  $E[X^m] = i^m \phi_X^{(m)}(0)$ .
- ▶ In particular, if E[X] = 0 and  $E[X^2] = 1$  then  $\phi_X(0) = 1$  and  $\phi_X'(0) = 0$  and  $\phi_X''(0) = -1$ .
- ▶ Write  $L_X := -\log \phi_X$ . Then  $L_X(0) = 0$  and  $L_X'(0) = -\phi_X'(0)/\phi_X(0) = 0$  and  $L_X'' = -(\phi_X''(0)\phi_X(0) \phi_X'(0)^2)/\phi_X(0)^2 = 1$ .
- If  $V_n = n^{-1/2} \sum_{i=1}^n X_i$  where  $X_i$  are i.i.d. with law of X, then  $L_{V_n}(t) = nL_X(n^{-1/2}t)$ .
- When we zoom in on a twice differentiable function near zero (scaling vertically by n and horizontally by  $\sqrt{n}$ ) the picture looks increasingly like a parabola.

18.175 Lecture 18

#### Stable laws

- ▶ Question? Is it possible for something like a CLT to hold if X has infinite variance? Say we write  $V_n = n^{-a} \sum_{i=1}^n X_i$  for some a. Could the law of these guys converge to something non-Gaussian?
- ▶ What if the  $L_{V_n}$  converge to something else as we increase n, maybe to some other power of |t| instead of  $|t|^2$ ?
- ▶ The the appropriately normalized sum should be converge in law to something with characteristic function  $e^{-|t|^{\alpha}}$  instead of  $e^{-|t|^2}$ .
- We already saw that this should work for Cauchy random variables.

#### Stable laws

- ▶ Example: Suppose that  $P(X_1 > x) = P(X_1 < -x) = x^{-\alpha}/2$  for  $0 < \alpha < 2$ . This is a random variable with a "power law tail".
- ▶ Compute  $1 \phi(t) \approx C|t|^{\alpha}$  when |t| is large.
- If  $X_1, X_2, \ldots$  have same law as  $X_1$  then we have  $E \exp(itS_n/n^{1/\alpha}) = \phi(t/n^\alpha)^n = (1 (1 \phi(t/n^{1/\alpha})))$ . As  $n \to \infty$ , this converges pointwise to  $\exp(-C|t|^\alpha)$ .
- ► Conclude by continuity theorems that  $X_n/n^{1/\alpha} \implies Y$  where Y is a random variable with  $\phi_Y(t) = \exp(-C|t|^{\alpha})$
- Let's look up stable distributions. Up to affine transformations, this is just a two-parameter family with characteristic functions  $\exp[-|t|^{\alpha}(1-i\beta \mathrm{sgn}(t)\Phi)]$  where  $\Phi = \tan(\pi\alpha/2)$  where  $\beta \in [-1,1]$  and  $\alpha \in (0,2]$ .

18.175 Lecture 18

#### Stable-Poisson connection

- Let's think some more about this example, where  $P(X_1 > x) = P(X_1 < -x) = x^{-\alpha}/2$  for  $0 < \alpha < 2$  and  $X_1, X_2, \ldots$  are i.i.d.
- ► Now  $P(an^{1/\alpha} < X_1 < bn^{1\alpha} = \frac{1}{2}(a^{-\alpha} b^{-\alpha})n^{-1}$ .
- ▶ So  $\{m \le n : X_m/n^{1/\alpha} \in (a,b)\}$  converges to a Poisson distribution with mean  $(a^{-\alpha} b^{-\alpha})/2$ .
- ▶ More generally  $\{m \le n : X_m/n^{1/\alpha} \in (a,b)\}$  converges in law to Poisson with mean  $\int_A \frac{\alpha}{2|x|^{\alpha+1}} dx < \infty$ .

## Domain of attraction to stable random variable

- More generality: suppose that  $\lim_{x\to\infty} P(X_1>x)/P(|X_1|>x)=\theta\in[0,1]$  and  $P(|X_1|>x)=x^{-\alpha}L(x)$  where L is slowly varying (which means  $\lim_{x\to\infty} L(tx)/L(x)=1$  for all t>0).
- ▶ **Theorem:** Then  $(S_n b_n)/a_n$  converges in law to limiting random variable, for appropriate  $a_n$  and  $b_n$  values.

## Infinitely divisible laws

- ▶ Say a random variable *X* is **infinitely divisible**, for each *n*, there is a random variable *Y* such that *X* has the same law as the sum of *n* i.i.d. copies of *Y*.
- What random variables are infinitely divisible?
- ▶ Poisson, Cauchy, normal, stable, etc.
- ▶ Let's look at the characteristic functions of these objects. What about compound Poisson random variables (linear combinations of Poisson random variables)? What are their characteristic functions like?
- More general constructions are possible via Lévy Khintchine representation.

18.175 Lecture 18

# Higher dimensional limit theorems

- Much of the CLT story generalizes to higher dimensional random variables.
- ► For example, given a random vector (X, Y, Z), we can define  $\phi(a, b, c) = Ee^{i(aX+bY+cZ)}$ .
- This is just a higher dimensional Fourier transform of the density function.
- ► The inversion theorems and continuity theorems that apply here are essentially the same as in the one-dimensional case.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 20 Infinite divisibility and Lévy processes

Scott Sheffield

MIT

Infinite divisibility

Infinite divisibility

### Infinitely divisible laws

- ▶ Say a random variable *X* is **infinitely divisible**, for each *n*, there is a random variable *Y* such that *X* has the same law as the sum of *n* i.i.d. copies of *Y*.
- What random variables are infinitely divisible?
- ▶ Poisson, Cauchy, normal, stable, etc.
- ▶ Let's look at the characteristic functions of these objects. What about compound Poisson random variables (linear combinations of independent Poisson random variables)? What are their characteristic functions like?
- What if have a random variable X and then we choose a Poisson random variable N and add up N independent copies of X.
- More general constructions are possible via Lévy Khintchine representation.

Infinite divisibility

Infinite divisibility

## Higher dimensional limit theorems

- Much of the CLT story generalizes to higher dimensional random variables.
- ► For example, given a random vector (X, Y, Z), we can define  $\phi(a, b, c) = Ee^{i(aX+bY+cZ)}$ .
- This is just a higher dimensional Fourier transform of the density function.
- ► The inversion theorems and continuity theorems that apply here are essentially the same as in the one-dimensional case.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.175: Lecture not yet posted

Scott Sheffield

MIT

MIT OpenCourseWare http://ocw.mit.edu

## 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.175: Lecture not yet posted

Scott Sheffield

MIT

MIT OpenCourseWare http://ocw.mit.edu

## 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 23 Random walks

Scott Sheffield

MIT

Random walks

Stopping times

Random walks

Stopping times

## Exchangeable events

- ▶ Start with measure space  $(S, S, \mu)$ . Let  $\Omega = \{(\omega_1, \omega_2, \ldots) : \omega_i \in S\}$ , let  $\mathcal{F}$  be product  $\sigma$ -algebra and P the product probability measure.
- ▶ Finite permutation of  $\mathbb{N}$  is one-to-one map from  $\mathbb{N}$  to itself that fixes all but finitely many points.
- ▶ Event  $A \in \mathcal{F}$  is permutable if it is invariant under any finite permutation of the  $\omega_i$ .
- ▶ Let  $\mathcal{E}$  be the  $\sigma$ -field of permutable events.
- ► This is related to the tail  $\sigma$ -algebra we introduced earlier in the course. Bigger or smaller?

## Hewitt-Savage 0-1 law

- ▶ If  $X_1, X_2, \ldots$  are i.i.d. and  $A \in \mathcal{A}$  then  $P(A) \in \{0, 1\}$ .
- ▶ Idea of proof: Try to show A is independent of itself, i.e., that  $P(A) = P(A \cap A) = P(A)P(A)$ . Start with measure theoretic fact that we can approximate A by a set  $A_n$  in  $\sigma$ -algebra generated by  $X_1, \ldots X_n$ , so that symmetric difference of A and  $A_n$  has very small probability. Note that  $A_n$  is independent of event  $A'_n$  that  $A_n$  holds when  $X_1, \ldots, X_n$  and  $X_{n_1}, \ldots, X_{2n}$  are swapped. Symmetric difference between A and  $A'_n$  is also small, so A is independent of itself up to this small error. Then make error arbitrarily small.

18.175 Lecture 23

## Application of Hewitt-Savage:

- ▶ If  $X_i$  are i.i.d. in  $\mathbb{R}^n$  then  $S_n = \sum_{i=1}^n X_i$  is a **random walk** on  $\mathbb{R}^n$ .
- ▶ **Theorem:** if  $S_n$  is a random walk on  $\mathbb{R}$  then one of the following occurs with probability one:
  - $\rightharpoonup S_n = 0$  for all n
  - $\rightharpoonup S_n \to \infty$
  - $\rightharpoonup S_n \to -\infty$
  - ▶  $-\infty = \liminf S_n < \limsup S_n = \infty$
- ▶ Idea of proof: Hewitt-Savage implies the lim sup  $S_n$  and lim inf  $S_n$  are almost sure constants in  $[-\infty, \infty]$ . Note that if  $X_1$  is not a.s. constant, then both values would depend on  $X_1$  if they were not in  $\pm \infty$

Random walks

Stopping times

Random walks

Stopping times

## Stopping time definition

- Say that T is a **stopping time** if the event that T = n is in  $\mathcal{F}_n$  for  $i \leq n$ .
- ▶ In finance applications, *T* might be the time one sells a stock. Then this states that the decision to sell at time *n* depends only on prices up to time *n*, not on (as yet unknown) future prices.

## Stopping time examples

- Let  $A_1, \ldots$  be i.i.d. random variables equal to -1 with probability .5 and 1 with probability .5 and let  $X_0 = 0$  and  $X_n = \sum_{i=1}^n A_i$  for  $n \ge 0$ .
- Which of the following is a stopping time?
  - 1. The smallest T for which  $|X_T| = 50$
  - 2. The smallest T for which  $X_T \in \{-10, 100\}$
  - 3. The smallest T for which  $X_T = 0$ .
  - 4. The T at which the  $X_n$  sequence achieves the value 17 for the 9th time.
  - 5. The value of  $T \in \{0, 1, 2, ..., 100\}$  for which  $X_T$  is largest.
  - 6. The largest  $T \in \{0, 1, 2, ..., 100\}$  for which  $X_T = 0$ .
- Answer: first four, not last two.

## Stopping time theorems

- ▶ **Theorem:** Let  $X_1, X_2, ...$  be i.i.d. and N a stopping time with  $N < \infty$ .
- ▶ Conditioned on stopping time  $N < \infty$ , conditional law of  $\{X_{N+n}, n \ge 1\}$  is independent of  $\mathcal{F}_n$  and has same law as original sequence.
- ▶ Wald's equation: Let  $X_i$  be i.i.d. with  $E|X_i| < \infty$ . If N is a stopping time with  $EN < \infty$  then  $ES_N = EX_1EN$ .
- ▶ Wald's second equation: Let  $X_i$  be i.i.d. with  $E|X_i|=0$  and  $EX_i^2=\sigma^2<\infty$ . If N is a stopping time with  $EN<\infty$  then  $ES_N=\sigma^2EN$ .


## Wald applications to SRW

- ▶  $S_0 = a \in \mathbb{Z}$  and at each time step  $S_j$  independently changes by  $\pm 1$  according to a fair coin toss. Fix  $A \in \mathbb{Z}$  and let  $N = \inf\{k : S_k \in \{0, A\}.$  What is  $\mathbb{E}S_N$ ?
- ► What is EN?

Random walks

Stopping times

Random walks

Stopping times

### Reflection principle

- ► How many walks from (0, x) to (n, y) that don't cross the horizontal axis?
- ▶ Try counting walks that *do* cross by giving bijection to walks from (0, -x) to (n, y).

#### **Ballot Theorem**

- ▶ Suppose that in election candidate A gets  $\alpha$  votes and B gets  $\beta < \alpha$  votes. What's probability that A is a head throughout the counting?
- ▶ Answer:  $(\alpha \beta)/(\alpha + \beta)$ . Can be proved using reflection principle.

#### Arcsin theorem

- ► Theorem for last hitting time.
- ▶ Theorem for amount of positive positive time.

# 18.175: Lecture 23 Random walks

Scott Sheffield

MIT

Random walks

Stopping times

Random walks

Stopping times

## Exchangeable events

- ▶ Start with measure space  $(S, S, \mu)$ . Let  $\Omega = \{(\omega_1, \omega_2, \ldots) : \omega_i \in S\}$ , let  $\mathcal{F}$  be product  $\sigma$ -algebra and P the product probability measure.
- ▶ Finite permutation of  $\mathbb{N}$  is one-to-one map from  $\mathbb{N}$  to itself that fixes all but finitely many points.
- ▶ Event  $A \in \mathcal{F}$  is permutable if it is invariant under any finite permutation of the  $\omega_i$ .
- ▶ Let  $\mathcal{E}$  be the  $\sigma$ -field of permutable events.
- ► This is related to the tail  $\sigma$ -algebra we introduced earlier in the course. Bigger or smaller?

## Hewitt-Savage 0-1 law

- ▶ If  $X_1, X_2, \ldots$  are i.i.d. and  $A \in \mathcal{A}$  then  $P(A) \in \{0, 1\}$ .
- ▶ Idea of proof: Try to show A is independent of itself, i.e., that  $P(A) = P(A \cap A) = P(A)P(A)$ . Start with measure theoretic fact that we can approximate A by a set  $A_n$  in  $\sigma$ -algebra generated by  $X_1, \ldots X_n$ , so that symmetric difference of A and  $A_n$  has very small probability. Note that  $A_n$  is independent of event  $A'_n$  that  $A_n$  holds when  $X_1, \ldots, X_n$  and  $X_{n_1}, \ldots, X_{2n}$  are swapped. Symmetric difference between A and  $A'_n$  is also small, so A is independent of itself up to this small error. Then make error arbitrarily small.

18.175 Lecture 23

## Application of Hewitt-Savage:

- ▶ If  $X_i$  are i.i.d. in  $\mathbb{R}^n$  then  $S_n = \sum_{i=1}^n X_i$  is a **random walk** on  $\mathbb{R}^n$ .
- ▶ **Theorem:** if  $S_n$  is a random walk on  $\mathbb{R}$  then one of the following occurs with probability one:
  - $\rightharpoonup S_n = 0$  for all n
  - $\rightharpoonup S_n \to \infty$
  - $\rightharpoonup S_n \to -\infty$
  - ▶  $-\infty = \liminf S_n < \limsup S_n = \infty$
- ▶ Idea of proof: Hewitt-Savage implies the lim sup  $S_n$  and lim inf  $S_n$  are almost sure constants in  $[-\infty, \infty]$ . Note that if  $X_1$  is not a.s. constant, then both values would depend on  $X_1$  if they were not in  $\pm \infty$

Random walks

Stopping times

Random walks

Stopping times

## Stopping time definition

- Say that T is a **stopping time** if the event that T = n is in  $\mathcal{F}_n$  for  $i \leq n$ .
- ▶ In finance applications, *T* might be the time one sells a stock. Then this states that the decision to sell at time *n* depends only on prices up to time *n*, not on (as yet unknown) future prices.

## Stopping time examples

- Let  $A_1, \ldots$  be i.i.d. random variables equal to -1 with probability .5 and 1 with probability .5 and let  $X_0 = 0$  and  $X_n = \sum_{i=1}^n A_i$  for  $n \ge 0$ .
- Which of the following is a stopping time?
  - 1. The smallest T for which  $|X_T| = 50$
  - 2. The smallest T for which  $X_T \in \{-10, 100\}$
  - 3. The smallest T for which  $X_T = 0$ .
  - 4. The T at which the  $X_n$  sequence achieves the value 17 for the 9th time.
  - 5. The value of  $T \in \{0, 1, 2, ..., 100\}$  for which  $X_T$  is largest.
  - 6. The largest  $T \in \{0, 1, 2, ..., 100\}$  for which  $X_T = 0$ .
- Answer: first four, not last two.

## Stopping time theorems

- ▶ **Theorem:** Let  $X_1, X_2, ...$  be i.i.d. and N a stopping time with  $N < \infty$ .
- ▶ Conditioned on stopping time  $N < \infty$ , conditional law of  $\{X_{N+n}, n \ge 1\}$  is independent of  $\mathcal{F}_n$  and has same law as original sequence.
- ▶ Wald's equation: Let  $X_i$  be i.i.d. with  $E|X_i| < \infty$ . If N is a stopping time with  $EN < \infty$  then  $ES_N = EX_1EN$ .
- ▶ Wald's second equation: Let  $X_i$  be i.i.d. with  $E|X_i|=0$  and  $EX_i^2=\sigma^2<\infty$ . If N is a stopping time with  $EN<\infty$  then  $ES_N=\sigma^2EN$ .


## Wald applications to SRW

- ▶  $S_0 = a \in \mathbb{Z}$  and at each time step  $S_j$  independently changes by  $\pm 1$  according to a fair coin toss. Fix  $A \in \mathbb{Z}$  and let  $N = \inf\{k : S_k \in \{0, A\}.$  What is  $\mathbb{E}S_N$ ?
- ► What is EN?

Random walks

Stopping times

Random walks

Stopping times

### Reflection principle

- ► How many walks from (0, x) to (n, y) that don't cross the horizontal axis?
- ▶ Try counting walks that *do* cross by giving bijection to walks from (0, -x) to (n, y).

#### **Ballot Theorem**

- ▶ Suppose that in election candidate A gets  $\alpha$  votes and B gets  $\beta < \alpha$  votes. What's probability that A is a head throughout the counting?
- ▶ Answer:  $(\alpha \beta)/(\alpha + \beta)$ . Can be proved using reflection principle.

#### Arcsin theorem

- ► Theorem for last hitting time.
- ▶ Theorem for amount of positive positive time.

MIT OpenCourseWare http://ocw.mit.edu

18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## 18.175: Lecture not yet posted

Scott Sheffield

MIT

MIT OpenCourseWare http://ocw.mit.edu

## 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 25 Reflections and martingales

Scott Sheffield

MIT

Conditional expectation

Martingales

Conditional expectation

Martingales

# Conditional expectation

- ▶ Say we're given a probability space  $(\Omega, \mathcal{F}_0, P)$  and a  $\sigma$ -field  $\mathcal{F} \subset \mathcal{F}_0$  and a random variable X measurable w.r.t.  $\mathcal{F}_0$ , with  $E|X| < \infty$ . The **conditional expectation of** X **given**  $\mathcal{F}$  is a new random variable, which we can denote by  $Y = E(X|\mathcal{F})$ .
- ▶ We require that Y is  $\mathcal{F}$  measurable and that for all A in  $\mathcal{F}$ , we have  $\int_A XdP = \int_A YdP$ .
- Any Y satisfying these properties is called a version of E(X|F).
- ▶ Is it possible that there exists more than one version of  $E(X|\mathcal{F})$  (which would mean that in some sense the conditional expectation is not canonically defined)?
- ▶ Is there some sense in which  $E(X|\mathcal{F})$  always exists and is always uniquely defined (maybe up to set of measure zero)?

18.175 Lecture 25

# Conditional expectation

- ▶ Claim: Assuming  $Y = E(X|\mathcal{F})$  as above, and  $E|X| < \infty$ , we have  $E|Y| \le E|X|$ . In particular, Y is integrable.
- ▶ **Proof:** let  $A = \{Y > 0\} \in \mathcal{F}$  and observe:  $\int_A Y dP \int_A X dP \le \int_A |X| dP$ . By similarly argument,  $\int_{A^c} -Y dP \le \int_{A^c} |X| dP$ .
- ▶ Uniqueness of Y: Suppose Y' is  $\mathcal{F}$ -measurable and satisfies  $\int_A Y' dP = \int_A X dP = \int_A Y dP$  for all  $A \in \mathcal{F}$ . Then consider the set  $Y Y' \geq \epsilon$ . Integrating over that gives zero. Must hold for any  $\epsilon$ . Conclude that Y = Y' almost everywhere.

18.175 Lecture 25

# Radon-Nikodym theorem

- Let  $\mu$  and  $\nu$  be  $\sigma$ -finite measures on  $(\Omega, \mathcal{F})$ . Say  $\nu << \mu$  (or  $\nu$  is **absolutely continuous w.r.t.**  $\mu$  if  $\mu(A) = 0$  implies  $\nu(A) = 0$ .
- ▶ Recall **Radon-Nikodym theorem:** If  $\mu$  and  $\nu$  are  $\sigma$ -finite measures on  $(\Omega, \mathcal{F})$  and  $\nu$  is absolutely continuous w.r.t.  $\mu$ , then there exists a measurable  $f: \Omega \to [0, \infty)$  such that  $\nu(A) = \int_A f d\mu$ .
- Observe: this theorem implies existence of conditional expectation.

Conditional expectation

Martingales

Conditional expectation

Martingales

# Two big results

- Optional stopping theorem: Can't make money in expectation by timing sale of asset whose price is non-negative martingale.
- ► Martingale convergence: A non-negative martingale almost surely has a limit.

#### Wald

- ▶ Wald's equation: Let  $X_i$  be i.i.d. with  $E|X_i| < \infty$ . If N is a stopping time with  $EN < \infty$  then  $ES_N = EX_1EN$ .
- ▶ Wald's second equation: Let  $X_i$  be i.i.d. with  $E|X_i|=0$  and  $EX_i^2=\sigma^2<\infty$ . If N is a stopping time with  $EN<\infty$  then  $ES_N=\sigma^2EN$ .

18.175 Lecture 25

# Wald applications to SRW

- ▶  $S_0 = a \in \mathbb{Z}$  and at each time step  $S_j$  independently changes by  $\pm 1$  according to a fair coin toss. Fix  $A \in \mathbb{Z}$  and let  $N = \inf\{k : S_k \in \{0, A\}.$  What is  $\mathbb{E}S_N$ ?
- ► What is EN?

Conditional expectation

Martingales

Conditional expectation

Martingales

# Reflection principle

- ► How many walks from (0, x) to (n, y) that don't cross the horizontal axis?
- ▶ Try counting walks that *do* cross by giving bijection to walks from (0, -x) to (n, y).

#### **Ballot Theorem**

- ▶ Suppose that in election candidate A gets  $\alpha$  votes and B gets  $\beta < \alpha$  votes. What's probability that A is ahead throughout the counting?
- ▶ Answer:  $(\alpha \beta)/(\alpha + \beta)$ . Can be proved using reflection principle.

### Arcsin theorem

- ► Theorem for last hitting time.
- ▶ Theorem for amount of positive positive time.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 26 More on martingales

Scott Sheffield

MIT

Conditional expectation

Regular conditional probabilities

Martingales

Conditional expectation

Regular conditional probabilities

Martingales

# Recall: conditional expectation

- ▶ Say we're given a probability space  $(\Omega, \mathcal{F}_0, P)$  and a  $\sigma$ -field  $\mathcal{F} \subset \mathcal{F}_0$  and a random variable X measurable w.r.t.  $\mathcal{F}_0$ , with  $E|X| < \infty$ . The **conditional expectation of** X **given**  $\mathcal{F}$  is a new random variable, which we can denote by  $Y = E(X|\mathcal{F})$ .
- ▶ We require that Y is  $\mathcal{F}$  measurable and that for all A in  $\mathcal{F}$ , we have  $\int_A XdP = \int_A YdP$ .
- Any Y satisfying these properties is called a version of E(X|F).
- ▶ **Theorem:** Up to redefinition on a measure zero set, the random variable  $E(X|\mathcal{F})$  exists and is unique.
- ▶ This follows from Radon-Nikodym theorem.

# Conditional expectation observations

- ▶ Linearity:  $E(aX + Y|\mathcal{F}) = aE(X|\mathcal{F}) + E(Y|\mathcal{F})$ .
- ▶ If  $X \leq Y$  then  $E(E|\mathcal{F}) \leq E(Y|\mathcal{F})$ .
- ▶ If  $X_n \ge 0$  and  $X_n \uparrow X$  with  $EX < \infty$ , then  $E(X_n | \mathcal{F}) \uparrow E(X | \mathcal{F})$  (by dominated convergence).
- ▶ If  $\mathcal{F}_1 \subset \mathcal{F}_2$  then
  - $E(E(X|\mathcal{F}_1)|\mathcal{F}_2) = E(X|\mathcal{F}_1).$
  - $E(E(X|\mathcal{F}_2)|\mathcal{F}_1) = E(X|\mathcal{F}_1).$
- ▶ Second is kind of interesting: says, after I learn  $\mathcal{F}_1$ , my best guess of what my best guess for X will be after learning  $\mathcal{F}_2$  is simply my current best guess for X.
- ▶ Deduce that  $E(X|\mathcal{F}_i)$  is a martingale if  $\mathcal{F}_i$  is an increasing sequence of  $\sigma$ -algebras and  $E(|X|) < \infty$ .

18.175 Lecture 26

Conditional expectation

Regular conditional probabilities

Martingales

Conditional expectation

Regular conditional probabilities

Martingales

# Regular conditional probability

- ▶ Consider probability space  $(\Omega, \mathcal{F}, P)$ , a measurable map  $X: (\Omega, \mathcal{F}) \to (S, \mathcal{S})$  and  $\mathcal{G} \subset \mathcal{F}$  a  $\sigma$ -field. Then  $\mu: \Omega \times \mathcal{S} \to [0,1]$  is a **regular conditional distribution for** X **given**  $\mathcal{G}$  if
  - ▶ For each A,  $\omega \to \mu(\omega, A)$  is a version of  $P(X \in A|\mathcal{G})$ .
  - ▶ For a.e.  $\omega$ ,  $A \to \mu(\omega, A)$  is a probability measure on (S, S).
- ▶ **Theorem:** Regular conditional probabilities exist if (S, S) is nice.

Conditional expectation

Regular conditional probabilities

Martingales

Conditional expectation

Regular conditional probabilities

Martingales

# Martingales

- ▶ Let  $\mathcal{F}_n$  be increasing sequence of  $\sigma$ -fields (called a **filtration**).
- ▶ A sequence  $X_n$  is **adapted** to  $\mathcal{F}_n$  if  $X_n \in \mathcal{F}_n$  for all n. If  $X_n$  is an adapted sequence (with  $E|X_n| < \infty$ ) then it is called a **martingale** if

$$E(X_{n+1}|\mathcal{F}_n)=X_n$$

for all n. It's a supermartingale (resp., submartingale) if same thing holds with = replaced by  $\le$  (resp.,  $\ge$ ).

# Martingale observations

- ▶ **Claim:** If  $X_n$  is a supermartingale then for n > m we have  $E(X_n | \mathcal{F}_m) \leq X_m$ .
- ▶ **Proof idea:** Follows if n = m + 1 by definition; take n = m + k and use induction on k.
- ▶ Similar result holds for submartingales. Also, if  $X_n$  is a martingale and n > m then  $E(X_n | \mathcal{F}_m) = X_m$ .
- ▶ **Claim:** if  $X_n$  is a martingale w.r.t.  $\mathcal{F}_n$  and  $\phi$  is convex with  $E|\phi(X_n)| < \infty$  then  $\phi(X_n)$  is a submartingale.
- Proof idea: Immediate from Jensen's inequality and martingale definition.
- ▶ Example: take  $\phi(x) = \max\{x, 0\}$ .

18.175 Lecture 26

# Predictable sequence

- ▶ Call  $H_n$  **predictable** if each H + n is  $\mathcal{F}_{n-1}$  measurable.
- ▶ Maybe  $H_n$  represents amount of shares of asset investor has at nth stage.
- ▶ Write  $(H \cdot X)_n = \sum_{m=1}^n H_m(X_m X_{m-1})$ .
- ▶ **Observe:** If  $X_n$  is a supermartingale and the  $H_n \ge 0$  are bounded, then  $(H \cdot X)_n$  is a supermartingale.
- ▶ Example: take  $H_n = 1_{N \ge n}$  for stopping time N.

# Two big results

- ▶ **Optional stopping theorem:** Can't make money in expectation by timing sale of asset whose price is non-negative martingale.
- **Proof:** Just a special case of statement about  $(H \cdot X)$ .
- ► Martingale convergence: A non-negative martingale almost surely has a limit.
- ▶ Idea of proof: Count upcrossings (times martingale crosses a fixed interval) and devise gambling strategy that makes lots of money if the number of these is not a.s. finite.

#### **Problems**

- How many primary candidates ever get above twenty percent in expected probability of victory? (Asked by Aldous.)
- Compute probability of having conditional probability reach a before b

#### Wald

- ▶ Wald's equation: Let  $X_i$  be i.i.d. with  $E|X_i| < \infty$ . If N is a stopping time with  $EN < \infty$  then  $ES_N = EX_1EN$ .
- ▶ Wald's second equation: Let  $X_i$  be i.i.d. with  $E|X_i|=0$  and  $EX_i^2=\sigma^2<\infty$ . If N is a stopping time with  $EN<\infty$  then  $ES_N=\sigma^2EN$ .

18.175 Lecture 26

# Wald applications to SRW

- ▶  $S_0 = a \in \mathbb{Z}$  and at each time step  $S_j$  independently changes by  $\pm 1$  according to a fair coin toss. Fix  $A \in \mathbb{Z}$  and let  $N = \inf\{k : S_k \in \{0, A\}.$  What is  $\mathbb{E}S_N$ ?
- ► What is EN?

Conditional expectation

Regular conditional probabilities

Martingales

Conditional expectation

Regular conditional probabilities

Martingales

# Reflection principle

- ► How many walks from (0, x) to (n, y) that don't cross the horizontal axis?
- ► Try counting walks that *do* cross by giving bijection to walks from (0, -x) to (n, y).

#### **Ballot Theorem**

- ▶ Suppose that in election candidate A gets  $\alpha$  votes and B gets  $\beta < \alpha$  votes. What's probability that A is ahead throughout the counting?
- ▶ Answer:  $(\alpha \beta)/(\alpha + \beta)$ . Can be proved using reflection principle.

#### Arcsin theorem

- ► Theorem for last hitting time.
- ▶ Theorem for amount of positive positive time.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 27 More on martingales

Scott Sheffield

MIT

Conditional expectation

Martingales

Conditional expectation

Martingales

# Recall: conditional expectation

- ▶ Say we're given a probability space  $(\Omega, \mathcal{F}_0, P)$  and a  $\sigma$ -field  $\mathcal{F} \subset \mathcal{F}_0$  and a random variable X measurable w.r.t.  $\mathcal{F}_0$ , with  $E|X| < \infty$ . The **conditional expectation of** X **given**  $\mathcal{F}$  is a new random variable, which we can denote by  $Y = E(X|\mathcal{F})$ .
- ▶ We require that Y is  $\mathcal{F}$  measurable and that for all A in  $\mathcal{F}$ , we have  $\int_A XdP = \int_A YdP$ .
- Any Y satisfying these properties is called a version of E(X|F).
- ▶ **Theorem:** Up to redefinition on a measure zero set, the random variable  $E(X|\mathcal{F})$  exists and is unique.
- ▶ This follows from Radon-Nikodym theorem.

# Conditional expectation observations

- ▶ Linearity:  $E(aX + Y|\mathcal{F}) = aE(X|\mathcal{F}) + E(Y|\mathcal{F})$ .
- ▶ If  $X \le Y$  then  $E(E|\mathcal{F}) \le E(Y|\mathcal{F})$ .
- ▶ If  $X_n \ge 0$  and  $X_n \uparrow X$  with  $EX < \infty$ , then  $E(X_n | \mathcal{F}) \uparrow E(X | \mathcal{F})$  (by dominated convergence).
- ▶ If  $\mathcal{F}_1 \subset \mathcal{F}_2$  then
  - $E(E(X|\mathcal{F}_1)|\mathcal{F}_2) = E(X|\mathcal{F}_1).$
  - $E(E(X|\mathcal{F}_2)|\mathcal{F}_1) = E(X|\mathcal{F}_1).$
- ▶ Second is kind of interesting: says, after I learn  $\mathcal{F}_1$ , my best guess of what my best guess for X will be after learning  $\mathcal{F}_2$  is simply my current best guess for X.
- ▶ Deduce that  $E(X|\mathcal{F}_i)$  is a martingale if  $\mathcal{F}_i$  is an increasing sequence of  $\sigma$ -algebras and  $E(|X|) < \infty$ .

18.175 Lecture 27

Conditional expectation

Martingales

Conditional expectation

Martingales

# Martingales

- ▶ Let  $\mathcal{F}_n$  be increasing sequence of  $\sigma$ -fields (called a **filtration**).
- ▶ A sequence  $X_n$  is **adapted** to  $\mathcal{F}_n$  if  $X_n \in \mathcal{F}_n$  for all n. If  $X_n$  is an adapted sequence (with  $E|X_n| < \infty$ ) then it is called a **martingale** if

$$E(X_{n+1}|\mathcal{F}_n)=X_n$$

for all n. It's a supermartingale (resp., submartingale) if same thing holds with = replaced by  $\le$  (resp.,  $\ge$ ).

# Martingale observations

- ▶ **Claim:** If  $X_n$  is a supermartingale then for n > m we have  $E(X_n | \mathcal{F}_m) \leq X_m$ .
- ▶ **Proof idea:** Follows if n = m + 1 by definition; take n = m + k and use induction on k.
- ▶ Similar result holds for submartingales. Also, if  $X_n$  is a martingale and n > m then  $E(X_n | \mathcal{F}_m) = X_m$ .
- ▶ **Claim:** if  $X_n$  is a martingale w.r.t.  $\mathcal{F}_n$  and  $\phi$  is convex with  $E|\phi(X_n)| < \infty$  then  $\phi(X_n)$  is a submartingale.
- Proof idea: Immediate from Jensen's inequality and martingale definition.
- ▶ Example: take  $\phi(x) = \max\{x, 0\}$ .

# Predictable sequence

- ▶ Call  $H_n$  **predictable** if each H + n is  $\mathcal{F}_{n-1}$  measurable.
- ▶ Maybe  $H_n$  represents amount of shares of asset investor has at nth stage.
- ▶ Write  $(H \cdot X)_n = \sum_{m=1}^n H_m(X_m X_{m-1})$ .
- ▶ **Observe:** If  $X_n$  is a supermartingale and the  $H_n \ge 0$  are bounded, then  $(H \cdot X)_n$  is a supermartingale.
- ▶ Example: take  $H_n = 1_{N \ge n}$  for stopping time N.

# Two big results

- ▶ **Optional stopping theorem:** Can't make money in expectation by timing sale of asset whose price is non-negative martingale.
- ▶ **Proof:** Just a special case of statement about  $(H \cdot X)$  if stopping time is bounded.
- ► Martingale convergence: A non-negative martingale almost surely has a limit.
- ▶ Idea of proof: Count upcrossings (times martingale crosses a fixed interval) and devise gambling strategy that makes lots of money if the number of these is not a.s. finite. Basically, you buy every time price gets below the interval, sell each time it gets above.
- ▶ Stronger convergence statement: If  $X_n$  is a submartingale with sup  $EX_n^+ < \infty$  then as  $n \to \infty$ ,  $X_+ n$  converges a.s. to a limit X with  $E|X| < \infty$ .

18.175 Lecture 27

#### Other statements

- ▶ If  $X_n$  is a supermartingale then as  $n \to \infty$ ,  $X_n \to X$  a.s. and  $EX \le EX_0$ .
- ▶ **Proof:**  $Y_n = -X_n \le 0$  is a submartingale with  $EY^+ = 0$ . Since  $EX_0 \ge EX_n$ , inequality follows from Fatou's lemma.
- ▶ **Doob's decomposition:** Any submartingale  $X_n$  can be written in a unique way as  $X_n = M_n + A_n$  where  $M_n$  is a martingale and  $A_n$  is a predictable increasing sequence with  $A_0 = 0$ .
- ▶ **Proof idea:** Just let  $M_n$  be sum of "surprises" (i.e., the values  $X_n E(X_n | \mathcal{F}_{n-1})$ ).
- ▶ A martingale with bounded increments a.s. either converges to limit or oscillates between  $\pm \infty$ . That is, a.s. either  $\lim X_n < \infty$  exists or  $\lim \sup X_n = +\infty$  and  $\lim \inf X_n = -\infty$ .

18.175 Lecture 27 12

#### **Problems**

- ► How many primary candidates does one expect to ever exceed 20 percent on Intrade? (Asked by Aldous.)
- Compute probability of having a martingale price reach a before b if martingale prices vary continuously.
- ▶ Polya's urn: *r* red and *g* green balls. Repeatedly sample randomly and add extra ball of sampled color. Ratio of red to green is martingale, hence a.s. converges to limit.

#### Wald

- ▶ Wald's equation: Let  $X_i$  be i.i.d. with  $E|X_i| < \infty$ . If N is a stopping time with  $EN < \infty$  then  $ES_N = EX_1EN$ .
- ▶ Wald's second equation: Let  $X_i$  be i.i.d. with  $E|X_i|=0$  and  $EX_i^2=\sigma^2<\infty$ . If N is a stopping time with  $EN<\infty$  then  $ES_N=\sigma^2EN$ .

18.175 Lecture 27

# Wald applications to SRW

- ▶  $S_0 = a \in \mathbb{Z}$  and at each time step  $S_j$  independently changes by  $\pm 1$  according to a fair coin toss. Fix  $A \in \mathbb{Z}$  and let  $N = \inf\{k : S_k \in \{0, A\}.$  What is  $\mathbb{E}S_N$ ?
- ► What is EN?

Conditional expectation

Martingales

Conditional expectation

Martingales

# Reflection principle

- ► How many walks from (0, x) to (n, y) that don't cross the horizontal axis?
- ▶ Try counting walks that *do* cross by giving bijection to walks from (0, -x) to (n, y).

#### **Ballot Theorem**

- ▶ Suppose that in election candidate A gets  $\alpha$  votes and B gets  $\beta < \alpha$  votes. What's probability that A is ahead throughout the counting?
- ▶ Answer:  $(\alpha \beta)/(\alpha + \beta)$ . Can be proved using reflection principle.

#### Arcsin theorem

- ► Theorem for last hitting time.
- ▶ Theorem for amount of positive positive time.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 28 Even more on martingales

Scott Sheffield

MIT

Recollections

Recollections

#### Recall: conditional expectation

- ▶ Say we're given a probability space  $(\Omega, \mathcal{F}_0, P)$  and a  $\sigma$ -field  $\mathcal{F} \subset \mathcal{F}_0$  and a random variable X measurable w.r.t.  $\mathcal{F}_0$ , with  $E|X| < \infty$ . The **conditional expectation of** X **given**  $\mathcal{F}$  is a new random variable, which we can denote by  $Y = E(X|\mathcal{F})$ .
- ▶ We require that Y is  $\mathcal{F}$  measurable and that for all A in  $\mathcal{F}$ , we have  $\int_A XdP = \int_A YdP$ .
- Any Y satisfying these properties is called a version of E(X|F).
- ▶ **Theorem:** Up to redefinition on a measure zero set, the random variable  $E(X|\mathcal{F})$  exists and is unique.
- ▶ This follows from Radon-Nikodym theorem.
- ▶ **Theorem:**  $E(X|\mathcal{F}_i)$  is a martingale if  $\mathcal{F}_i$  is an increasing sequence of  $\sigma$ -algebras and  $E(|X|) < \infty$ .

# Martingales

- ▶ Let  $\mathcal{F}_n$  be increasing sequence of  $\sigma$ -fields (called a **filtration**).
- ▶ A sequence  $X_n$  is **adapted** to  $\mathcal{F}_n$  if  $X_n \in \mathcal{F}_n$  for all n. If  $X_n$  is an adapted sequence (with  $E|X_n| < \infty$ ) then it is called a **martingale** if

$$E(X_{n+1}|\mathcal{F}_n)=X_n$$

for all n. It's a supermartingale (resp., submartingale) if same thing holds with = replaced by  $\le$  (resp.,  $\ge$ ).

#### Two big results

- ▶ Optional stopping theorem: Can't make money in expectation by timing sale of asset whose price is non-negative martingale.
- ▶ **Proof:** Just a special case of statement about  $(H \cdot X)$  if stopping time is bounded.
- ► Martingale convergence: A non-negative martingale almost surely has a limit.
- ▶ Idea of proof: Count upcrossings (times martingale crosses a fixed interval) and devise gambling strategy that makes lots of money if the number of these is not a.s. finite. Basically, you buy every time price gets below the interval, sell each time it gets above.

#### **Problems**

- ▶ Assume Intrade prices are continuous martingales. (Forget about bid-ask spreads, possible longshot bias, this year's bizarre arbitrage opportunities, discontinuities brought about by sudden spurts of information, etc.)
- How many primary candidates does one expect to ever exceed 20 percent on Intrade primary nomination market? (Asked by Aldous.)
- Compute probability of having a martingale price reach a before b if martingale prices vary continuously.
- ▶ Polya's urn: *r* red and *g* green balls. Repeatedly sample randomly and add extra ball of sampled color. Ratio of red to green is martingale, hence a.s. converges to limit.

Recollections

Recollections

## *L*<sup>p</sup> convergence theorem

- ▶ **Theorem:** If  $X_n$  is a martingale with sup  $E|X_n|^p < \infty$  where p > 1 then  $X_n \to X$  a.s. and in  $L^p$ .
- ▶ **Proof idea:** Have  $(EX_n^+)^p \le (E|X_n|)^p \le E|X_n|^p$  for martingale convergence theorem  $X_n \to X$  a.s. Use  $L^p$  maximal inequality to get  $L^p$  convergence.

## Orthogonality of martingale increments

- ▶ **Theorem:** Let  $X_n$  be a martingale with  $EX_n^2 < \infty$  for all n. If  $m \le n$  and  $Y \in \mathcal{F}_m$  with  $EY^2 < \infty$ , then  $E((X_n X_m)Y) = 0$ .
- ▶ Proof idea:  $E((X_n X_m)Y) = E[E((X_n X_m)Y|\mathcal{F}_m)] = E[YE((X_n X_m)|\mathcal{F}_m)] = 0$
- ▶ Conditional variance theorem: If  $X_n$  is a martingale with  $EX_n^2 < \infty$  for all n then  $E((X_n X_m)^2 | \mathcal{F}_m) = E(X_n^2 | \mathcal{F}_m) X_m^2$ .

## Square integrable martingales

- ▶ Suppose we have a martingale  $X_n$  with  $EX_n^2 < \infty$  for all n.
- We know  $X_n^2$  is a submartingale. By Doob's decomposition, an write  $X_n^2 = M_n + A_n$  where  $M_n$  is a martingale, and

$$A_n = \sum_{m=1}^n E(X_m^2 | \mathcal{F}_{m-1}) - X_{m-1}^2 = \sum_{m=1}^n E((X_m - X_{m-1})^2 | \mathcal{F}_{m-1}).$$

- $\rightharpoonup A_n$  in some sense measures total accumulated variance by time n.
- ▶ Theorem:  $E(\sup_m |X_m|^2) \le 4EA_{\infty}$
- ▶ **Proof idea:**  $L^2$  maximal equality gives  $E(\sup_{0 \le m \le n} |X_m|^2) \le 4EX_n^2 = 4EA_n$ . Use monotone convergence.

#### Square integrable martingales

- ▶ Suppose we have a martingale  $X_n$  with  $EX_n^2 < \infty$  for all n.
- ▶ **Theorem:**  $\lim_{n\to\infty} X_n$  exists and is finite a.s. on  $\{A_\infty < \infty\}$ .
- ▶ **Proof idea:** Try fixing *a* and truncating at time  $N = \inf\{n : A_{n+1} > a^2\}$ , use  $L^2$  convergence theorem.

# Uniform integrability

▶ Say  $X_i$ ,  $i \in I$ , are uniform integrable if

$$\lim_{M\to\infty} \left(\sup_{i\in I} E(|X_i|;|X_i|>M)\right)=0.$$

- ▶ Example: Given  $(\Omega, \mathcal{F}_0, P)$  and  $X \in L^1$ , then a uniformly integral family is given by  $\{E(X|\mathcal{F})\}$  (where  $\mathcal{F}$  ranges over all  $\sigma$ -algebras contained in  $\mathcal{F}_0$ ).
- ▶ **Theorem:** If  $X_n \to X$  in probability then the following are equivalent:
  - $\rightharpoonup X_n$  are uniformly integrable
  - $\rightharpoonup X_n \to X$  in  $L^1$
  - $E|X_n| \to E|X| < \infty$

## Submartingale convergence

- ► Following are equivalent for a submartingale:
  - ► It's uniformly integrable.
  - ▶ It converges a.s. and in  $L^1$ .
  - ▶ It converges in  $L^1$ .

#### Backwards martingales

- ▶ Suppose  $E(X_{n+1}|\mathcal{F}_n) = X$  with  $n \le 0$  (and  $\mathcal{F}_n$  increasing as n increases).
- ▶ **Theorem:**  $X_{-\infty} = \lim_{n \to -\infty} X_n$  exists a.s. and in  $L^1$ .
- ▶ **Proof idea:** Use upcrosing inequality to show expected number of upcrossings of any interval is finite. Since  $X_n = E(X_0|\mathcal{F}_n)$  the  $X_n$  are uniformly integrable, and we can deduce convergence in  $L^1$ .

#### General optional stopping theorem

- ▶ Let  $X_n$  be a uniformly integrable submartingale.
- ▶ **Theorem:** For any stopping time N,  $X_{N \wedge n}$  is uniformly integrable.
- ▶ **Theorem:** If  $E|X_n| < \infty$  and  $X_n 1_{(N>n)}$  is uniformly integrable, then  $X_{N \wedge n}$  is uniformly integrable.
- ▶ **Theorem:** For any stopping time  $N \le \infty$ , we have  $EX_0 \le EX_N \le EX_\infty$  where  $X_\infty = \lim X_n$ .
- ▶ Fairly general form of optional stopping theorem: If  $L \leq M$  are stopping times and  $Y_{M \wedge n}$  is a uniformly integrable submartingale, then  $EY_L \leq EY_M$  and  $Y_L \leq E(Y_M | \mathcal{F}_L)$ .

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 29 Still more martingales

Scott Sheffield

MIT

#### Martingales

- ▶ Let  $\mathcal{F}_n$  be increasing sequence of  $\sigma$ -fields (called a **filtration**).
- ▶ A sequence  $X_n$  is **adapted** to  $\mathcal{F}_n$  if  $X_n \in \mathcal{F}_n$  for all n. If  $X_n$  is an adapted sequence (with  $E|X_n| < \infty$ ) then it is called a **martingale** if

$$E(X_{n+1}|\mathcal{F}_n)=X_n$$

for all n. It's a **supermartingale** (resp., **submartingale**) if same thing holds with = replaced by  $\le$  (resp.,  $\ge$ ).

- ▶ **Theorem:**  $E(X|\mathcal{F}_i)$  is a martingale if  $\mathcal{F}_i$  is an increasing sequence of  $\sigma$ -algebras and  $E(|X|) < \infty$ .
- ▶ Optional stopping theorem: Under some conditions (what conditions?) the expectation of martingale at a stopping time is just the initial value of martingale.
- ► Martingale convergence: A non-negative martingale almost surely has a limit. Under some conditions (what conditions?) the expectation of the limit is the initial value of the martingale.

#### **Problems**

- ➤ Classic brainteaser: 52 cards (half red, half black) shuffled and face down. I turn them over one at a time. At some point (before last card is turned over) you say "stop". If subsequent card is red, you get one dollar. You do you time your stop to maximize your probability of winning?
- ▶ Classic observation: if  $r_n$  denotes fraction of face-down cards that are red after n have been turned over, then  $r_n$  is a martingale.
- ▶ Optional stopping theorem implies that it doesn't matter when you say stop. All strategies yield same expected payoff.
- Odds of winning are same for monkey and genius.
- Unless you cheat.
- ► Classic question: Is this also true of the stock market?

## Martingales as real-time subjective probability updates

- Ivan sees email from girlfriend with subject "some possibly serious news", thinks there's a 20 percent chance she'll dump him by email's end. Revises number after each line:
- ▶ Oh Ivan, I've missed you so much! 12
- But there's something I have to tell you 23
- and please don't take this the wrong way. 29
- ▶ I've been spending lots of time with a guy named Robert, 47
- a visiting database consultant on my project 34
- who seems very impressed by my work 23
- and wants me to join his startup in Palo Alto. 38
- ► Said I'd absolutely have to talk to you first, 19
- that you are my first priority in life. 7
- ▶ But I'm just so confused on so many levels. 15
- ▶ Please call me! I love you so much! Alice 0

### Continuous martingales

- Cassandra is a rational person. She subjective probability estimates in real time so fast that they can be viewed as continuous martingales.
- ▶ She uses the phrase "I think X" in a precise way: it means that P(X) > 1/2.
- Cassandra thinks she will win her tennis match today. However, she thinks that she will at some point think she won't win. She does not think that she will ever think that she won't at some point think she will win.
- ▶ What's the probability that Cassandra will win? (Give the full range of possibilities.)

#### Theorems

- ▶  $L^p$  convergence theorem: If  $X_n$  is martingale with  $\sup E|X_n|^p < \infty$  where p > 1 then  $X_n \to X$  a.s. and in  $L^p$ .
- ▶ Orthogonal increment theorem: Let  $X_n$  be a martingale with  $EX_n^2 < \infty$  for all n. If  $m \le n$  and  $Y \in \mathcal{F}_m$  with  $EY^2 < \infty$ , then  $E((X_n X_m)Y) = 0$ .
- ▶ Cond. variance theorem: If  $X_n$  is martingale,  $EX_n^2 < \infty$  for all n, then  $E((X_n X_m)^2 | \mathcal{F}_m) = E(X_n^2 | \mathcal{F}_m) X_m^2$ .
- ▶ "Accumulated variance" theorems: Consider martingale  $X_n$  with  $EX_n^2 < \infty$  for all n. By Doob, can write  $X_n^2 = M_n + A_n$  where  $M_n$  is a martingale, and

$$A_n = \sum_{m=1}^n E(X_m^2 | \mathcal{F}_{m-1}) - X_{m-1}^2 = \sum_{m=1}^n E((X_m - X_{m-1})^2 | \mathcal{F}_{m-1}).$$

Then  $E(\sup_m |X_m|^2) \le 4EA_{\infty}$ . And  $\lim_{n\to\infty} X_n$  exists and is finite a.s. on  $\{A_{\infty} < \infty\}$ .

## Uniform integrability

▶ Say  $X_i$ ,  $i \in I$ , are uniform integrable if

$$\lim_{M\to\infty} \left(\sup_{i\in I} E(|X_i|;|X_i|>M)\right) = 0.$$

- ▶ Example: Given  $(\Omega, \mathcal{F}_0, P)$  and  $X \in L^1$ , then a uniformly integral family is given by  $\{E(X|\mathcal{F})\}$  (where  $\mathcal{F}$  ranges over all  $\sigma$ -algebras contained in  $\mathcal{F}_0$ ).
- ▶ **Theorem:** If  $X_n \to X$  in probability then the following are equivalent:
  - $\triangleright$   $X_n$  are uniformly integrable
  - $X_n \to X$  in  $L^1$
  - $E|X_n| \to E|X| < \infty$
- ▶ **Proof idea:** They all amount to controlling "contribution to expectation from values near infinity".

#### Submartingale convergence

- ▶ **Submartingale convergence theorem:** The following are equivalent for a submartingale:
  - It's uniformly integrable.
  - ▶ It converges a.s. and in  $L^1$ .
  - ▶ It converges in  $L^1$ .
- ▶ **Proof idea:** First implies second: uniform integrability implies  $\sup E|X_n|<\infty$ , martingale convergence then implies  $X_n\to X$  a.s., and previous result implies  $X_n\to X$  in probability. Easier to see second implies third, third implies first.

### Martingale convergence

- ► Martingale convergence theorem: The following are equivalent for a martingale:
  - ► It's uniformly integrable.
  - ▶ It converges a.s. and in  $L^1$ .
  - ▶ It converges in L¹.
  - ▶ There is an integrable random variable X so that  $X_n = E(X|\mathcal{F}_n)$ .
  - In other words, every uniformly integrable martingale can be interpreted as a "revised expectation given latest information" sequence.

#### Backwards martingales

- ▶ Suppose  $E(X_{n+1}|\mathcal{F}_n) = X$  with  $n \le 0$  (and  $\mathcal{F}_n$  increasing as n increases).
- ▶ Kind of like conditional expectation given less and less an information (as  $n \to -\infty$ )
- ▶ **Theorem:**  $X_{-\infty} = \lim_{n \to -\infty} X_n$  exists a.s. and in  $L^1$ .
- ▶ **Proof idea:** Use upcrosing inequality to show expected number of upcrossings of any interval is finite. Since  $X_n = E(X_0|\mathcal{F}_n)$  the  $X_n$  are uniformly integrable, and we can deduce convergence in  $L^1$ .

#### General optional stopping theorem

- Let  $X_n$  be a uniformly integrable submartingale.
- ▶ **Theorem:** For any stopping time N,  $X_{N \wedge n}$  is uniformly integrable.
- ▶ **Theorem:** If  $E|X_n| < \infty$  and  $X_n 1_{(N>n)}$  is uniformly integrable, then  $X_{N \wedge n}$  is uniformly integrable.
- ▶ **Theorem:** For any stopping time  $N \le \infty$ , we have  $EX_0 \le EX_N \le EX_\infty$  where  $X_\infty = \lim X_n$ .
- ▶ Fairly general form of optional stopping theorem: If  $L \leq M$  are stopping times and  $Y_{M \wedge n}$  is a uniformly integrable submartingale, then  $EY_L \leq EY_M$  and  $Y_L \leq E(Y_M | \mathcal{F}_L)$ .

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 30

## Markov chains

Scott Sheffield

MIT

Review what you know about finite state Markov chains

Finite state ergodicity and stationarity

Review what you know about finite state Markov chains

Finite state ergodicity and stationarity

#### Markov chains

- ▶ Consider a sequence of random variables  $X_0, X_1, X_2, \ldots$  each taking values in the same state space, which for now we take to be a finite set that we label by  $\{0, 1, \ldots, M\}$ .
- ▶ Interpret  $X_n$  as state of the system at time n.
- Sequence is called a **Markov chain** if we have a fixed collection of numbers  $P_{ij}$  (one for each pair  $i, j \in \{0, 1, \dots, M\}$ ) such that whenever the system is in state i, there is probability  $P_{ij}$  that system will next be in state j.
- ▶ Precisely,  $P\{X_{n+1} = j | X_n = i, X_{n-1} = i_{n-1}, \dots, X_1 = i_1, X_0 = i_0\} = P_{ij}.$
- ► Kind of an "almost memoryless" property. Probability distribution for next state depends only on the current state (and not on the rest of the state history).


## Simple example

- ► For example, imagine a simple weather model with two states: rainy and sunny.
- ▶ If it's rainy one day, there's a .5 chance it will be rainy the next day, a .5 chance it will be sunny.
- ▶ If it's sunny one day, there's a .8 chance it will be sunny the next day, a .2 chance it will be rainy.
- ▶ In this climate, sun tends to last longer than rain.
- Given that it is rainy today, how many days to I expect to have to wait to see a sunny day?
- ► Given that it is sunny today, how many days to I expect to have to wait to see a rainy day?
- Over the long haul, what fraction of days are sunny?

## Matrix representation

- ▶ To describe a Markov chain, we need to define  $P_{ij}$  for any  $i, j \in \{0, 1, ..., M\}$ .
- ▶ It is convenient to represent the collection of transition probabilities P<sub>ij</sub> as a matrix:

$$A = \begin{pmatrix} P_{00} & P_{01} & \dots & P_{0M} \\ P_{10} & P_{11} & \dots & P_{1M} \\ \vdots & & & & \\ \vdots & & & & \\ P_{M0} & P_{M1} & \dots & P_{MM} \end{pmatrix}$$

▶ For this to make sense, we require  $P_{ij} \ge 0$  for all i, j and  $\sum_{i=0}^{M} P_{ij} = 1$  for each i. That is, the rows sum to one.


#### Transitions via matrices

- Suppose that p<sub>i</sub> is the probability that system is in state i at time zero.
- What does the following product represent?

$$\left(\begin{array}{ccccc} p_{0} & p_{1} & \dots & p_{M} \end{array}\right) \left(\begin{array}{ccccc} P_{00} & P_{01} & \dots & P_{0M} \\ P_{10} & P_{11} & \dots & P_{1M} \\ \vdots & & & & \\ P_{M0} & P_{M1} & \dots & P_{MM} \end{array}\right)$$

- Answer: the probability distribution at time one.
- ► How about the following product?

$$(p_0 p_1 \dots p_M) A^n$$

Answer: the probability distribution at time *n*.

#### Powers of transition matrix

- We write  $P_{ij}^{(n)}$  for the probability to go from state i to state j over n steps.
- ► From the matrix point of view

$$\begin{pmatrix} P_{00}^{(n)} & P_{01}^{(n)} & \dots & P_{0M}^{(n)} \\ P_{10}^{(n)} & P_{11}^{(n)} & \dots & P_{1M}^{(n)} \\ \vdots & & & & & \\ \vdots & & & & & \\ P_{M0}^{(n)} & P_{M1}^{(n)} & \dots & P_{MM}^{(n)} \end{pmatrix} = \begin{pmatrix} P_{00} & P_{01} & \dots & P_{0M} \\ P_{10} & P_{11} & \dots & P_{1M} \\ \vdots & & & & & \\ \vdots & & & & & \\ P_{M0} & P_{M1} & \dots & P_{MM} \end{pmatrix}^{n}$$

▶ If A is the one-step transition matrix, then  $A^n$  is the n-step transition matrix.


## Questions

- ▶ What does it mean if all of the rows are identical?
- ▶ Answer: state sequence  $X_i$  consists of i.i.d. random variables.
- What if matrix is the identity?
- Answer: states never change.
- ▶ What if each  $P_{ii}$  is either one or zero?
- Answer: state evolution is deterministic.

## Simple example

- ➤ Consider the simple weather example: If it's rainy one day, there's a .5 chance it will be rainy the next day, a .5 chance it will be sunny. If it's sunny one day, there's a .8 chance it will be sunny the next day, a .2 chance it will be rainy.
- Let rainy be state zero, sunny state one, and write the transition matrix by

$$A = \left(\begin{array}{cc} .5 & .5 \\ .2 & .8 \end{array}\right)$$

Note that

$$A^2 = \begin{pmatrix} .64 & .35 \\ .26 & .74 \end{pmatrix}$$

► Can compute  $A^{10} = \begin{pmatrix} .285719 & .714281 \\ .285713 & .714287 \end{pmatrix}$ 

# Does relationship status have the Markov property?

- Can we assign a probability to each arrow?
- Markov model implies time spent in any state (e.g., a marriage) before leaving is a geometric random variable.
- Not true... Can we make a better model with more states?

Review what you know about finite state Markov chains

Finite state ergodicity and stationarity

Review what you know about finite state Markov chains

Finite state ergodicity and stationarity

# Ergodic Markov chains

- ► Say Markov chain is **ergodic** if some power of the transition matrix has all non-zero entries.
- ► Turns out that if chain has this property, then  $\pi_j := \lim_{n \to \infty} P_{ij}^{(n)}$  exists and the  $\pi_j$  are the unique non-negative solutions of  $\pi_j = \sum_{k=0}^M \pi_k P_{kj}$  that sum to one.
- This means that the row vector

$$\pi = ( \pi_0 \quad \pi_1 \quad \dots \quad \pi_M )$$

is a left eigenvector of A with eigenvalue 1, i.e.,  $\pi A = \pi$ .

- We call  $\pi$  the *stationary distribution* of the Markov chain.
- One can solve the system of linear equations  $\pi_j = \sum_{k=0}^M \pi_k P_{kj}$  to compute the values  $\pi_j$ . Equivalent to considering A fixed and solving  $\pi A = \pi$ . Or solving  $(A-I)\pi = 0$ . This determines  $\pi$  up to a multiplicative constant, and fact that  $\sum \pi_j = 1$  determines the constant.

## Simple example

► If  $A = \begin{pmatrix} .5 & .5 \\ .2 & .8 \end{pmatrix}$ , then we know

$$\pi A = \begin{pmatrix} \pi_0 & \pi_1 \end{pmatrix} \begin{pmatrix} .5 & .5 \\ .2 & .8 \end{pmatrix} = \begin{pmatrix} \pi_0 & \pi_1 \end{pmatrix} = \pi.$$

- ▶ This means that  $.5\pi_0 + .2\pi_1 = \pi_0$  and  $.5\pi_0 + .8\pi_1 = \pi_1$  and we also know that  $\pi_1 + \pi_2 = 1$ . Solving these equations gives  $\pi_0 = 2/7$  and  $\pi_1 = 5/7$ , so  $\pi = \left( \ 2/7 \ \ 5/7 \ \right)$ .
- ► Indeed,

$$\pi A = \begin{pmatrix} 2/7 & 5/7 \end{pmatrix} \begin{pmatrix} .5 & .5 \\ .2 & .8 \end{pmatrix} = \begin{pmatrix} 2/7 & 5/7 \end{pmatrix} = \pi.$$

Recall that  $A^{10} = \begin{pmatrix} .285719 & .714281 \\ .285713 & .714287 \end{pmatrix} \approx \begin{pmatrix} 2/7 & 5/7 \\ 2/7 & 5/7 \end{pmatrix} = \begin{pmatrix} \pi \\ \pi \end{pmatrix}$ 


Review what you know about finite state Markov chains

Finite state ergodicity and stationarity

Review what you know about finite state Markov chains

Finite state ergodicity and stationarity

# Markov chains: general definition

- ▶ Consider a measurable space (S, S).
- ▶ A function  $p: S \times S \rightarrow \mathbb{R}$  is a **transition probability** if
  - ▶ For each  $x \in S$ ,  $A \rightarrow p(x, A)$  is a probability measure on S, S).
  - ▶ For each  $A \in S$ , the map  $x \to p(x, A)$  is a measurable function.
- Say that  $X_n$  is a **Markov chain** w.r.t.  $\mathcal{F}_n$  with transition probability p if  $P(X_{n+1} \in B | \mathcal{F}_n) = p(X_n, B)$ .
- ▶ How do we construct an infinite Markov chain? Choose p and initial distribution  $\mu$  on (S, S). For each  $n < \infty$  write

$$P(X_j \in B_j, 0 \le j \le n) = \int_{B_0} \mu(dx_0) \int_{B_1} p(x_0, dx_1) \cdots$$

$$\int_{B_n} p(x_{n-1}, dx_n).$$

Extend to  $n = \infty$  by Kolmogorov's extension theorem.

#### Markov chains

- ▶ **Definition, again:** Say  $X_n$  is a **Markov chain** w.r.t.  $\mathcal{F}_n$  with transition probability p if  $P(X_{n+1} \in B | \mathcal{F}_n) = p(X_n, B)$ .
- ▶ Construction, again: Fix initial distribution  $\mu$  on (S, S). For each  $n < \infty$  write

$$P(X_j \in B_j, 0 \le j \le n) = \int_{B_0} \mu(dx_0) \int_{B_1} p(x_0, dx_1) \cdots$$

$$\int_{B_n} p(x_{n-1}, dx_n).$$

Extend to  $n = \infty$  by Kolmogorov's extension theorem.

- ▶ **Notation:** Extension produces probability measure  $P_{\mu}$  on sequence space  $(S^{0,1,\dots},S^{0,1,\dots})$ .
- ▶ **Theorem:**  $(X_0, X_1,...)$  chosen from  $P_\mu$  is Markov chain.
- ▶ **Theorem:** If  $X_n$  is any Markov chain with initial distribution  $\mu$  and transition p, then finite dim. probabilities are as above.

## Examples

- ▶ Random walks on  $\mathbb{R}^d$ .
- ▶ Branching processes:  $p(i,j) = P(\sum_{m=1}^{i} \xi_m = j)$  where  $\xi_i$  are i.i.d. non-negative integer-valued random variables.
- ▶ Renewal chain.
- Card shuffling.
- Ehrenfest chain.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 31 More Markov chains

Scott Sheffield

MIT

Recollections

General setup and basic properties

Recollections

General setup and basic properties

#### Markov chains

- ▶ Consider a sequence of random variables  $X_0, X_1, X_2, ...$  each taking values in the same state space, which for now we take to be a finite set that we label by  $\{0, 1, ..., M\}$ .
- ▶ Interpret  $X_n$  as state of the system at time n.
- Sequence is called a **Markov chain** if we have a fixed collection of numbers  $P_{ij}$  (one for each pair  $i, j \in \{0, 1, \dots, M\}$ ) such that whenever the system is in state i, there is probability  $P_{ij}$  that system will next be in state j.
- ▶ Precisely,  $P\{X_{n+1} = j | X_n = i, X_{n-1} = i_{n-1}, \dots, X_1 = i_1, X_0 = i_0\} = P_{ij}.$
- ► Kind of an "almost memoryless" property. Probability distribution for next state depends only on the current state (and not on the rest of the state history).

## Matrix representation

- ▶ To describe a Markov chain, we need to define  $P_{ij}$  for any  $i, j \in \{0, 1, ..., M\}$ .
- ▶ It is convenient to represent the collection of transition probabilities P<sub>ij</sub> as a matrix:

$$A = \begin{pmatrix} P_{00} & P_{01} & \dots & P_{0M} \\ P_{10} & P_{11} & \dots & P_{1M} \\ \vdots & & & & \\ \vdots & & & & \\ P_{M0} & P_{M1} & \dots & P_{MM} \end{pmatrix}$$

For this to make sense, we require  $P_{ij} \ge 0$  for all i, j and  $\sum_{i=0}^{M} P_{ij} = 1$  for each i. That is, the rows sum to one.

#### Powers of transition matrix

- We write  $P_{ij}^{(n)}$  for the probability to go from state i to state j over n steps.
- ► From the matrix point of view

$$\begin{pmatrix} P_{00}^{(n)} & P_{01}^{(n)} & \dots & P_{0M}^{(n)} \\ P_{10}^{(n)} & P_{11}^{(n)} & \dots & P_{1M}^{(n)} \\ \vdots & & & & & \\ \vdots & & & & & \\ P_{M0}^{(n)} & P_{M1}^{(n)} & \dots & P_{MM}^{(n)} \end{pmatrix} = \begin{pmatrix} P_{00} & P_{01} & \dots & P_{0M} \\ P_{10} & P_{11} & \dots & P_{1M} \\ \vdots & & & & & \\ \vdots & & & & & \\ P_{M0} & P_{M1} & \dots & P_{MM} \end{pmatrix}^{n}$$

▶ If A is the one-step transition matrix, then  $A^n$  is the n-step transition matrix.

# Ergodic Markov chains

- ► Say Markov chain is **ergodic** if some power of the transition matrix has all non-zero entries.
- ► Turns out that if chain has this property, then  $\pi_j := \lim_{n \to \infty} P_{ij}^{(n)}$  exists and the  $\pi_j$  are the unique non-negative solutions of  $\pi_j = \sum_{k=0}^M \pi_k P_{kj}$  that sum to one.
- This means that the row vector

$$\pi = ( \pi_0 \quad \pi_1 \quad \dots \quad \pi_M )$$

is a left eigenvector of A with eigenvalue 1, i.e.,  $\pi A = \pi$ .

- We call  $\pi$  the *stationary distribution* of the Markov chain.
- One can solve the system of linear equations  $\pi_j = \sum_{k=0}^M \pi_k P_{kj}$  to compute the values  $\pi_j$ . Equivalent to considering A fixed and solving  $\pi A = \pi$ . Or solving  $(A-I)\pi = 0$ . This determines  $\pi$  up to a multiplicative constant, and fact that  $\sum \pi_j = 1$  determines the constant.

18.175 Lecture 31

## **Examples**

- $\triangleright$  Random walks on  $\mathbb{R}^d$ .
- ▶ Branching processes:  $p(i,j) = P(\sum_{m=1}^{i} \xi_m = j)$  where  $\xi_i$  are i.i.d. non-negative integer-valued random variables.
- ► Renewal chain (deterministic unit decreases, random jump when zero hit).
- Card shuffling.
- Ehrenfest chain (n balls in two chambers, randomly pick ball to swap).
- ▶ Birth and death chains (changes by  $\pm 1$ ). Stationarity distribution?
- M/G/1 queues.
- Random walk on a graph. Stationary distribution?
- ▶ Random walk on directed graph (e.g., single directed chain). 8
- Snakes and ladders

Recollections

General setup and basic properties

Recollections

General setup and basic properties

# Markov chains: general definition

- ▶ Consider a measurable space (S, S).
- ▶ A function  $p: S \times S \rightarrow \mathbb{R}$  is a **transition probability** if
  - ▶ For each  $x \in S$ ,  $A \rightarrow p(x, A)$  is a probability measure on S, S).
  - ▶ For each  $A \in S$ , the map  $x \to p(x, A)$  is a measurable function.
- Say that  $X_n$  is a **Markov chain** w.r.t.  $\mathcal{F}_n$  with transition probability p if  $P(X_{n+1} \in B | \mathcal{F}_n) = p(X_n, B)$ .
- ▶ How do we construct an infinite Markov chain? Choose p and initial distribution  $\mu$  on (S, S). For each  $n < \infty$  write

$$P(X_j \in B_j, 0 \le j \le n) = \int_{B_0} \mu(dx_0) \int_{B_1} p(x_0, dx_1) \cdots$$

$$\int_{B_n} p(x_{n-1}, dx_n).$$

Extend to  $n = \infty$  by Kolmogorov's extension theorem.

18.175 Lecture 31

#### Markov chains

- ▶ **Definition, again:** Say  $X_n$  is a **Markov chain** w.r.t.  $\mathcal{F}_n$  with transition probability p if  $P(X_{n+1} \in B | \mathcal{F}_n) = p(X_n, B)$ .
- ▶ Construction, again: Fix initial distribution  $\mu$  on (S, S). For each  $n < \infty$  write

$$P(X_j \in B_j, 0 \le j \le n) = \int_{B_0} \mu(dx_0) \int_{B_1} p(x_0, dx_1) \cdots$$

$$\int_{B_n} p(x_{n-1}, dx_n).$$

Extend to  $n = \infty$  by Kolmogorov's extension theorem.

- ▶ **Notation:** Extension produces probability measure  $P_{\mu}$  on sequence space  $(S^{0,1,\dots}, S^{0,1,\dots})$ .
- ▶ **Theorem:**  $(X_0, X_1,...)$  chosen from  $P_\mu$  is Markov chain.
- ▶ **Theorem:** If  $X_n$  is any Markov chain with initial distribution  $\mu$  and transition p, then finite dim. probabilities are as above.

18.175 Lecture 31

## Markov properties

▶ Markov property: Take  $(\Omega_0, \mathcal{F}) = (S^{\{0,1,\ldots\}}, \mathcal{S}^{\{0,1,\ldots\}})$ , and let  $P_\mu$  be Markov chain measure and  $\theta_n$  the shift operator on  $\Omega_0$  (shifts sequence n units to left, discarding elements shifted off the edge). If  $Y: \Omega_0 \to \mathbb{R}$  is bounded and measurable then

$$E_{\mu}(Y \circ \theta_n | \mathcal{F}_n) = E_{X_n} Y.$$

▶ Strong Markov property: Can replace n with a.s. finite stopping time N and function Y can vary with time. Suppose that for each n,  $Y_n : \Omega_n \to \mathbb{R}$  is measurable and  $|Y_n| \leq M$  for all n. Then

$$E_{\mu}(Y_{N}\circ\theta_{N}|\mathcal{F}_{N})=E_{X_{N}}Y_{N},$$

where RHS means  $E_x Y_n$  evaluated at  $x = X_n$ , n = N.

## **Properties**

▶ Property of infinite opportunities: Suppose X<sub>n</sub> is Markov chain and

$$P(\cup_{m=n+1}^{\infty}\{X_m\in B_m\}|X_n)\geq \delta>0$$

on 
$$\{X_n \in A_n\}$$
. Then  $P(\{X_n \in A_n i.o.\} - \{X_n \in B_n i.o.\}) = 0$ .

- ▶ **Reflection principle:** Symmetric random walks on  $\mathbb{R}$ . Have  $P(\sup_{m\geq n} S_m > a) \leq 2P(S_n > a)$ .
- Proof idea: Reflection picture.

Recollections

General setup and basic properties

Recollections

General setup and basic properties

# Query

- ▶ **Interesting question:** If A is an infinite probability transition matrix on a countable state space, what does the (infinite) matrix  $I + A + A^2 + A^3 + \ldots = (I A)^{-1}$  represent (if the sum converges)?
- ▶ **Question:** Does it describe the expected number of *y* hits when starting at *x*? Is there a similar interpretation for other power series?
- ▶ How about  $e^A$  or  $e^{\lambda A}$ ?
- Related to distribution after a Poisson random number of steps?

#### Recurrence

- Consider probability walk from y ever returns to y.
- ▶ If it's 1, return to *y* infinitely often, else don't. Call *y* a **recurrent state** if we return to *y* infinitely often.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 32 More Markov chains

Scott Sheffield

MIT

General setup and basic properties

General setup and basic properties

# Markov chains: general definition

- ▶ Consider a measurable space (S, S).
- ▶ A function  $p: S \times S \rightarrow \mathbb{R}$  is a **transition probability** if
  - ▶ For each  $x \in S$ ,  $A \rightarrow p(x, A)$  is a probability measure on S, S).
  - ▶ For each  $A \in S$ , the map  $x \to p(x, A)$  is a measurable function.
- Say that  $X_n$  is a **Markov chain** w.r.t.  $\mathcal{F}_n$  with transition probability p if  $P(X_{n+1} \in B | \mathcal{F}_n) = p(X_n, B)$ .
- ▶ How do we construct an infinite Markov chain? Choose p and initial distribution  $\mu$  on (S, S). For each  $n < \infty$  write

$$P(X_j \in B_j, 0 \le j \le n) = \int_{B_0} \mu(dx_0) \int_{B_1} p(x_0, dx_1) \cdots$$

$$\int_{B_n} p(x_{n-1}, dx_n).$$

Extend to  $n = \infty$  by Kolmogorov's extension theorem.

18.175 Lecture 32

#### Markov chains

- ▶ **Definition, again:** Say  $X_n$  is a **Markov chain** w.r.t.  $\mathcal{F}_n$  with transition probability p if  $P(X_{n+1} \in B | \mathcal{F}_n) = p(X_n, B)$ .
- ▶ Construction, again: Fix initial distribution  $\mu$  on (S, S). For each  $n < \infty$  write

$$P(X_j \in B_j, 0 \le j \le n) = \int_{B_0} \mu(dx_0) \int_{B_1} p(x_0, dx_1) \cdots$$

$$\int_{B_n} p(x_{n-1}, dx_n).$$

Extend to  $n = \infty$  by Kolmogorov's extension theorem.

- ▶ **Notation:** Extension produces probability measure  $P_{\mu}$  on sequence space  $(S^{0,1,\dots},S^{0,1,\dots})$ .
- ▶ **Theorem:**  $(X_0, X_1, ...)$  chosen from  $P_\mu$  is Markov chain.
- ▶ **Theorem:** If  $X_n$  is any Markov chain with initial distribution  $\mu$  and transition p, then finite dim. probabilities are as above.

18.175 Lecture 32

# Markov properties

▶ Markov property: Take  $(\Omega_0, \mathcal{F}) = (S^{\{0,1,\ldots\}}, \mathcal{S}^{\{0,1,\ldots\}})$ , and let  $P_\mu$  be Markov chain measure and  $\theta_n$  the shift operator on  $\Omega_0$  (shifts sequence n units to left, discarding elements shifted off the edge). If  $Y: \Omega_0 \to \mathbb{R}$  is bounded and measurable then

$$E_{\mu}(Y \circ \theta_n | \mathcal{F}_n) = E_{X_n} Y.$$

▶ Strong Markov property: Can replace n with a.s. finite stopping time N and function Y can vary with time. Suppose that for each n,  $Y_n : \Omega_n \to \mathbb{R}$  is measurable and  $|Y_n| \leq M$  for all n. Then

$$E_{\mu}(Y_{N}\circ\theta_{N}|\mathcal{F}_{N})=E_{X_{N}}Y_{N},$$

where RHS means  $E_x Y_n$  evaluated at  $x = X_n, n = N$ .

## **Properties**

▶ Property of infinite opportunities: Suppose X<sub>n</sub> is Markov chain and

$$P(\cup_{m=n+1}^{\infty}\{X_m\in B_m\}|X_n)\geq \delta>0$$

on 
$$\{X_n \in A_n\}$$
. Then  $P(\{X_n \in A_n i.o.\} - \{X_n \in B_n i.o.\}) = 0$ .

- ▶ **Reflection principle:** Symmetric random walks on  $\mathbb{R}$ . Have  $P(\sup_{m \ge n} S_m > a) \le 2P(S_n > a)$ .
- Proof idea: Reflection picture.

## Reversibility

- ▶ Measure  $\mu$  called **reversible** if  $\mu(x)p(x,y) = \mu(y)p(y,x)$  for all x,y.
- Reversibility implies stationarity. Implies that amount of mass moving from x to y is same as amount moving from y to x. Net flow of zero along each edge.
- Markov chain called reversible if admits a reversible probability measure.
- Are all random walks on (undirected) graphs reversible?
- What about directed graphs?

# Cycle theorem

- ► **Kolmogorov's cycle theorem:** Suppose *p* is irreducible. Then exists reversible measure if and only if
  - p(x, y) > 0 implies p(y, x) > 0
  - for any loop  $x_0, x_1, \ldots x_n$  with  $\prod_{i=1}^n p(x_i, x_{i-1}) > 0$ , we have

$$\prod_{i=1}^{n} \frac{p(x_{i-1}, x_i)}{p(x_i, x_{i-1})} = 1.$$

Useful idea to have in mind when constructing Markov chains with given reversible distribution, as needed in Monte Carlo Markov Chains (MCMC) applications.

General setup and basic properties

General setup and basic properties

# Query

- ▶ **Interesting question:** If A is an infinite probability transition matrix on a countable state space, what does the (infinite) matrix  $I + A + A^2 + A^3 + \ldots = (I A)^{-1}$  represent (if the sum converges)?
- ▶ **Question:** Does it describe the expected number of *y* hits when starting at *x*? Is there a similar interpretation for other power series?
- ▶ How about  $e^A$  or  $e^{\lambda A}$ ?
- Related to distribution after a Poisson random number of steps?

#### Recurrence

- Consider probability walk from y ever returns to y.
- ▶ If it's 1, return to *y* infinitely often, else don't. Call *y* a **recurrent state** if we return to *y* infinitely often.

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 33 Ergodic theory

Scott Sheffield

MIT

Setup

Birkhoff's ergodic theorem

Setup

Birkhoff's ergodic theorem

## Motivating problem

- ▶ Consider independent bond percolation on  $\mathbb{Z}^2$  with some fixed parameter p > 1/2. Look at some simulations.
- Let  $\Omega$  be the set of maps from the edges of  $\mathbb{Z}^2$  to  $\{0,1\}$ ,  $\mathcal{F}$  the usual product  $\sigma$ -algebra, and  $P=P_p$  the probability measure.
- Now consider an  $n \times n$  box centered at 0 and ask: what fraction of the points in that box belong to an infinite clusters? Does this fraction converge to a limit (in some sense: in probability, or maybe almost surely) as  $n \to \infty$ ?
- ▶ Let  $C_x = 1_{x \in \text{infinitecluster}}$ . If the  $C_x$  were independent or each other, then this would just be a law of large numbers question. But the  $C_x$  are not independent of each other far from it.
- ► We don't have independence. We have translation invariance instead. Is that good enough?
- ▶ More general:  $C_x$  distributed in *some* translation invariant way,  $EC_0 < \infty$ . Is mean of  $C_x$  (on large box) nearly constant?

18.175 Lecture 33

## Rephrasing problem

- Let  $\theta_x$  be the translation of the  $\mathbb{Z}^2$  that moves 0 to x. Each  $\theta_x$  induces a measure-preserving translation of  $\Omega$ . Then  $C_x(\omega) = C_0(\theta_{-x}(\omega))$ . So summing up the  $C_x$  values is the same as summing up the  $C_0(\theta_x(\omega))$  value over a range of x.
- ▶ The group of translations is generated by a one-step vertical and a one-step horizontal translation. Refer to the corresponding (commuting, P-preserving) maps on  $\Omega$  as  $\phi_1$  and  $\phi_2$ .
- We're interested in averaging  $C_0(\phi_1^j\phi_2^k\omega)$  over a range of (j,k) pairs.
- ► Let's simplify matters still further and consider the one-dimensional problem. In this case, we have a random variable *X* and we study empirical averages of the form

$$N^{-1}\sum_{n=1}^{N}X(\phi^{n}\omega).$$

# Examples: stationary $X_j$ sequences

- ▶ Could take X<sub>j</sub> i.i.d.
- ▶ Or  $X_n$  could be a Markov chain, with each individual  $X_j$  distributed according to a stationary distribution  $\pi$ .
- ▶ Rotations of the circle. Say  $X_0$  is uniform in [0,1] and generally  $X_i = X_0 + \alpha j$  modulo 1.
- ▶ If  $X_0, X_1,...$  is stationary and  $g : \mathbb{R}^{\{0,1,...\}} \to \mathbb{R}$  is measurable, then  $Y_k = g(X_k, X_{k+1},...)$  is stationary.
- ▶ Bernoulli shift.  $X_0, X_1, \ldots$  are i.i.d. and  $Y_k = \sum_{j=1}^{\infty} X_{k+j} 2^{-j}$ .
- ► Can constructed two-sided (ℤ-indexed) stationary sequence from one-sided stationary sequence by Kolmogorov extension.
- What if X<sub>i</sub> are i.i.d. tosses of a p-coin, where p is itself random?

#### **Definitions**

- Say that A is **invariant** if the symmetric difference between  $\phi(A)$  and A has measure zero.
- ▶ Observe: class  $\mathcal{I}$  of invariant events is a  $\sigma$ -field.
- ▶ Measure preserving transformation is called **ergodic** if  $\mathcal{I}$  is trivial, i.e., every set  $A \in \mathcal{I}$  satisfies  $P(A) \in \{0,1\}$ .
- ▶ **Example:** If  $\Omega = \mathbb{R}^{\{0,1,\dots\}}$  and A is invariant, then A is necessarily in tail  $\sigma$ -field  $\mathcal{T}$ , hence has probability zero or one by Kolmogorov's 0-1 law. So sequence is ergodic (the shift on sequence space  $\mathbb{R}^{\{0,1,2,\dots\}}$  is ergodic..

Setup

Birkhoff's ergodic theorem

Setup

Birkhoff's ergodic theorem

## Ergodic theorem

Let  $\phi$  be a measure preserving transformation of  $(\Omega, \mathcal{F}, P)$ . Then for any  $X \in L^1$  we have

$$\frac{1}{n}\sum_{m=0}^{n-1}X(\phi^m\omega)\to E(X|\mathcal{I})$$

a.s. and in  $L^1$ .

- Note: if sequence is ergodic, then  $E(X|\mathcal{I}) = E(X)$ , so the limit is just the mean.
- Proof takes a couple of pages. Shall we work through it?

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 34 Ergodic theory

Scott Sheffield

MIT

Recall setup

Recall setup

# Motivating problem

- ▶ Consider independent bond percolation on  $\mathbb{Z}^2$  with some fixed parameter p > 1/2. Look at some simulations.
- Let  $\Omega$  be the set of maps from the edges of  $\mathbb{Z}^2$  to  $\{0,1\}$ ,  $\mathcal{F}$  the usual product  $\sigma$ -algebra, and  $P=P_p$  the probability measure.
- Now consider an  $n \times n$  box centered at 0 and ask: what fraction of the points in that box belong to an infinite clusters? Does this fraction converge to a limit (in some sense: in probability, or maybe almost surely) as  $n \to \infty$ ?
- ▶ Let  $C_x = 1_{x \in \text{infinitecluster}}$ . If the  $C_x$  were independent or each other, then this would just be a law of large numbers question. But the  $C_x$  are not independent of each other far from it.
- ► We don't have independence. We have translation invariance instead. Is that good enough?
- ▶ More general:  $C_x$  distributed in *some* translation invariant way,  $EC_0 < \infty$ . Is mean of  $C_x$  (on large box) nearly constant?

# Rephrasing problem

- Let  $\theta_x$  be the translation of the  $\mathbb{Z}^2$  that moves 0 to x. Each  $\theta_x$  induces a measure-preserving translation of  $\Omega$ . Then  $C_x(\omega) = C_0(\theta_{-x}(\omega))$ . So summing up the  $C_x$  values is the same as summing up the  $C_0(\theta_x(\omega))$  value over a range of x.
- ▶ The group of translations is generated by a one-step vertical and a one-step horizontal translation. Refer to the corresponding (commuting, P-preserving) maps on  $\Omega$  as  $\phi_1$  and  $\phi_2$ .
- We're interested in averaging  $C_0(\phi_1^j\phi_2^k\omega)$  over a range of (j,k) pairs.
- ▶ Let's simplify matters still further and consider the one-dimensional problem. In this case, we have a random variable *X* and we study empirical averages of the form

$$N^{-1}\sum_{n=1}^{N}X(\phi^{n}\omega).$$

# Examples: stationary $X_j$ sequences

- ▶ Could take X<sub>j</sub> i.i.d.
- ▶ Or  $X_n$  could be a Markov chain, with each individual  $X_j$  distributed according to a stationary distribution  $\pi$ .
- ▶ Rotations of the circle. Say  $X_0$  is uniform in [0,1] and generally  $X_i = X_0 + \alpha j$  modulo 1.
- ▶ If  $X_0, X_1,...$  is stationary and  $g : \mathbb{R}^{\{0,1,...\}} \to \mathbb{R}$  is measurable, then  $Y_k = g(X_k, X_{k+1},...)$  is stationary.
- ▶ Bernoulli shift.  $X_0, X_1, \ldots$  are i.i.d. and  $Y_k = \sum_{j=1}^{\infty} X_{k+j} 2^{-j}$ .
- ► Can constructed two-sided (ℤ-indexed) stationary sequence from one-sided stationary sequence by Kolmogorov extension.
- What if X<sub>i</sub> are i.i.d. tosses of a p-coin, where p is itself random?


#### **Definitions**

- ▶ Say that A is **invariant** if the symmetric difference between  $\phi(A)$  and A has measure zero.
- ▶ Observe: class  $\mathcal{I}$  of invariant events is a  $\sigma$ -field.
- ▶ Measure preserving transformation is called **ergodic** if  $\mathcal{I}$  is trivial, i.e., every set  $A \in \mathcal{I}$  satisfies  $P(A) \in \{0,1\}$ .
- ▶ **Example:** If  $\Omega = \mathbb{R}^{\{0,1,\ldots\}}$  and A is invariant, then A is necessarily in tail  $\sigma$ -field  $\mathcal{T}$ , hence has probability zero or one by Kolmogorov's 0-1 law. So sequence is ergodic (the shift on sequence space  $\mathbb{R}^{\{0,1,2,\ldots\}}$  is ergodic.
- ▶ Other examples: What about fair coin toss  $(\Omega = \{H, T\})$  with  $\phi(H) = T$  and  $\phi(T) = H$ ? What about stationary Markov chain sequences?


Recall setup

Recall setup

# Ergodic theorem

Let  $\phi$  be a measure preserving transformation of  $(\Omega, \mathcal{F}, P)$ . Then for any  $X \in L^1$  we have

$$\frac{1}{n}\sum_{m=0}^{n-1}X(\phi^m\omega)\to E(X|\mathcal{I})$$

a.s. and in  $L^1$ .

- Note: if sequence is ergodic, then  $E(X|\mathcal{I}) = E(X)$ , so the limit is just the mean.
- ▶ Proof takes a couple of pages. Shall we work through it?
- ▶ There's this lemma: let  $A_k$  be the event the maximum  $M_k$  of  $X_0$  and  $X_0 + X_1$  up to  $X_1 + \ldots + X_{k-1}$  is non-negative. Then  $EX_01_{A_k} \ge 0$  is non-negative.

#### Benford's law

- ► Typical starting digit of a physical constant? Look up Benford's law.
- ▶ Does ergodic theorem kind of give a mathematical framework for this law?

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 35 Ergodic theory

Scott Sheffield

MIT


Recall setup

Birkhoff's ergodic theorem


Recall setup

Birkhoff's ergodic theorem

#### **Definitions**

- ▶ Say that A is **invariant** if the symmetric difference between  $\phi(A)$  and A has measure zero.
- ▶ Observe: class  $\mathcal{I}$  of invariant events is a  $\sigma$ -field.
- ▶ Measure preserving transformation is called **ergodic** if  $\mathcal{I}$  is trivial, i.e., every set  $A \in \mathcal{I}$  satisfies  $P(A) \in \{0,1\}$ .
- ▶ **Example:** If  $\Omega = \mathbb{R}^{\{0,1,\ldots\}}$  and A is invariant, then A is necessarily in tail  $\sigma$ -field  $\mathcal{T}$ , hence has probability zero or one by Kolmogorov's 0-1 law. So sequence is ergodic (the shift on sequence space  $\mathbb{R}^{\{0,1,2,\ldots\}}$  is ergodic.
- ▶ Other examples: What about fair coin toss  $(\Omega = \{H, T\})$  with  $\phi(H) = T$  and  $\phi(T) = H$ ? What about stationary Markov chain sequences?


Recall setup

Birkhoff's ergodic theorem

Recall setup

Birkhoff's ergodic theorem

## Ergodic theorem

Let  $\phi$  be a measure preserving transformation of  $(\Omega, \mathcal{F}, P)$ . Then for any  $X \in L^1$  we have

$$\frac{1}{n}\sum_{m=0}^{n-1}X(\phi^m\omega)\to E(X|\mathcal{I})$$

a.s. and in  $L^1$ .

- Note: if sequence is ergodic, then  $E(X|\mathcal{I}) = E(X)$ , so the limit is just the mean.
- Proof takes a couple of pages. Shall we work through it?
- ▶ There's this lemma: let  $A_k$  be the event the maximum  $M_k$  of  $X_0$  and  $X_0 + X_1$  up to  $X_1 + \ldots + X_{k-1}$  is non-negative. Then  $EX_01_{A_k} \ge 0$  is non-negative.

#### Benford's law

- ► Typical starting digit of a physical constant? Look up Benford's law.
- ► Does ergodic theorem kind of give a mathematical framework for this law?

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 36 Brownian motion

Scott Sheffield

MIT

Brownian motion properties and construction

Brownian motion properties and construction

### Basic properties

- ▶ Brownian motion is real-valued process  $B_t$ ,  $t \ge 0$ .
- ▶ Independent increments: If  $t_0 < t_1 < t_2 ...$  then  $B(t_0), B(t_1 t_0), B(t_2 t_1), ...$  are independent.
- ▶ Gaussian increments: If  $s, t \ge 0$  then B(s + t) B(s) is normal with variance t.
- **Continuity:** With probability one,  $t \rightarrow B_t$  is continuous.
- ▶ Hmm... does this mean we need to use a  $\sigma$ -algebra in which the event " $B_t$  is continuous" is a measurable?
- ▶ Suppose  $\Omega$  is set of all functions of t, and we use smallest  $\sigma$ -field that makes each  $B_t$  a measurable random variable... does that fail?

## Basic properties

- ▶ Translation invariance: is  $B_{t_0+t} B_{t_0}$  a Brownian motion?
- ▶ Brownian scaling: fix c, then  $B_{ct}$  agrees in law with  $c^{1/2}B_t$ .
- ▶ Another characterization: B is jointly Gaussian,  $EB_s = 0$ ,  $EB_sB_t = s \land t$ , and  $t \rightarrow B_t$  a.s. continuous.

# Defining Brownian motion

- Can define joint law of B<sub>t</sub> values for any finite collection of values.
- ▶ Can observe consistency and extend to countable set by Kolmogorov. This gives us measure in  $\sigma$ -field  $\mathcal{F}_0$  generated by cylinder sets.
- But not enough to get a.s. continuity.
- Can define Brownian motion jointly on diadic rationals pretty easily. And claim that this a.s. extends to continuous path in unique way.
- Check out Kolmogorov continuity theorem.
- Can prove Hölder continuity using similar estimates (see problem set).
- ► Can extend to higher dimensions: make each coordinate independent Brownian motion.

Brownian motion properties and construction

Brownian motion properties and construction

# More $\sigma$ -algebra thoughts

- Write  $\mathcal{F}_s^o = \sigma(B_r : r \leq s)$ .
- Write  $\mathcal{F}_s^+ = \cap_{t>s} \mathcal{F}_t^o$
- ▶ Note right continuity:  $\cap_{t>s} \mathcal{F}_t^+ = \mathcal{F}_s^+$ .
- $\triangleright$   $\mathcal{F}_s^+$  allows an "infinitesimal peek at future"

## Markov property

▶ If  $s \ge 0$  and Y is bounded and  $\mathcal{C}$ -measurable, then for all  $x \in \mathbb{R}^d$ , we have

$$E_{x}(Y \circ \theta_{s}|\mathcal{F}_{s}^{+}) = E_{B_{s}}Y,$$

where the RHS is function  $\phi(x) = E_x Y$  evaluated at  $x = B_s$ .

#### Blumenthal's 0-1 law

- ▶ If  $A \in \mathcal{F}_0^+$ , then  $P(A) \in \{0,1\}$  (if P is probability law for Brownian motion started at fixed value x at time 0).
- ► There's nothing you can learn from infinitesimal neighborhood of future

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 37 More Brownian motion

Scott Sheffield

MIT

Brownian motion properties and construction

Brownian motion properties and construction

## Basic properties

- ▶ Brownian motion is real-valued process  $B_t$ ,  $t \ge 0$ .
- ▶ Independent increments: If  $t_0 < t_1 < t_2 ...$  then  $B(t_0), B(t_1 t_0), B(t_2 t_1), ...$  are independent.
- ▶ Gaussian increments: If  $s, t \ge 0$  then B(s + t) B(s) is normal with variance t.
- ▶ **Continuity:** With probability one,  $t \rightarrow B_t$  is continuous.
- ▶ Hmm... does this mean we need to use a  $\sigma$ -algebra in which the event " $B_t$  is continuous" is a measurable?
- ▶ Suppose  $\Omega$  is set of all functions of t, and we use smallest  $\sigma$ -field that makes each  $B_t$  a measurable random variable... does that fail?

## Basic properties

- ▶ Translation invariance: is  $B_{t_0+t} B_{t_0}$  a Brownian motion?
- ▶ Brownian scaling: fix c, then  $B_{ct}$  agrees in law with  $c^{1/2}B_t$ .
- ▶ Another characterization: B is jointly Gaussian,  $EB_s = 0$ ,  $EB_sB_t = s \land t$ , and  $t \rightarrow B_t$  a.s. continuous.

# Defining Brownian motion

- Can define joint law of B<sub>t</sub> values for any finite collection of values.
- ▶ Can observe consistency and extend to countable set by Kolmogorov. This gives us measure in  $\sigma$ -field  $\mathcal{F}_0$  generated by cylinder sets.
- But not enough to get a.s. continuity.
- Can define Brownian motion jointly on diadic rationals pretty easily. And claim that this a.s. extends to continuous path in unique way.
- ▶ We can use the Kolmogorov continuity theorem (next slide).
- Can prove Hölder continuity using similar estimates (see problem set).
- ► Can extend to higher dimensions: make each coordinate independent Brownian motion.

## Continuity theorem

- ▶ Kolmogorov continuity theorem: Suppose  $E|X_s X_t|^{\beta} \le K|t s|^{1+\alpha}$  where  $\alpha, \beta > 0$ . If  $\gamma < \alpha/\beta$  then with probability one there is a constant  $C(\omega)$  so that  $|X(q) X(r)| \le C|q r|^{\gamma}$  for all  $q, r \in \mathbb{Q}_2 \cap [0, 1]$ .
- ▶ **Proof idea:** First look at values at all multiples of  $2^{-0}$ , then at all multiples of  $2^{-1}$ , then multiples of  $2^{-2}$ , etc.
- At each stage we can draw a nice piecewise linear approximation of the process. How much does the approximation change in supremum norm (or some other Hölder norm) on the *i*th step? Can we say it probably doesn't change very much? Can we say the sequence of approximations is a.s. Cauchy in the appropriate normed spaced?

## Continuity theorem proof

- ▶ Kolmogorov continuity theorem: Suppose  $E|X_s-X_t|^{\beta} \leq K|t-s|^{1+\alpha}$  where  $\alpha,\beta>0$ . If  $\gamma<\alpha/\beta$  then with probability one there is a constant  $C(\omega)$  so that  $|X(q)-X(r)|\leq C|q-r|^{\gamma}$  for all  $q,r\in\mathbb{Q}_2\cap[0,1]$ .
- Argument from Durrett (Pemantle): Write

$$G_n = \{|X(i/2^n) - X((i-1)/2^n)|\} \le C|q-r|^{\lambda} \text{ for } 0 < i \le 2^n\}.$$

► Chebyshev implies  $P(|Y| > a) \le a^{-\beta} E|Y|^{\beta}$ , so if  $\lambda = \alpha - \beta\gamma > 0$  then

$$P(G_n^c) \leq 2^n \cdot 2^{n\beta\gamma} \cdot E|X(j2^{-n})|^{\beta} = K2^{-n\lambda}.$$

# Easy observations

- ▶ Brownian motion is Hölder continuous for any  $\gamma < 1/2$  (apply theorem with  $\beta = 2m, \alpha = m-1$ ).
- Brownian motion is almost surely not differentiable.
- Brownian motion is almost surely not Lipschitz.
- ▶ Kolmogorov-Centsov theorem applies to higher dimensions (with adjusted exponents). One can construct a.s. continuous functions from  $\mathbb{R}^n$  to  $\mathbb{R}$ .

Brownian motion properties and construction

Brownian motion properties and construction

# More $\sigma$ -algebra thoughts

- Write  $\mathcal{F}_s^o = \sigma(B_r : r \leq s)$ .
- $\blacksquare$  Write  $\mathcal{F}^+_s = \cap_{t>s} \mathcal{F}^o_t$
- ▶ Note right continuity:  $\cap_{t>s} \mathcal{F}_t^+ = \mathcal{F}_s^+$ .
- $\rightharpoonup \mathcal{F}_s^+$  allows an "infinitesimal peek at future"

## Markov property

▶ If  $s \ge 0$  and Y is bounded and C-measurable, then for all  $x \in \mathbb{R}^d$ , we have

$$E_{\mathsf{x}}(\mathsf{Y} \circ \theta_{\mathsf{s}} | \mathcal{F}_{\mathsf{s}}^{+}) = E_{\mathsf{B}_{\mathsf{s}}} \mathsf{Y},$$

where the RHS is function  $\phi(x) = E_x Y$  evaluated at  $x = B_s$ .

▶ **Proof idea:** First establish this for some simple functions *Y* (depending on finitely many time values) and then use measure theory (monotone class theorem) to extend to general case.

## Looking ahead

▶ **Theorem:** If Z is bounded, measurable then for  $s \ge 0$  have

$$E_x(A|\mathcal{F}_s^+)=E_x(Z|\mathcal{F}_s^0).$$

#### Blumenthal's 0-1 law

- ▶ If  $A \in \mathcal{F}_0^+$ , then  $P(A) \in \{0,1\}$  (if P is probability law for Brownian motion started at fixed value x at time 0).
- ► There's nothing you can learn from infinitesimal neighborhood of future

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 38

## **Even more Brownian motion**

Scott Sheffield

MIT

Recollections

Recollections

## Basic properties

- ▶ Brownian motion is real-valued process  $B_t$ ,  $t \ge 0$ .
- ▶ Independent increments: If  $t_0 < t_1 < t_2 ...$  then  $B(t_0), B(t_1 t_0), B(t_2 t_1), ...$  are independent.
- ▶ Gaussian increments: If  $s, t \ge 0$  then B(s + t) B(s) is normal with variance t.
- **Continuity:** With probability one,  $t \rightarrow B_t$  is continuous.
- ▶ Hmm... does this mean we need to use a  $\sigma$ -algebra in which the event " $B_t$  is continuous" is a measurable?
- ▶ Suppose  $\Omega$  is set of all functions of t, and we use smallest  $\sigma$ -field that makes each  $B_t$  a measurable random variable... does that fail?

## Basic properties

- ▶ Translation invariance: is  $B_{t_0+t} B_{t_0}$  a Brownian motion?
- ▶ Brownian scaling: fix c, then  $B_{ct}$  agrees in law with  $c^{1/2}B_t$ .
- ▶ Another characterization: B is jointly Gaussian,  $EB_s = 0$ ,  $EB_sB_t = s \land t$ , and  $t \rightarrow B_t$  a.s. continuous.

# Defining Brownian motion

- Can define joint law of B<sub>t</sub> values for any finite collection of values.
- ▶ Can observe consistency and extend to countable set by Kolmogorov. This gives us measure in  $\sigma$ -field  $\mathcal{F}_0$  generated by cylinder sets.
- But not enough to get a.s. continuity.
- Can define Brownian motion jointly on diadic rationals pretty easily. And claim that this a.s. extends to continuous path in unique way.
- ▶ We can use the Kolmogorov continuity theorem (next slide).
- Can prove Hölder continuity using similar estimates (see problem set).
- Can extend to higher dimensions: make each coordinate independent Brownian motion.


18.175 Lecture 38

## Continuity theorem

- ▶ Kolmogorov continuity theorem: Suppose  $E|X_s X_t|^{\beta} \le K|t s|^{1+\alpha}$  where  $\alpha, \beta > 0$ . If  $\gamma < \alpha/\beta$  then with probability one there is a constant  $C(\omega)$  so that  $|X(q) X(r)| \le C|q r|^{\gamma}$  for all  $q, r \in \mathbb{Q}_2 \cap [0, 1]$ .
- ▶ **Proof idea:** First look at values at all multiples of  $2^{-0}$ , then at all multiples of  $2^{-1}$ , then multiples of  $2^{-2}$ , etc.
- At each stage we can draw a nice piecewise linear approximation of the process. How much does the approximation change in supremum norm (or some other Hölder norm) on the *i*th step? Can we say it probably doesn't change very much? Can we say the sequence of approximations is a.s. Cauchy in the appropriate normed spaced?

-

## Continuity theorem proof

- ▶ Kolmogorov continuity theorem: Suppose  $E|X_s-X_t|^{\beta} \leq K|t-s|^{1+\alpha}$  where  $\alpha,\beta>0$ . If  $\gamma<\alpha/\beta$  then with probability one there is a constant  $C(\omega)$  so that  $|X(q)-X(r)|\leq C|q-r|^{\gamma}$  for all  $q,r\in\mathbb{Q}_2\cap[0,1]$ .
- Argument from Durrett (Pemantle): Write

$$G_n = \{|X(i/2^n) - X((i-1)/2^n)|\} \le C|q-r|^{\lambda} \text{ for } 0 < i \le 2^n\}.$$

► Chebyshev implies  $P(|Y| > a) \le a^{-\beta} E|Y|^{\beta}$ , so if  $\lambda = \alpha - \beta\gamma > 0$  then

$$P(G_n^c) \leq 2^n \cdot 2^{n\beta\gamma} \cdot E|X(j2^{-n})|^{\beta} = K2^{-n\lambda}.$$

# Easy observations

- ▶ Brownian motion is Hölder continuous for any  $\gamma < 1/2$  (apply theorem with  $\beta = 2m, \alpha = m 1$ ).
- Brownian motion is almost surely not differentiable.
- Brownian motion is almost surely not Lipschitz.
- ▶ Kolmogorov-Centsov theorem applies to higher dimensions (with adjusted exponents). One can construct a.s. continuous functions from  $\mathbb{R}^n$  to  $\mathbb{R}$ .

Recollections

Recollections

# More $\sigma$ -algebra thoughts

- Write  $\mathcal{F}_s^o = \sigma(B_r : r \leq s)$ .
- $\blacksquare$  Write  $\mathcal{F}^+_s = \cap_{t>s} \mathcal{F}^o_t$
- ▶ Note right continuity:  $\cap_{t>s} \mathcal{F}_t^+ = \mathcal{F}_s^+$ .
- $\rightharpoonup \mathcal{F}_{s}^{+}$  allows an "infinitesimal peek at future"

## Markov property

▶ If  $s \ge 0$  and Y is bounded and C-measurable, then for all  $x \in \mathbb{R}^d$ , we have

$$E_{\mathsf{x}}(\mathsf{Y} \circ \theta_{\mathsf{s}} | \mathcal{F}_{\mathsf{s}}^{+}) = E_{\mathsf{B}_{\mathsf{s}}} \mathsf{Y},$$

where the RHS is function  $\phi(x) = E_x Y$  evaluated at  $x = B_s$ .

▶ **Proof idea:** First establish this for some simple functions *Y* (depending on finitely many time values) and then use measure theory (monotone class theorem) to extend to general case.

# Looking ahead

**Expectation equivalence theorem** If *Z* is bounded and measurable then for all  $s \ge 0$  and  $x \in \mathbb{R}^d$  have

$$E_{\mathsf{x}}(Z|\mathcal{F}_{\mathsf{s}}^{+}) = E_{\mathsf{x}}(Z|\mathcal{F}_{\mathsf{s}}^{o}).$$

- ▶ **Proof idea:** Consider case that  $Z = \sum_{i=1}^m f_m(B(t_m))$  and the  $f_m$  are bounded and measurable. Kind of obvious in this case. Then use same measure theory as in Markov property proof to extend general Z.
- ▶ **Observe:** If  $Z \in \mathcal{F}_s^+$  then  $Z = E_x(Z|\mathcal{F}_s^o)$ . Conclude that  $\mathcal{F}_s^+$  and  $\mathcal{F}_s^o$  agree up to null sets.

#### Blumenthal's 0-1 law

- ▶ If  $A \in \mathcal{F}_0^+$ , then  $P(A) \in \{0,1\}$  (if P is probability law for Brownian motion started at fixed value x at time 0).
- There's nothing you can learn from infinitesimal neighborhood of future.
- ▶ **Proof:** If we have  $A \in \mathcal{F}_0^+$ , then previous theorem implies

$$1_A = E_x(1_A|\mathcal{F}_0^+) = E_x(1_A|\mathcal{F}_0^o) = P_x(A) \quad P_x \text{a.s.}$$

#### More observations

- ▶ If  $\tau = \inf\{t \ge 0 : B_t > 0\}$  then  $P_0(\tau = 0) = 1$ .
- ▶ If  $T_0 = \inf\{t > 0 : B_t = 0\}$  then  $P_0(T_0 = 0) = 1$ .
- ▶ If  $B_t$  is Brownian motion started at 0, then so is process defined by  $X_0 = 0$  and  $X_t = tB(1/t)$ . (Proved by checking  $E(X_sX_t) = stE(B(1/s)B(1/t)) = s$  when s < t. Then check continuity at zero.)

## Continuous martingales

- ▶ What can we say about continuous martingales?
- Do they all kind of look like Brownian motion?

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# 18.175: Lecture 39 Last lecture

Scott Sheffield

MIT

Recollections

Recollections

# More $\sigma$ -algebra thoughts

- Write  $\mathcal{F}_s^o = \sigma(B_r : r \leq s)$ .
- $\blacksquare$  Write  $\mathcal{F}^+_s = \cap_{t>s} \mathcal{F}^o_t$
- ▶ Note right continuity:  $\cap_{t>s} \mathcal{F}_t^+ = \mathcal{F}_s^+$ .
- $\rightharpoonup \mathcal{F}_s^+$  allows an "infinitesimal peek at future"

## Looking ahead

**Expectation equivalence theorem** If *Z* is bounded and measurable then for all  $s \ge 0$  and  $x \in \mathbb{R}^d$  have

$$E_{\mathsf{x}}(Z|\mathcal{F}_{\mathsf{s}}^{+}) = E_{\mathsf{x}}(Z|\mathcal{F}_{\mathsf{s}}^{\mathsf{o}}).$$

- ▶ **Proof idea:** Consider case that  $Z = \sum_{i=1}^m f_m(B(t_m))$  and the  $f_m$  are bounded and measurable. Kind of obvious in this case. Then use same measure theory as in Markov property proof to extend general Z.
- ▶ **Observe:** If  $Z \in \mathcal{F}_s^+$  then  $Z = E_x(Z|\mathcal{F}_s^o)$ . Conclude that  $\mathcal{F}_s^+$  and  $\mathcal{F}_s^o$  agree up to null sets.

#### Blumenthal's 0-1 law

- ▶ If  $A \in \mathcal{F}_0^+$ , then  $P(A) \in \{0,1\}$  (if P is probability law for Brownian motion started at fixed value x at time 0).
- There's nothing you can learn from infinitesimal neighborhood of future.
- ▶ **Proof:** If we have  $A \in \mathcal{F}_0^+$ , then previous theorem implies

$$1_A = E_x(1_A|\mathcal{F}_0^+) = E_x(1_A|\mathcal{F}_0^o) = P_x(A) \quad P_x \text{a.s.}$$

## Markov property

▶ If  $s \ge 0$  and Y is bounded and C-measurable, then for all  $x \in \mathbb{R}^d$ , we have

$$E_{\mathsf{x}}(\mathsf{Y} \circ \theta_{\mathsf{s}} | \mathcal{F}_{\mathsf{s}}^{+}) = E_{\mathsf{B}_{\mathsf{s}}} \mathsf{Y},$$

where the RHS is function  $\phi(x) = E_x Y$  evaluated at  $x = B_s$ .

▶ **Proof idea:** First establish this for some simple functions *Y* (depending on finitely many time values) and then use measure theory (monotone class theorem) to extend to general case.

#### More observations

- ▶ If  $\tau = \inf\{t \ge 0 : B_t > 0\}$  then  $P_0(\tau = 0) = 1$ .
- ▶ If  $T_0 = \inf\{t > 0 : B_t = 0\}$  then  $P_0(T_0 = 0) = 1$ .
- ▶ If  $B_t$  is Brownian motion started at 0, then so is process defined by  $X_0 = 0$  and  $X_t = tB(1/t)$ . (Proved by checking  $E(X_sX_t) = stE(B(1/s)B(1/t)) = s$  when s < t. Then check continuity at zero.)

Recollections

Recollections

# Stopping time

- ▶ A random variable S taking values in  $[0, \infty]$  is a **stopping** time if for all  $t \ge 0$ , we have  $\{S > t\} \in \mathcal{F}_t$ .
- ▶ Distinction between  $\{S < t\}$  and  $\{S \le t\}$  doesn't make a difference for a right continuous filtration.
- ▶ Example: let  $S = \inf\{t : B_t \in A\}$  for some open (or closed) set A.

# Strong Markov property

▶ Let  $(s,\omega) \to Y_s(\omega)$  be bounded and  $\mathcal{R} \times \mathcal{C}$ -measurable. If S is a stopping time, then for all  $x \in \mathbb{R}^d$ 

$$E_x(Y_S \circ \theta_S | \mathcal{F}_S) = E_{B(S)} Y_S \text{ on } \{S < \infty\},$$

where RHS means function  $\phi(x, t) = E_x Y_t$  evaluated at x = B(S), and t = S.

- ► In fact, similar result holds for more general Markov processes (Feller processes).
- ▶ **Proof idea:** First consider the case that *S* a.s. belongs to an increasing countable sequence (e.g., *S* is a.s. a multiple of 2<sup>-n</sup>). Then this essentially reduces to discrete Markov property proof. Then approximate a general stopping time by a discrete time by rounding down to multiple of 2<sup>-n</sup>. Use some continuity estimates, bounded convergence, monotone class theorem to conclude.
- Extend optional stopping to continuous martingales similarly.

18.175 Lecture 39

# Continuous martingales

- ▶ **Question:** If  $B_t$  is a Brownian motion, then is  $B_t^2 t$  a martingale?
- ▶ **Question:** If  $B_t$  and  $\tilde{B}_t$  are independent Brownian motions, then is  $B_t\tilde{B}_t$  a martingale?
- ▶ **Question:** If  $B_t$  is a martingale, then is  $e^{B_t t/2}$  a martingale?
- ▶ Question: If  $B_t$  is a Brownian motion in  $\mathbb{C}$  (i.e., real and imaginary parts are independent Brownian motions) and f is an analytic function on  $\mathbb{C}$ , is  $f(B_t)$  a complex martingale?
- ▶ Question: If  $B_t$  is a Brownian motion on  $\mathbb{R}^d$  and f is a harmonic function on  $\mathbb{R}^d$ , is  $f(B_t)$  a martingale?
- ▶ **Question:** Suppose  $B_t$  is a one dimensional Brownian motion, and  $g_t : \mathbb{C} \to \mathbb{C}$  is determined by solving the ODE

$$\frac{\partial}{\partial t}g_t(z) = \frac{2}{g_t(z) - 2B_t}, \quad g_0(z) = z.$$

Is  $arg(g_t(z) - W_t)$  a martingale?

18.175 Lecture 39

#### Farewell... and for future reference..

- ▶ Course has reached finite stopping time. Process goes on.
- Future probability graduate courses include
  - ▶ 18.177: fall 2014 (Jason Miller)
  - ▶ 18.177: spring 2015 (Alice Giuonnet)
  - ▶ 18.176: fall or spring 2015-16
- Probability seminar: Mondays at 4:15.
- ▶ I am happy to help with quals and reading.
- ► Talk to friendly postdocs: Vadim Gorin, Jason Miller, Jonathon Novak, Charlie Smart, Nike Sun, Hao Wu.
- Thanks for taking the class!

MIT OpenCourseWare http://ocw.mit.edu

#### 18.175 Theory of Probability

Spring 2014

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
