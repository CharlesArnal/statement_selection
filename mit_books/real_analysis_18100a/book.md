# 18.100A: Complete Lecture Notes

# Contents

| 1                                                                                            | Sets, Set Operations, and Mathematical Induction                                       | 3          |
|----------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------|------------|
| 2                                                                                            | Cantor's Theory of Cardinality (Size)                                                  | 7          |
| 3                                                                                            | Cantor's Remarkable Theorem and the Rationals' Lack of the Least Upper Bound Property  | 9          |
| 4                                                                                            | The Characterization of the Real Numbers                                               | 13         |
| 5                                                                                            | The Archimedian Property, Density of the Rationals, and Absolute Value                 | 16         |
| 6                                                                                            | The Uncountabality of the Real Numbers                                                 | 20         |
| 7                                                                                            | Convergent Sequences of Real Numbers                                                   | 24         |
| 8                                                                                            | The Squeeze Theorem and Operations Involving Convergent Sequences                      | 27         |
| 9                                                                                            | Limsup, Liminf, and the Bolzano-Weierstrass Theorem                                    | 31         |
| 10                                                                                           | The Completeness of the Real Numbers and Basic Properties of Infinite Series           | 35         |
| 11                                                                                           | Absolute Convergence and the Comparison Test for Series                                | 39         |
| <b>12</b>                                                                                    | The Ratio, Root, and Alternating Series Tests                                          | 43         |
| <b>13</b>                                                                                    | Limits of Functions                                                                    | 47         |
| 14                                                                                           | Limits of Functions in Terms of Sequences and Continuity                               | <b>5</b> 0 |
| <b>15</b>                                                                                    | The Continuity of Sine and Cosine and the Many Discontinuities of Dirichlet's Function | 53         |
| 16                                                                                           | The $Min/Max$ Theorem and Bolzano's Intermediate Value Theorem                         | 56         |
| 17                                                                                           | Uniform Continuity and the Definition of the Derivative                                | 59         |
| 18                                                                                           | Weierstrass's Example of a Continuous and Nowhere Differentiable Function              | 62         |
| 19                                                                                           | Differentiation Rules, Rolle's Theorem, and the Mean Value Theorem                     | 65         |
| <b>20</b>                                                                                    | Taylor's Theorem and the Definition of Riemann Sums                                    | 69         |
| <b>21</b>                                                                                    | The Riemann Integral of a Continuous Function                                          | 72         |
| 22 The Fundamental Theorem of Calculus, Integration by Parts, and Change of Variable Formula | <b>76</b>                                                                              |            |
| 23 Pointwise and Uniform Convergence of Sequences of Functions                               | 81                                                                                     |            |
| 24 Uniform Convergence, the Weierstrass M-Test, and Interchanging Limits                     | 84                                                                                     |            |
| 25 Power Series and the Weierstrass Approximation Theorem                                    | 86                                                                                     |            |

## Sets, Set Operations, and Mathematical Induction

For this class, we will be using the book Introduction to Real Analysis, Volume I by Jiří Lebl [L]. I will use  $\blacksquare$  to end proofs of examples, and  $\square$  to end proofs of theorems.

## Basic Set Theory

Remark 1. There are two main goals of this class:

- 1. Gain experience with proofs.
- 2. Prove statements about real numbers, functions, and limits.

## $\underline{\mathbf{Set}}\mathbf{s}$

A set is a collection of objects called elements or members of that set. The empty set (denoted  $\emptyset$ ) is the set with no elements. There are a few symbols that are super helpful to know as a shorthand, and will be used throughout the course. Let S be a set. Then

- $a \in S$  means that "a is an element in S."
- $a \notin S$  means that "a is <u>not</u> an element in S."
- $\forall$  means "for all."
- := means "define."

- ∃ means "there exists."
- ∃! means "there exists a unique."
- $\implies$  means "implies."
- $\iff$  means "if and only if."

#### **Definition 2** (Set Relations)

We want to relate different sets, and thus we get the following notation/definitions:

- 1. A set A is a <u>subset</u> of B,  $A \subset B$ , if every element of A is in B. Given  $A \subset B$ , if  $a \in A \implies a \in B$ .
- 2. Two sets A and B are equal, A = B, if  $A \subset B$  and  $B \subset A$ .
- 3. A set A is a proper subset of B,  $A \subseteq B$  if  $A \subset B$  and  $A \neq B$ .

One way we can describe a set is using "set building notation". We write

$$\{x \in A \mid P(x)\}\ \text{ or } \{x \mid P(x)\}$$

to mean "all  $x \in A$  that satisfies property P(x)". One example of this would be  $\{x \mid x \text{ is an even number}\}$ . There are a few key sets that we will use throughout this class:

- 1. The set of natural numbers:  $\mathbb{N} = \{1, 2, 3, 4, \dots\}$ .
- 2. The set of integers:  $\mathbb{Z} = \{0, 1, -1, 2, -2, 3, -3, \dots\}$ .
- 3. The set of rational numbers:  $\mathbb{Q} = \{ \frac{m}{n} \mid m, n \in \mathbb{Z} \text{ and } n \neq 0 \}.$
- 4. The set of real numbers:  $\mathbb{R}$ .

It follows that

$$\mathbb{N} \subset \mathbb{Z} \subset \mathbb{Q} \subset \mathbb{R}$$
.


The fourth item on this list brings us to an important question, and the first goal of our course:

#### Problem 3

How do we describe  $\mathbb{R}$ ?

We will answer this question in Lectures 3 and 4. In the meantime, let's continue our study of sets and proof methods. Given sets A and B, we have the following definitions:

- 1. The <u>union</u> of A and B is the set  $A \cup B = \{x \mid x \in A \text{ or } x \in B\}.$
- 2. The <u>intersection</u> of A and B is the set  $A \cap B = \{x \mid x \in A \text{ and } x \in B\}$ .
- 3. The set difference of A and B is the set  $A \setminus B = \{x \in A \mid x \notin B\}$ .
- 4. The complement of A is the set  $A^c = \{x \mid x \notin A\}$ .
- 5. A and B are disjoint if  $A \cap B = \emptyset$ .

**Theorem 4** (De Morgan's Laws)

If A, B, C are sets then

- 1.  $(B \cup C)^c = B^c \cap C^c$ ,
- $2. (B \cap C)^c = B^c \cup C^c,$
- 3.  $A \setminus (B \cup C) = (A \setminus B) \cap (A \setminus C)$ ,
- 4. and  $A \setminus (B \cap C) = (A \setminus B) \cup (A \setminus C)$ .

We will prove the first statement to give an example of how such a proof would go, but the rest will be left to you. **Proof**: Let B, C be sets. We must prove that

$$(B \cup C)^c \subset B^c \cap C^c$$
 and  $B^c \cap C^c \subset (B \cup C)^c$ .

If  $x \in (B \cup C)^c \implies x \notin B \cup C \implies x \notin B$  and  $x \notin C$ . Hence,  $x \in B^c$  and  $x \in C^c \implies x \in B^c \cap C^c$ . Thus,  $(B \cup C)^c \subset B^c \cap C^c$ .

If  $x \in B^c \cap C^c$  then  $x \in B^c$  and  $x \in C^c \implies x \notin B$  and  $x \notin C$ . Hence,  $x \notin B \cup C \implies x \in (B \cup C)^c$ . Thus,  $B^c \cap C^c \subset (B \cup C)^c$ .

## **Mathematical Induction**

We will now talk about some of the biggest proof methods there are. Firstly, note that  $\mathbb{N} = \{1, 2, 3, \dots\}$  has an ordering (as  $1 < 2 < 3 < \dots$ ).

## **Axiom 5** (Well-ordering property)

The well-ordering property of  $\mathbb{N}$  states that if  $S \subset \mathbb{N}$  then there exists an  $x \in S$  such that  $x \leq y$  for all  $y \in S$ . In other words, there is always a smallest element.

Note that this is an axiom, and thus we have to assume this without proof.

## Theorem 6 (Induction)

This concept was invented by Pascal in 1665. Let P(n) be a statement depending on  $n \in \mathbb{N}$ . Assume that

- 1. (Base case) P(1) is true and
- 2. (Inductive step) if P(m) is true then P(m+1) is true.

Then, P(n) is true for all  $n \in \mathbb{N}$ .

**Proof**: Let  $S = \{n \in \mathbb{N} \mid P(n) \text{ is not true}\}$ . We wish to show that  $S = \emptyset$ . We will prove this by contradiction.

**Remark 7.** When we prove something by contradiction, we assume the conclusion we want is false, and then show that we will reach a false statement. Rules of logic thus imply that the initial statement must be false. Thus in this case, we will assume  $S \neq \emptyset$  and derive a false statement.

Suppose that  $S \neq \emptyset$ . Then, by the well-ordering property of  $\mathbb{N}$ , S has a least element  $m \in S$ . Since P(1) is true,  $m \neq 1$ , i.e. m > 1. Since m is a least element,  $m - 1 \notin S \implies P(m - 1)$  is true. This implies that P(m) is true  $\implies m \notin S$  by assumption. But then  $m \in S$  and  $m \notin S$ . This is a contradiction. Thus  $S = \emptyset$  and hence P(n) is true for all  $n \in \mathbb{N}$ .

Let's see an example of induction in action.

#### Theorem 8

For all  $c \neq 1$  in the real numbers, and for all  $n \in \mathbb{N}$ ,

$$1 + c + c^{2} + \dots + c^{n} = \frac{1 - c^{n+1}}{1 - c}.$$

**Proof**: We will prove this by induction. First, we prove the base case (n = 1). The left hand side of the equation is 1 + c for n = 1. The right hand side is  $\frac{1-c^2}{1-c} = \frac{(1-c)(1+c)}{1-c} = 1 + c$ . Hence, the base case has been shown.

Assume that the equation is true for  $k \in \mathbb{N}$ , in other words

$$1 + c + c^2 + \dots + c^k = \frac{1 - c^{k+1}}{1 - c}.$$

Thus,

$$\implies 1 + c + c^2 + \dots + c^k + c^{k+1} = (1 + c + c^2 + \dots + c^k) + c^{k+1}$$

$$= \frac{1 - c^{k+1}}{1 - c} + c^{k+1}$$

$$= \frac{1 - c^{k+1} + c^{k+1}(1 - c)}{(1 - c)}$$

$$= \frac{1 - c^{(k+1)+1}}{1 - c}.$$

Therefore, our proof is complete.

Let's do another example:

## Theorem 9

For all  $c \ge -1$ ,  $(1+c)^n \ge 1 + nc$  for all  $n \in \mathbb{N}$ .

**Proof**: We prove this through induction. In the base case, we have:  $(1+c)^1 = 1+1 \cdot c$ . For the inductive step, suppose that

$$(1+c)^m \ge 1 + mc.$$

Then,

$$(1+c)^{m+1} = (1+c)^m \cdot (1+c).$$

By assumption,

$$\geq (1 + mc) \cdot (1 + c)$$

$$= 1 + (m+1)c + mc^{2}$$

$$\geq 1 + (m+1)c.$$

By induction, our proof is complete.

## Cantor's Theory of Cardinality (Size)

## **Functions**

If A and B are sets, a function  $f: A \to B$  is a mapping that assigns each  $x \in A$  to a <u>unique</u> element in B denoted f(x). Let  $f: A \to B$ . Then

- 1. If  $C \subset A$ , we define  $f(C) := \{ y \in B \mid y \in f(x) \text{ for some } x \in C \}$ .
- 2. If  $D \subset B$ , we define  $f^{-1}(D) := \{x \in A \mid f(x) \in D\}.$

As an example, consider the following mapping  $f: \{1, 2, 3, 4\} \rightarrow \{a, b\}$ :

We can categorize functions in 3 important ways. Let  $f: A \to B$ .

- 1. f is injective or one-to-one (1-1) if  $f(x_1) = f(x_2) \implies x_1 = x_2$ .
- 2. f is surjective or onto if f(A) = B.
- 3. f is bijective if it is 1-1 and onto.

If a function  $f: A \to B$  is bijective, then  $f^{-1}: B \to A$  is the function which assigns each  $y \in B$  to the unique  $x \in A$  such that f(x) = y. Note that  $f(f^{-1}(x)) = x$ .

## Cardinality

Question 10. When do two sets have the same size?

Cantor answered this question in the 1800s, stating that two sets have the same size when you can pair each element in one set with a unique element in the other.

#### **Definition 11** (Cardinality)

We state that two sets A and B have the same cardinality if there exists a bijection  $f: A \to B$ .

With this new concept comes some new notation:

- 1. |A| = |B| if A and B have the same cardinality.
- 2. |A| = n if  $|A| = |\{1, \dots, n\}|$ . If this is the case we say A is finite.
- 3.  $|A| \leq |B|$  if there exists an injection  $f: A \to B$ .
- 4. |A| < |B| if  $|A| \le |B|$  but  $|A| \ne |B|$ .

## Theorem 12 (Cantor-Schröder-Bernstein)

If  $|A| \leq |B|$  and  $|B| \leq |A|$  then |A| = |B|.

If  $|A| = |\mathbb{N}|$ , then A is <u>countably infinite</u>. If A is finite or countably infinite, we say A is countable. Otherwise, we say A is uncountable.

## Example 13

There are a few key theorems that we can prove with this new concept:

- 1.  $|\{2n \mid n \in \mathbb{N}\}| = |\mathbb{N}|$ .
- 2.  $|\{2n-1 \mid n \in \mathbb{N}\}| = |\mathbb{N}|$ .
- 3.  $|\{x \in \mathbb{Q} \mid x > 0\}| = |\mathbb{N}|$ .

The first two statements can be summarized by Feynman: "There are twice as many numbers as numbers." **Proof**:

- 1. Define the function  $f: \mathbb{N} \to \{2n \mid n \in \mathbb{N}\}$  as f(n) = 2n. Then, f is 1-1- if f(n) = f(m) then  $2n = 2m \implies n = m$ . Furthermore, f is also onto, as if  $m \in \{2n \mid n \in \mathbb{N}\}$  then  $\exists n \in \mathbb{N}$  such that m = 2n = f(n).
- 2. The second statement can be proven similarly.
- 3. This is left as an exercise to the reader in Assignment 1.

Cantor's Remarkable Theorem and the Rationals' Lack of the Least Upper Bound Property

**Question 14.** Is anything bigger than  $\mathbb{N}$ ?

If A is a set then  $\mathcal{P}(A) = \{B \mid B \subset A\}$ . Here are a few examples:

- 1.  $A = \emptyset$  then  $\mathcal{P}(A) = {\emptyset}$ .
- 2.  $A = \{1\}$ , then  $\mathcal{P}(A) = \{\emptyset, \{1\}\}$ .
- 3.  $A = \{1, 2\}, \text{ then } \mathcal{P}(A) = \{\emptyset, \{1\}, \{2\}, \{1, 2\}\}.$

In general, if |A| = n then  $|\mathcal{P}(A)| = 2^n$ . This is why we call  $\mathcal{P}(A)$  the power set of A.

**Theorem 15** (Cantor)

If A is a set, then  $|A| < |\mathcal{P}(A)|$ .

Remark 16. Therefore,

$$\mathbb{N} < |\mathcal{P}(\mathbb{N})| < |\mathcal{P}(\mathcal{P}(\mathbb{N}))| < \dots$$

Hence, there are an infinite number of infinite sets.

**Proof**: Define the function  $f: A \to \mathcal{P}(A)$  by  $f(x) = \{x\}$ . Then, f is 1-1- as if  $\{x\} = \{y\} \implies x = y$ . Thus,  $|A| \leq |\mathcal{P}(A)|$ . To finish the proof now all we need to show is that  $|A| \neq |\mathcal{P}(A)|$ . We will do so through contradiction. Suppose that  $|A| = |\mathcal{P}(A)|$ . Then, there exists a surjection  $g: A \to \mathcal{P}(A)$ . Let

$$B := \{ x \in A \mid x \notin g(x) \} \in \mathcal{P}(A).$$

Since g is surjective, there exists a  $b \in A$  such that g(b) = B. There are two cases:

- 1.  $b \in B$ . If this is the case, then  $b \notin g(b) = B \implies b \notin B$ .
- 2.  $b \notin B$ . If this is the case, then  $b \notin g(b) = B \implies b \in B$ .

In either case we obtain a contradiction. Thus, g is not surjective  $\implies |A| \neq |\mathcal{P}(A)|$ .

**Remark 17.** This is another proof method: casework. If the conclusion for every case is true, then the conclusion must be true.

Corollary 18

For all  $n \in \mathbb{N} \cup \{0\}$ ,  $n < 2^n$ .

Remark 19. This can also be shown by induction, see Assignment 1.

## Real Numbers

Remark 20. In a sense, to be made precise, the set of real numbers is the unique set with all of the <u>algebraic</u> and ordering properties of the rational numbers, but none of the holes.

#### Problem 21

Now let's try to precisely describe  $\mathbb{R}$ .

We will start by stating what our end result will be, and then we will derive it:

## **Theorem 22** (Real Numbers $(\mathbb{R})$ )

There exists a unique **ordered field** containing  $\mathbb{Q}$  with the **least upper bound property**. We denote this field by  $\mathbb{R}$ .

## Ordered Sets & Fields

## **Definition 23** (Ordered set)

An ordered set is a set S with a relation < called an "ordering" such that

- 1.  $\forall x, y \in S$  either x < y, y < x, or x = y.
- 2. If x < y and y < z then x < z.

Here are a few examples and one non-example:

- $\mathbb{Z}$  is an ordered set, with the relation that  $m > n \iff m n \in \mathbb{N}$ .
- $\mathbb{Q}$  is an ordered set, with the relation that  $p>q\iff \exists m,n\in\mathbb{N}$  such that  $p-q=\frac{m}{n}$ .
- $\mathbb{Q} \times \mathbb{Q}$  is an ordered set with the relation  $(q,r) > (s,t) \iff q > s$  or q = s and r > t.
- Consider the set  $\mathcal{P}(\mathbb{N})$ . Let  $A, B \in \mathcal{P}(\mathbb{N})$  and let  $A \prec B$  if  $A \subset B$ . This is **NOT** an ordered set—it doesn't satisfy the first property of an ordered set.

#### **Definition 24** (Bounded Above/Below)

Let S be an ordered set and let  $E \subset S$ . Then,

- 1. If there exists a  $b \in S$  such that  $x \leq b$  for all  $x \in E$ , then E is bounded above and b is an <u>vocab</u> of E.
- 2. If  $\exists c \in S$  such that  $x \geq c$  for all  $x \in E$ , then E is bounded below and c is a lower bound of E.

From here, there are some very important definitions in real analysis. We say that  $b_0$  is the **least upper** bound, or the supremum of E if

- A)  $b_0$  is an upper bound for E and
- B) if b is an upper bound for E then  $b_0 \leq b$ .

We denote this as  $b_0 = \sup E$ . Similarly, we say that  $c_0$  is the **greatest lower bound**, or the infinimum of E if

- A)  $c_0$  is a lower bound for E and
- B) if c is a lower bound for E then  $c < c_0$ .

We denote this as  $c_0 = \inf E$ .

### Example 25

Here are a few examples of infimums and supremums:

- $S = \mathbb{Z}$  and  $E = \{-2, -1, 0, 1, 2\}$ . Then, inf E = -2 and  $\sup E = 2$ .
- But, note that the supremum nor the infimum need to be in E. Consider the sets  $S=\mathbb{Q}$  and

$$E = \{ q \in \mathbb{Q} \mid 0 \le q < 1 \}.$$

Then, inf  $E = 0 \in E$ , but  $\sup E = 1 \notin E$ .

• Furthermore, neither the supremum nor the infimum need exist. Consider the sets  $S = \mathbb{Z}$  and  $E = \mathbb{N}$ . Then, inf E = 1, but sup E does not exist as there is not an integer greater than all natural numbers.

## **Definition 26** (Least Upper Bound Property)

An ordered set S has the least upper bound property if every  $E \subset S$  which is nonempty and bounded above has a supremum in S.

One example of such a set is

$$-\mathbb{N} = \{-1, -2, -3, \dots\}.$$

Then,  $E \subset S$  is bounded above if and only if  $-E \subset \mathbb{N}$  is bounded below. By the well-ordering principle, -E has a least element  $x \in -E$ , and thus  $-x = \sup E$ .

We will now show that  $\mathbb{Q}$  does not have the least upper bound property.

#### Theorem 27

If  $x \in \mathbb{Q}$  and

$$x = \sup\{q \in \mathbb{Q} \mid q > 0, q^2 < 2\}$$

then x > 0 and  $x^2 = 2$ .

**Proof**: Let E equal the set on the right hand side, and suppose  $x \in \mathbb{Q}$  such that  $x = \sup E$ . Then, since  $1 \in E$  and x is an upper bound for E,  $1 \le x \implies x > 0$ .

We now prove that  $x^2 \ge 2$ . Suppose that  $x^2 < 2$ . Define  $h = \min\left\{\frac{1}{2}, \frac{2-x^2}{2(2x+1)}\right\} < 1$ . Then, if  $x^2 < 2$  then h > 0. We now prove that  $x + h \in E$ . Indeed,

$$(x+h)^2 = x^2 + 2xh + h^2$$
  
<  $x^2 + h(2x+1)$ 

as h < 1. Hence

$$(x+h)^{2} \le x^{2} + (2-x^{2}) \cdot \frac{2x+1}{2(2x+1)}$$

$$= x^{2} + \frac{2-x^{2}}{2}$$

$$< 2 + \frac{2-2}{2}$$

$$= 2.$$

Therefore,  $x + h \in E$  and  $x + h > x \implies x$  is not an upper bound for E. Therefore,  $x \neq \sup E$  which is a contradiction. Hence,  $x^2 \geq 2$ .

We now prove that  $x^2 \le 2$ . Suppose  $x^2 > 2$ . Let  $h = \frac{x^2 - 2}{2x}$ . Hence, if  $x^2 > 2$  then h > 0 and x - h > 0. We will show that x - h is an upper bound for E. We have

$$(x - h)^{2} = x^{2} - 2xh + h^{2}$$

$$= x^{2} - (x^{2} - 2) + h^{2}$$

$$= 2 + h^{2}$$

$$> 2.$$

Let  $q \in E$ . Then,  $q^2 < 2 < (x-h)^2 \implies (x-h)^2 - q^2 > 0$ . Hence,

$$((x-h)+q)((x-h)+q)>0 \implies (x-h)-q>0.$$

Thus, for all  $q \in E$ ,  $q < x - h < x \implies x \neq \sup E$ . This is a contradiction. Therefore,  $x^2 = 2$ .

## Theorem 28

The set  $E = \{q \in \mathbb{Q} \mid q > 0 \text{ and } q^2 < 2\}$  does not have a supremum in  $\mathbb{Q}$ .

**Proof**: Suppose there exists an  $x \in \mathbb{Q}$  such that  $x = \sup E$ . Then, by our previous theorem,  $x^2 = 2$ . In particular, note that x > 1 as otherwise  $x \le 1 \implies 2 = x^2 < 1^2$ . Thus,  $\exists m, n \in \mathbb{N}$  such that m > n and  $x = \frac{m}{n}$ . Therefore,  $\exists n \in \mathbb{N}$  such that  $nx \in \mathbb{N}$ . Let

$$S = \{ k \in \mathbb{N} \mid kx \in \mathbb{N} \}.$$

Then,  $S \neq \emptyset$  since  $n \in S$ . By the well-ordering property of  $\mathbb{N}$ , S has a least element  $k_0 \in S$ . Let  $k_1 = k_0x - k_0 \in \mathbb{Z}$ . Then,  $k_1 = k_0(x-1) > 0$  since  $k_0 \in \mathbb{N}$  and x > 1. Therefore,  $k_1 \in \mathbb{N}$ . Now  $x^2 = 2 \implies x < 2$ , as otherwise  $x^2 > 4 > 2$ . Thus,  $k_1 = k_0(x-1) < k_0(2-1) = k_0$ . So,  $k_1 \in \mathbb{N}$  and  $k_1 < k_0 \implies k_1 \notin S$  as  $k_0$  is the least element of S. But,

$$xk_1 = k_0x^2 - xk_0 = 2k_0 - xk_0 = k_0 - k_1 \in \mathbb{N} \implies k_1 \in S.$$

This is a contradiction. Thus,  $\not\exists x \in \mathbb{Q}$  such that  $x = \sup E$ .

Q is an example of a field, which we will start to discuss in the next lecture.

## The Characterization of the Real Numbers

**Question 29.** Last time we stated that  $\mathbb{Q}$  was an example of a field, but what is a **field**?

## **Definition 30** (Field)

A set F is a field if it has two operations: addition (+) and multiplication  $(\cdot)$  with the following properties.

- A1) If  $x, y \in F$  then  $x + y \in F$ .
- A2) (Commutativity)  $\forall x, y \in F, x + y = y + x$ .
- A3) (Associativity)  $\forall x, y, z \in F$ , (x + y) + z = x + (y + z).
- A4)  $\exists$  an element  $0 \in F$  such that 0 + x = x = x + 0.
- A5)  $\forall x \in F$ ,  $\exists y \in F$  such that x + y = 0. We denote y = -x.
- M1) If  $x, y \in F$ , then  $x \cdot y \in F$ .
- M2) (Commutativity)  $\forall x, y \in F, x \cdot y = y \cdot x$ .
- M3) (Associativity)  $\forall x, y, z \in F, (x \cdot y) \cdot z = x \cdot (y \cdot z).$
- M4)  $\exists 1 \in F$  such that  $1 \cdot x = x = x \cdot 1$  for all  $x \in F$ .
- M5)  $\forall x \in F \setminus \{0\}, \exists x^{-1} \text{ such that } x \cdot x^{-1} = 1.$
- D) (Distributativity)  $\forall x, y, z \in F$ , (x + y)z = xz + yz.

These may seem like trivial properties, but consider the following non-example:  $\mathbb{Z}$ .  $\mathbb{Z}$  fails M5)— multiplicative inverses do not exist in the integers.

## Example 31

Here are two examples of fields:

- 1.  $\mathbb{Z}_2 = \{0, 1\}$  where 1 + 1 = 0.
- 2.  $\mathbb{Z}_3 = \{0, 1, 2\}$  with  $c := a + b \pmod{3}$ . In other words,

$$2+1=3=0\pmod{3}$$
 and  $2\cdot 2=4=3+1=1\pmod{3}$ .

Simple properties follow from the properties of a field!

#### Theorem 32

If  $x \in F$  where F is a field, 0x = 0.

**Proof**: If  $x \in F$ , then

$$0 = 0 \cdot x - 0 \cdot x = (0 + 0) \cdot x - 0 \cdot x = 0 \cdot x + 0 \cdot x - 0 \cdot x = 0 \cdot x.$$

## **Definition 33** (Ordered field)

A field F is an ordered field if F is also an ordered set with ordering < and

- i)  $\forall x, y, z \in F, x < y \implies x + z < y + z.$
- ii) If x > 0 and y > 0 then xy > 0.

If x > 0 we say x is **positive**, and if  $x \ge 0$  we say x is **non-negative**.

## Example 34

 $\mathbb{Q}$  is an ordered field.

A non-example would be  $\mathbb{Z}_2$ . For instance, consider 0 < 1. If 0 < 1, then  $1 + 0 < 1 + 1 = 0 \implies 1 < 0$  which is a contradiction. If 1 < 0, then  $0 = 1 + 1 < 0 + 1 \implies 0 < 1$  which is a contradiction. Hence,  $\mathbb{Z}_2$  is not an ordered field.

Using the definition of an ordered field, one can easily prove all of the usual facts about inequalities.

#### Theorem 35

If x > 0, then -x < 0 (and vice versa).

**Proof**: If  $x \in F$  and x > 0, then by i),

$$-x + x > -x \implies 0 > -x$$
.

One can see Proposition 1.1.8 [L] for a list of other simple inequality facts.

#### Theorem 36

Let  $x, y \in F$  where F is an ordered field. If x > 0 and y < 0 or x < 0 and y > 0, then xy < 0.

**Proof**: Suppose x > 0 and y < 0. Then, x > 0 and -y > 0. Hence, -xy = x(-y) > 0. Thus, xy < 0. If x < 0 and y > 0, then -x > 0 and  $y > 0 \implies -xy = (-x)y > 0 \implies xy < 0$ .

Question 37. Is there a greatest lower bound property?

For an ordered field F, if F has the least upper bound property then F has a greatest lower bound property.

#### Theorem 38

Let F be an ordered field with the least upper bound property. If  $A \subset F$  is nonempty and bounded below, then inf A exists in F.

**Proof**: Suppose  $A \subset F$  is nonempty and bounded below, i.e.  $\exists a \in F$  such that  $\forall x \in A, a \leq x$ . Let  $B = \{-x \mid x \in A\}$ . Then,  $\forall x \in A, -x \leq -a \implies -a$  is an upper bound for B. Since F has the least upper bound property,  $\exists c \in F$  such that  $c = \sup B$ . Then,  $\forall x \in A, -x \leq c \implies \forall x \in A, -c \leq x$ . Hence, -c is a lower bound for A. We have also shown that if a is a lower bound for A, then -a is an upper bound for B. Therefore,  $c \leq -a$  since  $c = \sup B \implies a \leq -c$ . Hence, -c is the greatest lower bound for A.

## Real Numbers

## Theorem 39

There exists a "unique" ordered field, labeled  $\mathbb{R}$ , such that  $\mathbb{Q} \subset \mathbb{R}$  and  $\mathbb{R}$  has the least upper bound property.

One can construct  $\mathbb{R}$  using Dedekind cuts or as equivalence classes of Cauchy sequences. (We will define Cauchy sequences later in the course.)

## Theorem 40

 $\exists ! r \in \mathbb{R} \text{ such that } r > 0 \text{ and } r^2 = 2.$  In other words,  $\sqrt{2} \in \mathbb{R} \text{ but } \sqrt{2} \notin \mathbb{Q}.$ 

**Proof**: Let  $\tilde{E} = \{x \in \mathbb{R} \mid x > 0 \text{ and } x^2 < 2\}$ . Then, since  $\tilde{E}$  is bounded above (by 2 for instance), we have that  $r := \sup \tilde{E}$  exists in  $\mathbb{R}$ . Then, one can show that r > 0 and  $r^2 = 2$ . This is left as an exercise.

We now prove uniqueness. Suppose that there is a  $\tilde{r} > 0$  with  $\tilde{r}^2 = 2$ . Then, since  $(r + \tilde{r}) > 0$ ,

$$0 = r^2 - \tilde{r}^2 = (r + \tilde{r})(r - \tilde{r}) \implies r - \tilde{r} = 0 \implies r = \tilde{r}.$$

**Remark 41.** In Assignment 2 Exercise 7, you will show that  $\sqrt[3]{2} \in \mathbb{R}$ .

The Archimedian Property, Density of the Rationals, and Absolute Value

For all  $x, y \in \mathbb{R}$  and x < y, there exists an  $r \in \mathbb{R}$  such that x < r < y (take  $r = \frac{x+y}{2}$ ).

**Question 42.** Can we find  $r \in \mathbb{Q}$  such that x < r < y?

## Theorem 43

The answer is yes!

- i) (Archimedian Property) If  $x, y \in \mathbb{R}$  and x > 0, then  $\exists n \in \mathbb{N}$  such that nx > y.
- ii) (Density of  $\mathbb{Q}$ ) If  $x, y \in \mathbb{R}$  and x < y then  $\exists r \in \mathbb{Q}$  such that x < r < y.

#### **Proof**:

i) Suppose that  $x, y \in \mathbb{R}$  and x > 0. Then we wish to show that  $\exists n \in \mathbb{N}$  such that  $n > \frac{y}{x}$ . Suppose this is not the case. Then,  $\forall n \in \mathbb{N}, n \leq \frac{y}{x}$ . In other words,  $\mathbb{N}$  is bounded above by  $\frac{y}{x}$ . Hence,  $\exists a = \sup \mathbb{N} \in \mathbb{R}$ . Since a is the least upper bound for  $\mathbb{N}$ , a - 1 cannot be an upper bound for  $\mathbb{N}$ . Hence,  $\exists m \in \mathbb{N}$  such that

$$a-1 < m \implies a < m+1 \in \mathbb{N}.$$

However, this is a contradiction, because then a is not an upper bound for  $\mathbb{N}$ . Therefore,  $\exists n \in \mathbb{N}$  such that  $n \geq \frac{y}{x}$ .

- ii) Suppose  $x, y \in \mathbb{R}$  and x < y. Then, there are three cases:
  - 0 < x < y,
  - x < 0 < y, and
  - $x < y \le 0$ .

For the second case, take  $r = 0 \in \mathbb{Q}$ . So, assume that  $0 \le x < y$ . Then, by the Archimedian Property,  $\exists n \in \mathbb{N}$  such that n(y - x) > 1. Again by the Archimedean property,  $\exists l \in \mathbb{N}$  such that l > nx. Thus, consider the set

$$S = \{k \in \mathbb{N} \mid k > nx\}.$$

By the well-ordering property of  $\mathbb{N}$ , S has a least element,  $m \in S \implies nx < m \implies x < \frac{m}{n} \in \mathbb{Q}$ .

Since  $m-1 \notin S, \ m-1 \leq nx \implies m \leq nx+1 < ny$ . Hence,  $\frac{m}{n} < y$ . Therefore,

$$x < \frac{m}{n} < y$$
.

If instead we have  $x < y \le 0$ , then  $0 \le -y < -x \implies \exists \tilde{r} \in \mathbb{Q}$  such that

$$-y < \tilde{r} < x \implies x < -\tilde{r} < y$$

by the previous case.

## Theorem 44

 $1 = \sup \left\{ 1 - \frac{1}{n} \mid n \in \mathbb{N} \right\}.$ 

**Proof**: If  $n \in \mathbb{N}$ , then  $1 - \frac{1}{n} < 1 \implies 1$  is an upper bound of this set. Suppose that x is an upper bound for the set  $\{1 - 1/n \mid n \in \mathbb{N}\}$ . We now prove that  $x \ge 1$ . For the sake of contradiction, assume that x < 1. By the Archimedean property, there exists an  $n \in \mathbb{N}$  such that 1 < n(1-x). Therefore,  $\exists n \in \mathbb{N}$  such that x < 1 - 1/n. Hence, x is not an upper bound for the set  $\{1 - 1/n \mid n \in \mathbb{N}\}$  if x < 1. Thus, if x is an upper bound,  $x \ge 1$ . Therefore,

$$\sup\left\{1 - \frac{1}{n} \mid n \in \mathbb{N}\right\} = 1.$$

We now begin proving some theorems about supremums and infinimums which will make them easier to use.

#### Theorem 45

Suppose that  $S \subset \mathbb{R}$  is nonempty and bounded above. Then,  $x = \sup S$  if and only if

- 1. x is an upper bound for S.
- 2. for all  $\epsilon > 0$ ,  $\exists y \in S$  such that  $x \epsilon < y \le x$ .

**Proof**: This is left as an exercise in Assignment 3.

#### Notation 46

For  $x \in \mathbb{R}$  and  $A \subset \mathbb{R}$ , define

$$x + A := \{x + a \mid a \in A\}$$
$$xA := \{xa \mid a \in A\}.$$

## Theorem 47

Using this new notation, we have the following theorems:

1. If  $x \in \mathbb{R}$  and A is bounded above, then x + A is bounded above and

$$\sup(x+A) = x + \sup A.$$

2. If x > 0 and A is bounded above then xA is bounded above and

$$\sup(xA) = x \sup A.$$

#### **Proof**:

1. Suppose that  $x \in \mathbb{R}$  and A is bounded above. Therefore,  $\sup A \in \mathbb{R}$  by the least upper bound property of  $\mathbb{R}$ . Then,  $\forall a \in A, a \leq \sup A$ . Hence,

$$\forall a \in A, \ x + a \le x + \sup A.$$

Hence,  $x + \sup A$  is an upper bound for x + A. Let  $\epsilon > 0$ . Then,  $\exists y \in A$  such that

$$\sup A - \epsilon < y \le \sup A \implies (x + \sup A) - \epsilon < y + x \le x + \sup A.$$

Therefore, by our previous theorem,  $x + \sup A = \sup(x + A)$ .

2. Suppose that x>0 and A is bounded above. Thus,  $\sup A\in\mathbb{R}$ . Then,  $\forall a\in A,\ a\leq \sup A$  and thus

 $xa \leq x \sup A$ . Hence,  $x \sup A$  is an upper bound of xA. Let  $\epsilon > 0$ . Then  $\exists y \in A$  such that

$$\sup A - \frac{\epsilon}{x} < y \le \sup A \implies x \sup A - \epsilon < xy \le x \sup A.$$

Therefore, by the previous theorem,  $\sup(xA) = x \sup A$ .

#### Theorem 48

Let  $A, B \subset \mathbb{R}$  such that  $\forall x \in A, \forall y \in B, x \leq y$ . Then,  $\sup A \leq \inf B$ .

**Proof**: The proof of this is left to the reader.

## Absolute Value

## **Definition 49**

If  $x \in \mathbb{R}$  we define

$$|x| := \begin{cases} x, & x \ge 0 \\ -x, & x \le 0 \end{cases}.$$

#### Theorem 50

We can prove a bunch of theorems about the absolute value function that we usually take for granted:

- 1)  $|x| \ge 0$  and  $|x| = 0 \iff x = 0$ .
- $2) \ \forall x \in \mathbb{R}, \ |-x| = |x|.$
- 3)  $\forall x, y \in \mathbb{R}, |xy| = |x||y|.$
- 4)  $|x^2| = x^2 = |x|^2$ .
- 5) If  $x, y \in \mathbb{R}$ , then  $|x| \le y \iff -y \le x \le y$ .
- 6)  $\forall x \in \mathbb{R}, x \leq |x|$ .

#### **Proof**:

- 1) If  $x \ge 0$  then  $|x| = x \ge 0$ . If  $x \le 0$ , then  $-x \ge 0 \implies |x| = -x \ge 0$ . Thus,  $|x| \ge 0$ . Now suppose x = 0. Then, |x| = x = 0. For the other direction, suppose |x| = 0. Then, if  $x \ge 0 \implies x = |x| = 0$ . If  $x \le 0$ , then -x = |x| = 0. Therefore,  $x = 0 \iff |x| = 0$ .
- 2) If  $x \ge 0$  then  $-x \le 0$ . Thus, |x| = x = -(-x) = |-x|. If  $x \le 0$  then  $-x \ge 0$  and thus |-x| = |-(-x)| = |x|.
- 3) If  $x \ge 0$  and  $y \ge 0$ , then  $xy \ge 0$  and |xy| = xy = |x||y|. If  $x \le 0$  and  $y \le 0$ , then

$$xy \le 0 \implies |xy| = -xy = (-x)y = |x||y|.$$

- 4) Take x = y in 3). Then,  $|x^2| = |x|^2$ . Since  $x^2 \ge 0$ , it follows that  $|x^2| = x^2$ .
- 5) Suppose  $|x| \le y$ . If  $x \ge 0$ , then  $-y \le 0 \le x = |x| \le y$ . Therefore,  $-y \le x \le y$ . If  $x \le 0$ , then  $-x \ge 0$  and  $|-x| \le y$ . Hence,  $-y \le -x \le y \implies -y \le x \le y$ .
- 6) Take y = |x| in 5).

On its own, these properties of the absolute values may not seem all that useful, but in the next lecture we will prove the extremely important Triangle Inequality.

The Uncountabality of the Real Numbers

**Theorem 51** (Triangle Inequality)

 $\forall x, y \in \mathbb{R},$ 

$$|x+y| \le |x| + |y|.$$

**Proof**: Let  $x, y \in \mathbb{R}$ . Then,  $x + y \le |x| + |y|$  and

$$(-x) + (-y) \le |-x| + |-y| = |x| + |y|.$$

Therefore,  $-(|x|+|y|) \le x+y \le |x|+|y|$ . Hence,

$$|x+y| \le |x| + |y|$$

by our previous theorem.

**Remark 52.** We may denote the Triangle Inequality with  $\triangle$ -inequality as a shorthand.

**Question 53.** As we showed in Assignment 1, we know that  $\mathbb{Q}$  is countable. Is the set of real numbers countable?

#### Recall 54

Recall that a set A is countable if A is either finite or  $|A| = |\mathbb{N}|$ .

We can think of  $\mathbb{Q}$  as decimal expansions. In other words, we can think of a rational number x as being in the form

$$x = 10^k d_k + \dots + 10d_1 + d_0 + 10^{-1} d_{-1} + \dots + 10^{-M} d_{-M}$$

with  $d_i \in \{0, 1, 2, 3, ..., 9\}$ . We may write

$$x = d_k d_{k-1} \dots d_1 d_0 \bullet d_{-1} \dots d_{-M}$$

where • is the decimal point. The same can be said about real numbers if we allow for infinite decimal expansions.

#### **Definition 55**

Let  $x \in (0,1]$  and let  $d_{-j} \in \{0,1,\ldots,9\}$ . We say that x is **represented** by the digits  $\{d_{-j} \mid j \in \mathbb{N}\}$ , i.e.  $x = 0 \bullet d_{-1}d_{-2}\ldots$ , if

$$x = \sup\{10^{-1}d_{-1} + 10^{-2}d_{-2} + \dots + 10^{-n}d_{-n} \mid n \in \mathbb{N}\}.$$

Here is an example:  $.2500 = \sup\{2 \cdot 10^{-1}, 2 \cdot 10^{-1} + 5 \cdot 10^{-2}, 2 \cdot 10^{-1} + 5 \cdot 10^{-2} + 0 \cdot 10^{-3}, \dots\}$ . Notice here that after a while the previous set becomes  $\frac{1}{4}$  repeating. Hence, we have  $.2500 = \sup\{\frac{1}{5}, \frac{1}{4}\} = \frac{1}{4}$ .

#### Theorem 56

For every  $x \in (0,1]$ , there exists a unique sequence of digits  $d_{-j}$  such that  $x = 0 \bullet d_{-1}d_{-2}...$  and

$$0 \bullet d_{-1}d_{-2} \dots d_{-n} < x \le 0 \bullet d_{-1}d_{-2} \dots d_{-n} + 10^{-n}$$
.

Furthermore, for every set of digits  $\{d_{-j} \mid j \in \mathbb{N}\}$ , there exists a unique  $x \in [0,1]$  such that  $x = 0 \bullet d_{-1} \ldots$ 

Notice however that the representative of  $\frac{1}{2}$  is 0.4999...

Theorem 57 (Cantor)

(0,1] is uncountable.

**Proof**: We will prove this through contradiction. Suppose that (0,1] is countable. Therefore, there exists a bijection  $x : \mathbb{N} \to (0,1]$ . We now construct a  $y \in (0,1]$  such that y is not in the range of x. We write

$$x(n) = 0 \bullet d_{-1}^{(n)} d_{-2}^{(n)} \dots$$

These are not exponents! This is the set of digits for a given  $n \in \mathbb{N}$ . In other words, x takes in a natural number n and maps it to the sequence of digits  $\left\{d_{-j}^{(n)} \mid n \in \mathbb{N}\right\}$ . Let

$$e_{-j} = \begin{cases} 1, & d_{-j}^{(j)} \neq 1 \\ 2, & d_{-j}^{(j)} = 1 \end{cases}.$$

Let  $y = 0 \bullet e_{-1}e_{-2}\dots$  Then,  $\forall n \in \mathbb{N}$ ,

$$0 \bullet e_{-1}e_{-2} \dots e_{-n} \le y0 \bullet e_{-1} \dots e_{-n} + 10^{-n}$$

since all  $e_{-j}$ s are positive. Thus,  $0 \bullet e_{-1} \dots$  is the unique decimal expansion of y. However, for all  $n \in \mathbb{N}$ ,  $d_{-n}^{(n)} \neq e_{-n}$ . Therefore,  $\forall n, x(n) \neq y$ . This is a contradiction, and thus (0, 1] is uncountable.

So  $(0,1] \subset \mathbb{R}$  is uncountable!

Corollary 58

The set of real numbers,  $\mathbb{R}$ , is uncountable.

## Sequences and Series

Remark 59. Analysis is the study of limits.

Sequences and Limits

**Definition 60** (Sequence of Reals)

A sequence of real numbers is a function  $x : \mathbb{N} \to \mathbb{R}$ . We denote  $x(n) = x_n$  and we denote the sequence by  $\{x_n\}_{n=1}^{\infty}, \{x_n\}, \text{ or } x_1, x_2, \dots$ 

#### **Definition 61**

A sequence  $\{x_n\}$  is bounded if  $\exists B \geq 0$  such that  $\forall n, |x_n| \leq B$ .

One example of a bounded sequence is  $x_n = \frac{1}{n}$ , since  $\left|\frac{1}{n}\right| \leq 1$  for all  $n \in \mathbb{N}$ . However,  $x_n = n$  is not bounded.

Remark 62. A sequence is different from a set!

For example,

$$-1, 1, -1, 1, \dots = \{(-1)^n\}_{n=1}^{\infty},$$

while

$$\{(-1)^n \mid n \in \mathbb{N}\} = \{-1, 1\}.$$

## **Definition 63** (Sequence Convergence of Reals)

A sequence  $\{x_n\}$  converges to  $x \in \mathbb{R}$  if  $\forall \epsilon > 0$ ,  $\exists M \in \mathbb{N}$  such that  $\forall n \geq M$ ,

$$|x_n - x| < \epsilon$$
.

A sequence that converges is said to be **convergent**, and otherwise is said to be **divergent**. We can also define divergence as the negation of convergent.

## Negation 64 (Not Convergent)

The sequence  $\{x_n\}$  is not convergent, or divergent if  $\exists \epsilon_0 > 0$  such that  $\forall M \in \mathbb{N}, \exists n \geq M$  so that

$$|x_n - x| > \epsilon_0$$
.

We now prove two theorems:

#### Theorem 65

If  $\{x_n\}$  converges for x and y, then x = y. In other words, limits of convergent sequences of real numbers are unique.

## Theorem 66

Let  $x, y \in \mathbb{R}$ . If  $\forall \epsilon > 0$ ,  $|x - y| < \epsilon$ , then x = y.

**Proof**: We first prove the second theorem. Suppose that  $x \neq y$ . Then, |x - y| > 0. Hence, choosing  $\epsilon = \frac{|x - y|}{2}$ , we have

$$|x-y| \le \frac{|x-y|}{2} \implies \frac{|x-y|}{2} < 0$$

which is a contradiction.

Using this we prove the former theorem. Suppose  $x_n$  converges to x and to y. We will show that for all  $\epsilon > 0$ ,  $|x - y| < \epsilon$ . Firstly, given  $x_n \to x$ , for  $\epsilon > 0$  there exists an  $N_1 \in \mathbb{N}$  such that  $\forall n \geq N_1$ ,

$$|x_n - x| < \frac{\epsilon}{2}.$$

Then, given  $x_n \to y$ , for  $\epsilon > 0$  there exists an  $N_2 \in \mathbb{N}$  such that  $\forall n \geq N_2$ ,

$$|x_n - y| < \frac{\epsilon}{2}.$$

Let  $N = \max\{N_1, N_2\}$ . Then, for all  $\epsilon > 0$  there exists an  $N = \max\{N_1, N_2\}$  such that for all  $n \geq N$ ,

$$|x-y| \le |x-x_n| + |x_n-y| < \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon$$

by the Triangle Inequality. Hence, for all  $\epsilon > 0$ ,  $|x - y| < \epsilon$ . Therefore, x = y.

#### Notation 67

We write  $x = \lim_{n \to \infty} x_n$  or  $x_n \to x$ .

## Example 68

Given the sequence  $x_n = c \ \forall n, \lim_{n \to \infty} x_n = c$ .

**Proof**: Let  $\epsilon > 0$  and M = 1. Thus, for all  $n \geq 1$ ,

$$|x_n - c| = |c - c| = 0 < \epsilon.$$

## Example 69

 $\lim_{n\to\infty} \frac{1}{n} = 0.$ 

**Proof**: Let  $\epsilon > 0$ . Choose  $M \in \mathbb{N}$  such that  $M^{-1} > \epsilon^{-1}$ . Hence, for all  $n \ge M$ ,  $\left| \frac{1}{n} - 0 \right| = \frac{1}{n} \le \frac{1}{M} \le \epsilon$ .

## Convergent Sequences of Real Numbers

We will do another example of limits that converge:

## Example 70

 $\lim_{n \to \infty} \frac{1}{n^2 + 2n + 100} = 0.$ 

**Proof**: Let  $\epsilon > 0$  and choose  $M \in \mathbb{N}$  such that  $M > \frac{\epsilon^{-1}}{2}$ . Then,  $\forall n \geq M$ ,

$$\left| \frac{1}{n^2 + 2m + 100} - 0 \right| \le \frac{1}{n^2 + 2m + 100} \le \frac{1}{2n} \le \frac{1}{2M} < \epsilon.$$

The fact that we can go from a complicated rational function to one that works for our purposes (namely to prove the sequence converges to 0) is awesome.

## Example 71

Consider the sequence  $x_n = (-1)^n$ . This sequence is divergent.

**Proof**: Let  $x \in \mathbb{R}$ . We claim  $\lim_{n\to\infty} (-1)^n \neq x$ . To prove this, we simply need find an epsilon that stops the sequence from converging. For instance, consider  $\epsilon_0 = \frac{1}{2}$ . Then, for  $M \in \mathbb{N}$ ,

$$1 = |(-1)^{M} - (-1)^{M+1}| \le |(-1)^{M} - x| + |(-1)^{M+1} - x|.$$

Thus, either  $|(-1)^M - x| \ge \frac{1}{2}$  or  $|(-1)^{M+1} - x| \ge \frac{1}{2}$ . In either case, this shows that the limit cannot converge to x.

## Theorem 72

If  $\{x_n\}$  is convergent, then  $\{x_n\}$  is bounded.

Before we start the proof, let's first talk about the idea of the proof. Let  $\epsilon = 1$  such that  $|x_n - x| < 1$  for all  $n \leq M$  for some  $M \in \mathbb{N}$ . Then, there are finitely many elements not in the interval (x - 1, x + 1). We use this to our advantage.

**Proof**: Suppose that  $\lim_{n\to\infty} x_n = x$ . Thus, there exists an  $M \in \mathbb{N}$  such that  $|x_n - x| < 1$  for all  $n \ge M$ . Let

$$B = \max\{|x_1|, |x_2|, \dots, |x_{M-1}|, |x|+1\}.$$

If n < M, then  $|x_n| \le B$  by construction. If  $n \ge M$ , then

$$|x_n| < |x_n - x| + |x| < 1 + |x| < B.$$

## **Definition 73** (Monotone)

A sequence  $\{x_n\}$  is monotone increasing if  $\forall n \in \mathbb{N}, x_n \leq x_{n+1}$ . A sequence  $\{x_n\}$  is monotone decreasing if  $\forall n \in \mathbb{N}, x_n \geq x_{n+1}$ . If  $\{x_n\}$  is either monotone increasing or monotone decreasing, we say  $\{x_n\}$  is monotone or **monotonic.** 

## Example 74

For example,  $x_n = \frac{1}{n}$  is monotone,  $y_n = -\frac{1}{n}$  is monotone increasing, and  $(-1)^n$  is neither.

## Theorem 75

Let  $\{x_n\}$  be a monotone increasing sequence. Then,  $\{x_n\}$  is convergent if and only if  $\{x_n\}$  is bounded. Moreover,  $\lim_{n\to\infty} x_n = \sup\{x_n \mid n\in\mathbb{N}\}.$ 

**Proof**: Firstly, we know that if  $\{x_n\}$  is convergent then it is bounded by the previous theorem, Now assume that  $\{x_n\}$  is bounded. Then,  $x := \sup\{x_n \mid n \in \mathbb{N}\}$  exists in  $\mathbb{R}$  by the lowest upper bound property of  $\mathbb{R}$ . We now prove that

$$\lim_{n\to\infty} x_n = x.$$

Let  $\epsilon > 0$ . Then,  $\exists M_0 \in \mathbb{N}$  such that

$$x - \epsilon < x_{M_0} < x$$

since x is the supremum of the set. Let  $M = M_0$ . Then,  $\forall n \geq M$ , we have

$$x - \epsilon < x_{M_0} = x_M \le x_n \le x < x + \epsilon$$
.

Therefore,  $|x_n| < |x + \epsilon|$ . Therefore,  $x_n \to x$ .

#### Theorem 76

Let  $\{x_n\}$  be a monotone decreasing function. Then,  $\{x_n\}$  is convergent if and only if  $\{x_n\}$  is bounded. Moreover,

$$\lim_{n \to \infty} x_n = \inf\{x_n \mid n \in \mathbb{N}\}\$$

The proof of this is similar to the previous theorem and is thus omitted.

## **Definition 77** (Subsequence)

Informally, a subsequence is a sequence with entries coming from another given sequence. In other words, let  $\{x_n\}$  be a sequence and let  $\{n_k\}$  be a strictly increasing sequence of natural numbers. Then the sequence

$$\{x_{n_k}\}_{k=1}^{\infty}$$

is called a subsequence of  $\{x_n\}$ .

Consider the sequence  $\{x_n\} = n$  – in other words, the sequence  $1, 2, 3, 4, \ldots$  Then, the following are subsequences of  $x_n$ :

$$1, 3, 5, 7, 9, 11, \dots$$

$$2, 4, 6, 8, 10, \dots$$

$$2, 3, 5, 7, 11, 13, \ldots$$

The first two are described by  $x_{n_k} = x_{2k}$  and  $x_{n_k} = x_{2k-1}$  respectively.

Question 78. How would we describe the third?

Continuing to let  $\{x_n = n\}_n$ , the following are *not* subsequences:

$$1, 1, 1, 1, 1, 1, \dots$$
  
 $1, 1, 3, 3, 5, 5, \dots$ 

Now consider the sequence  $\{(-1)^n\}$ . Then we have the subsequences

$$x_{n_k} = x_{2k-1} \to -1, -1, -1, \dots$$
  
 $y_{n_k} = x_{2k} \to 1, 1, 1, \dots$ 

## Theorem 79

If  $\{x_n\}$  converges to x, then any subsequence of  $x_n$  will converge to x.

**Proof**: Suppose  $\lim_{n\to\infty} x_n = x$ . Let  $\epsilon > 0$ . Then,  $\exists M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0$ ,

$$|x_n - x| < \epsilon$$
.

Choose  $M=M_0$ . If  $k\geq M$ , then  $n_k\geq k\geq M=M_0$ . Hence, for all  $\epsilon>0$  there exists an M such that for all  $n_k>M$ ,

$$|x_{n-k} - x| < \epsilon.$$

**Remark 80.** Notice that this also implies that the sequence  $\{(-1)^n\}_n$  is divergent.

## Notation 81 (DNC)

We can denote the statement "a sequence does not converge"/"a sequence is divergent" as "the sequence DNC".

The Squeeze Theorem and Operations Involving Convergent Sequences

## Facts About Limits

Theorem 82 (Squeeze Theorem)

Let  $\{a_n\}$ ,  $\{b_n\}$ , and  $\{x_n\}$  be sequences such that  $\forall n \in \mathbb{N}$ ,

$$a_n \le x_n \le b_k$$
.

Suppose that  $\{a_n\}$  and  $\{b_n\}$  converge and

$$\lim_{n \to \infty} a_n = x = \lim_{n \to \infty} b_n.$$

Therefore,  $\{x\}$  converges and  $\lim_{n\to\infty} x_n = x$ .

Remark 83. We sometimes abbreviate the Squeeze Theorem to ST.

**Proof**: Let  $\epsilon > 0$ . Since  $\lim_{n \to \infty} a_n = x$ , there exists an  $M_0 \in \mathbb{N}$  such that for all  $n \ge M_0$ ,

$$|a_n - x| < \epsilon \implies x - \epsilon < a_n.$$

Since  $\lim_{n\to\infty} b_n = x$ ,  $\exists M_1 \in \mathbb{N}$  such that  $\forall n \geq M_1$ ,

$$|b_n - x| < \epsilon \implies b_n < x + \epsilon.$$

Choose  $M = \max\{M_0, M_1\}$ . Then, if  $n \geq M$ , then

$$x - \epsilon < a_n < x_n < b_n < x - \epsilon \implies |x_n - x| < \epsilon$$
.

Therefore,  $\{x_n\}$  is convergent and  $\lim_{n\to\infty} x_n = x$ .

#### Theorem 84

Another way to check that a sequence  $x_n \to x$ , is stated below:

$$\lim_{n \to \infty} x_n = x \iff \lim_{n \to \infty} |x_n - x| = 0.$$

Hence, we can consider a sequence like the following:

#### Example 85

Show that

$$\lim_{n\to\infty}\frac{n^2}{n^2+n+1}=1.$$

**Proof**: We have

$$\left|\frac{n^2}{n^2+n+1}-1\right| = \left|\frac{-n-1}{n^2+n+1}\right| = \frac{n+1}{n^2+n+1} \le \frac{n+1}{n^2+n} = \frac{1}{n}.$$

Thus,

$$0 \leq \left| \frac{n^2}{n^2+n+1} - 1 \right| \leq \frac{1}{n} \to 0 \implies \lim_{n \to \infty} \left| \frac{n^2}{n^2+n+1} - 1 \right| = 0$$

## Question 86. How do limits interact with ordering?

## Theorem 87

Let  $\{x_n\}$  and  $\{y_n\}$  be sequences of real numbers. Then,

- 1. if  $\{x_n\}$  and  $\{y_n\}$  are convergent sequences and  $\forall n \in \mathbb{N} \ x_n \leq y_n$ , then  $\lim_{n \to \infty} x_n \leq \lim_{n \to \infty} y_n$ .
- 2. if  $\{x_n\}$  is a convergent sequence and  $\forall n \in \mathbb{N} \ x \leq x_n \leq b_n$  then  $a \leq \lim_{n \to \infty} x_n \leq b$ .

## **Proof**:

1. Let  $x = \lim_{n \to \infty} x_n$  and  $y = \lim_{n \to \infty} y_n$ . Suppose for the sake of contradiction that y < x. Then,  $\exists M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0$ 

$$|y_n - y| < \frac{x - y}{2}$$

And  $\exists M_1 \in \mathbb{N}$  such that for all  $n \geq M_1$ ,

$$|x_n - x| < \frac{x - y}{2}.$$

Then, if  $M = M_0 + M_1 \ge \max\{M_0, M_1\}$ ,

$$y_M < \frac{x-y}{2} + y = \frac{x+y}{2} = x - \frac{x-y}{2} + x < x_M.$$

However, this would imply that  $y_M < x_M$  which contradicts  $\forall n \in \mathbb{N} x_n \leq y_n$ .

2. Apply part 1 to proof part 2, by considering  $y_n = a \le x_n \le b = z_n$  for all  $n \in \mathbb{N}$ .

## Question 88. How do limits interact with algebraic operations?

#### Theorem 89

Suppose  $\lim_{n\to\infty} x_n = x$  and  $\lim_{n\to\infty} y_n = y$ . Then,

- 1.  $\{x_y + y_n\}_n$  is convergent and  $\lim_{n\to\infty} (x_n + y_n) = x + y$ .
- 2.  $\forall c \in \mathbb{R}, \{cx_n\}_n \text{ is convergent and } \lim_{n\to\infty} cx_n = cx.$
- 3.  $\{x_n \cdot y_n\}$  is convergent and  $\lim_{n\to\infty} x_n y_n = xy$ .
- 4. If  $\forall n \in \mathbb{N}, y_n \neq 0$  and  $y \neq 0$ , then  $\{x_n/y_n\}_n$  is convergent and

$$\lim_{n \to \infty} \frac{x_n}{y_n} = \frac{x}{y}.$$

#### **Proof**:

1. Let  $\epsilon > 0$ . Then, since  $x_n \to x$ ,  $\exists M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0$ ,  $|x_n - x| < \frac{\epsilon}{2}$ . Since  $y_n \to y$ ,  $\exists M_1 \in \mathbb{N}$  such that  $\forall n \geq M_1$ ,  $|y_n - y| < \frac{\epsilon}{2}$ . Hence, letting  $M = \max\{M_0, M_1\}$ , we get for all  $n \geq M$ ,

$$|x_n + y_n - (x+y)| \le |x_n - x| + |y_n - y| < \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon.$$

2. Let  $\epsilon > 0$ . Since  $x_n \to x$ ,  $\exists M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0, |x_n - x| < \frac{\epsilon}{|c|+1}$ . Let  $M = M_0$ . Then,  $\forall n \geq M$ ,

$$|cx_n - cx| = |c||x_n - x| \le \frac{|c|}{|c| + 1} \cdot \epsilon < \epsilon$$

since  $\frac{|c|}{|c|+1} < 1$ .

3. Since  $y_n \to y$ ,  $\{y_n\}$  is bounded. In other words,  $\exists B \geq 0$  such that  $\forall n \in \mathbb{N}, |y_n| \leq B$ . Then,

$$|x_n y_n - xy| = |(x_n - x)y_n + (y_n - y)x|$$

$$\leq |x_n - x||y_n + |x||y_n - y|$$

$$\leq B|x_n - x| + |x||y_n - y|.$$

Therefore,  $0 \le |x_n y_n - xy| \le B|x_n - x| + |x||y_n - y|$ . Since  $B|x_n - x| + |x||y_n - y| \to 0$ , by the Squeeze Theorem  $\lim_{n\to\infty} |x_n y_n - xy| = 0$ .

4. We prove  $\frac{1}{y_n} \to \frac{1}{y}$ . We first prove  $\exists b > 0$  such that  $\forall n \in \mathbb{N}, |y_n| \ge b$ . Since  $y_n \to y$  and  $y \ne 0, \exists M_0 \in \mathbb{N}$  such that  $\forall n \ge M_0$ ,

$$|y_n - y| < \frac{|y|}{2}.$$

By the Triangle Inequality,  $\forall n \geq M_0$ ,

$$|y| \le |y_n - y| + |y_n| \le \frac{|y|}{2} + |y_n| \implies |y_n| \ge \frac{|y|}{2}.$$

Let  $b = \min\left\{|y_1|, \dots, |y_{M_0-1}|, \frac{|y|}{2}\right\}$ . Then,  $\forall n \in \mathbb{N}, |y_n| \ge b$ . Therefore,

$$0 \le \left| \frac{1}{y_n} - \frac{1}{y} \right| = \frac{|y_n - y|}{|y_n||y|} \le \frac{1}{b|y|} |y_n - y|.$$

By the Squeeze Theorem,  $\lim_{n\to\infty}\left|\frac{1}{y_n}-\frac{1}{y}\right|=0$ . Therefore,  $\lim_{n\to\infty}\frac{1}{y_n}=\frac{1}{y}$ . Furthermore, by the proof before this (3.), it follows that  $\lim_{n\to\infty}\left(x_n\cdot\frac{1}{y_n}\right)=\frac{x}{y}$ .

Remark 90. By induction, one can prove that

$$\lim_{n \to \infty} (x_n)^k = x^k.$$

## Theorem 91

If  $\{x_n\}$  is a convergent sequence such that  $\forall n \in \mathbb{N}, x_n \geq 0$ , then  $\{\sqrt{x_n}\}$  is convergent and

$$\lim_{n \to \infty} \sqrt{x_n} = \sqrt{\lim_{n \to \infty} x_n}.$$

**Proof**: Let  $x = \lim_{n \to \infty} x_n$ .

<u>Case 1</u>: x = 0. Let  $\epsilon > 0$ . Then, since  $x_n \to 0$ , there exists an  $M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0$ ,  $x_n = |x_n - 0| < \epsilon^2$ . Choose  $M = M_0$ . Then,  $\forall n \geq M$ ,

$$|\sqrt{x_n} - \sqrt{0}| = \sqrt{x_n} < \sqrt{\epsilon^2} = \epsilon.$$

Case 2: x > 0. We have  $\forall n \in \mathbb{N}$ ,

$$|\sqrt{x_n} - \sqrt{x}| = \left| \frac{\sqrt{x_n} - \sqrt{x}}{\sqrt{x_n} + \sqrt{x}} \cdot (\sqrt{x_n} + \sqrt{x}) \right|$$
$$= \frac{1}{\sqrt{x_n} + \sqrt{x}} |x_n - x|$$
$$\leq \frac{1}{\sqrt{x}} |x_n - x|.$$

Hence,

$$0 \le |\sqrt{x_n} - \sqrt{x}| \le \frac{1}{\sqrt{x}} |x_n - x|$$

 $\forall n \in \mathbb{N}$ . Hence, by the Squeeze Theorem,

$$\lim_{n \to \infty} |\sqrt{x_n} - \sqrt{x}| = 0.$$

Remark 92. Why must we do casework in the above proof?

#### Theorem 93

If  $\{x_n\}$  is convergent and  $\lim_{n\to\infty} x_n = x$ , then  $\{|x_n|\}$  is convergent and  $\lim_{n\to\infty} |x_n| = |x|$ .

**Proof**: Firstly, note that  $\forall x \in \mathbb{R}, \sqrt{x^2} = |x|$ . Then,

$$\lim_{n \to \infty} |x_n| = \lim_{n \to \infty} \sqrt{x_n^2} = \sqrt{x^2} = |x|$$

by the previous theorem.

#### Theorem 94

If  $c \in (0,1)$ , then  $\lim_{n\to\infty} c^n = 0$ . If c > 1, then  $\{c^n\}$  is unbounded.

**Proof**: If 0 < c < 1, we claim that  $\forall n \in \mathbb{N}$ ,  $0 < c^{n+1} < c^n < 1$ . We can prove this through induction. Firstly, notice that  $0 < c^2 < c < 1$  since c > 0 and c < 1. Now assume that  $0 < c^{m+1} < c^m$ . Then, multiply by c > 0 to obtain

$$0 < c^{m+1} \cdot c = c^{(m+1)+1} < c^m \cdot c = c^{(m+1)}.$$

By induction, our claim holds. Thus,  $\{c^n\}$  is a monotone decreasing sequence and is bounded below. Thus,  $\{c^n\}$  is convergent. Let  $L = \lim_{n \to \infty} c^n$ . We will prove that L = 0. Let  $\epsilon > 0$ . Then,  $\exists M \in \mathbb{N}$  such that  $\forall n \geq M$ ,  $|c^n - L| < (1 - c)\frac{\epsilon}{2}$ . Therefore,

$$(1-c)|L| = |L - cL| = |L - c^{M+1} + c^{M+1} - cL|$$

$$\leq |L - c^{M+1}| + c|c^M - L|$$

$$< (1-c)\frac{\epsilon}{2} + c(1-c)\frac{\epsilon}{2} < (1-c)\epsilon.$$

Therefore,  $\forall \epsilon > 0$ ,  $|L| < \epsilon \implies L = 0$ .

Now let c > 1. We have to show that  $\forall B \geq 0$ ,  $\exists n \in \mathbb{N}$  such that  $c^n > B$ . Let  $B \geq 0$ . Choose  $n \in \mathbb{N}$  such that  $n > \frac{B}{c-1}$ . Then,

$$c^n = (1 + (1 - c))^n \ge 1 + n(c - 1) \ge n(c - 1) > B.$$

To see why this center inequality is true, see the last theorem shown in Lecture 1.

Limsup, Liminf, and the Bolzano-Weierstrass Theorem

**Theorem 95** (Some Special Sequences)

What follows are some special sequences to have in our toolbox.

- 1. If p > 0, then  $\lim_{n \to \infty} n^{-p} = 0$ .
- 2. If p > 0 then  $p^{\frac{1}{n}} = 1$ .
- 3.  $\lim_{n\to\infty} n^{\frac{1}{n}} = 1$ .

**Proof**:

1. Let  $\epsilon > 0$ . Then, choose  $M > (1/\epsilon)^{1/p}$ . Hence, if  $n \geq M$ ,

$$\left|\frac{1}{n^p} - 0\right| = \frac{1}{|n^p|} \le \frac{1}{M^p} < \epsilon.$$

2. Suppose p > 1. Then,  $p^{1/n} - 1 > 0$  which may be proven by induction. Furthermore, we have

$$p = (1 + (p^{1/n} - 1))^n$$
  
  $\ge 1 + n(p^{1/n} - 1).$ 

Therefore,  $0 < p^{1/n} - 1 \le \frac{p-1}{n}$ . Hence, we may apply the Squeeze Theorem, obtaining  $\lim_{n \to \infty} |p^{1/n} - 1| = 0$ . If p < 1, then

$$\lim_{n \to \infty} p^{1/n} = \lim_{n \to \infty} \frac{1}{(1/p)^{1/n}} = \frac{1}{1} = 1.$$

Furthermore, if p=1 then it is clear that  $\lim_{n\to\infty} p^{1/n}=1$ . Hence, in all cases, the limit is 1.

3. Let  $x_n = n^{1/n} - 1 \ge 0$ . We want to show that  $\lim_{n \to \infty} x_n = 0$ , as this will imply the end result. Notice that

$$n = (1 + x_n)^n = \sum_{j=0}^n \binom{n}{j} x_n^j \ge \binom{n}{2} x_n^2 = \frac{n!}{2(n-2)!} \cdot x_n^2 = \frac{n(n-1)}{2} \cdot x_n^2.$$

Thus, for n > 1,

$$0 \le x_n \le \sqrt{\frac{2}{n-1}} \implies x_n \to 0.$$

Limsup/Liminf

Question 96. Does a bounded sequence have a convergent subsequence?

## **Definition 97** (Limsup/Liminf)

Let  $\{x_n\}$  be a bounded sequence. We define, if the limits exist,

$$\limsup_{n \to \infty} x_n := \lim_{n \to \infty} (\sup\{x_k \mid k \ge n\})$$

$$\liminf_{n \to \infty} x_n := \lim_{n \to \infty} (\inf\{x_k \mid k \ge n\}).$$

These are called the limit superior and limit inferior respectively.

We will now show that these limits always exist.

## Theorem 98

Let  $\{x_n\}$  be a bounded sequence, and let

$$a_n = \sup\{x_k \mid k \ge n\}$$

$$b_n = \inf\{x_k \mid k \ge n\}.$$

Then,

- 1.  $\{a_n\}$  is monotone decreasing and bounded, and  $\{b_n\}$  is monotone increasing and bounded.
- 2.  $\liminf_{n\to\infty} x_n \leq \limsup_{n\to\infty} x_n$ .

## Proof

1. Since,  $\forall \in \mathbb{N}$ ,

$$\{x_k \mid k \ge n+1\} \subseteq \{x_k \mid k \ge n\},\$$

we have that  $a_{n+1} = \sup\{x_k \mid k \ge n + 1\} \le \sup\{x_k \mid k \ge n\} = a_n$ .

Similarly,  $\forall n \in \mathbb{N}, b_{n+1} \geq b_n$ . Given  $\{x_n\}$  is a bounded sequence,  $\exists B \geq 0$  such that  $\forall n \in \mathbb{N}$ ,

$$-B < x_n < B$$
.

Therefore,  $\forall n \in \mathbb{N}$ ,

$$-B < b_n < a_n < B$$

which implies both sequences are bounded.

2. By the above equation,  $\forall n \in \mathbb{N}, b_n \leq a_n \implies \liminf_{n \to \infty} x_n = \lim_{n \to \infty} b_n \leq \lim_{n \to \infty} a_n = \limsup_{n \to \infty} x_n$ .

Let's consider a few examples.

#### Example 99

Let  $x_n = (-1)^n$ . Calculate the lim inf and lim sup of this sequence.

**Proof**: Notice that  $\{(-1)^k \mid l \geq n\} = \{-1, 1\}$ . Thus, the supremum of these sets is always 1 and the infimum is always -1. Therefore,

$$\limsup_{n\to\infty} x_n = 1$$
 and  $\liminf_{n\to\infty} x_n = -1$ .

## Example 100

Let  $x_n = \frac{1}{n}$ . Calculate the liminf and lim sup of this sequence.

**Proof**: We may do this directly:

$$\sup\{1/k \mid k \ge n\} = \frac{1}{n} \to 0 \implies \limsup_{n \to \infty} x_n = 0.$$
$$\inf\{1/k \mid k \ge n\} = 0 \to 0 \implies \liminf_{n \to \infty} x_n = 0.$$

The limit inferior and the limit superior allow us to answer the question posed at the beginning of this section.

#### Theorem 101

Let  $\{x_n\}$  be a bounded sequence. Then, there exists subsequences  $\{x_{n_k}\}$  and  $\{x_{m_k}\}$  such that

$$\lim_{k \to \infty} x_{n_k} = \limsup_{n \to \infty} x_n$$
$$\lim_{k \to \infty} x_{m_k} = \limsup_{n \to \infty} x_n.$$

**Proof**: Let  $a_n = \sup\{x_k \mid k \geq n\}$ . Then,  $\exists n_1 \in \mathbb{N}$  such that  $a_1 - 1 < x_{n_1} \leq a_1$ . Now,  $\exists n_2 > n_1$  such that

$$a_{n_1+1} - \frac{1}{2} < x_{n_2} \le a_{n_1+1}$$

since

$$a_{n+1} = \sup\{x_k \mid k \ge n_1 + 1\}.$$

Similarly,  $\exists n_3 > n_2$  such that

$$a_{n_2+1} - \frac{1}{3} < x_{n_3} \le a_{n_2+1}.$$

Continuing in this way, we obtain a sequence of integers  $n_1 < n_2 < n_3 < \dots$  such that

$$a_{n_k+1} - \frac{1}{k+1} < x_{n_k} \le a_{n_k+1}.$$

Given  $\lim_{k\to\infty} a_{n_k+1} = \limsup_{n\to\infty} x_n$ , by the Squeeze Theorem,

$$\lim_{k \to \infty} x_{n_k} = \limsup_{n \to \infty} x_n.$$

The direction for the liminf works out the same way so that portion of the proof is left to the reader.

#### **Theorem 102** (Bolzano-Weierstrass)

Every bounded sequence has a convergent subsequence.

Remark 103. We may abbreviate the Bolzano-Weierstrass theorem to B-W.

**Proof**: This follows immediately from the previous theorem, but is so important that it itself is a theorem.  $\Box$ 

## Notation 104

When it is clear, we may have the following notational shorthand:  $\liminf_{n\to\infty} x_n := \liminf x_n$ , and  $\limsup_{n\to\infty} x_n := \limsup x_n$ .

## Theorem 105

Let  $\{x_n\}$  be a bounded sequence. Then,  $\{x_n\}$  converges if and only if  $\liminf x_n = \limsup x_n$ .

**Proof** ( $\iff$ ) Suppose  $\liminf x_n = \limsup x_n$ . Then,  $\forall n \in \mathbb{N}$ ,

$$\inf\{x_k \mid k \ge n\} \le x_n \le \sup\{x_k \mid k \ge n\}.$$

By the Squeeze Theorem, since  $\lim_{k\to\infty}\inf\{x_k\mid k\geq n\}=\lim_{k\to\infty}\sup\{x_k\mid k\geq n\}$  by assumption, we have

$$\lim_{n\to\infty} x_n = \liminf x_n = \limsup x_n.$$

Therefore,  $x_n$  converges.

( $\Longrightarrow$ ) Let  $x=\lim_{n\to\infty}x_n$ . Therefore, every subsequence of  $\{x_n\}$  converges to x, so  $\liminf x_n=x$  and  $\limsup x_n=x$  by a theorem we proved in Lecture 7. Hence,  $\liminf x_n=\limsup x_n$ .

The Completeness of the Real Numbers and Basic Properties of Infinite Series

## Cauchy Sequences

## **Definition 106**

Cauchy A sequence  $\{x_n\}$  is Cauchy if  $\forall \epsilon > 0 \ \exists M \in \mathbb{N}$  such that for all  $n, k \geq M$ ,

$$|x_n - x_k| < \epsilon.$$

## Example 107

Show the sequence  $x_n = \frac{1}{n}$  is Cauchy.

**Proof**: Let  $\epsilon > 0$  and choose  $M \in \mathbb{N}$  such that  $\frac{1}{M} < \frac{\epsilon}{2}$ . Then, if  $n, k \geq M$ , then

$$\left|\frac{1}{n} - \frac{1}{k}\right| \leq \frac{1}{n} + \frac{1}{k} \leq \frac{2}{M} < \epsilon.$$

## Negation 108 (Not Cauchy)

By the negation of the definition, a sequence  $\{x_n\}$  is not Cauchy if  $\exists \epsilon_0 > 0$  such that for all  $M \in \mathbb{N}$ ,  $\exists n, k \geq M$  such that  $|x_n - x_k| \geq \epsilon_0$ .

## Example 109

Show the sequence  $x_n = (-1)^n$  is not Cauchy.

**Proof**: Choose  $\epsilon = 1$  and let  $M \in \mathbb{N}$ . Choose n = M and k = M + 1. Then,

$$|(-1)^n - (-1)^k| = 2 > 1.$$

#### Theorem 110

If  $\{x_n\}$  is Cauchy, then  $\{x_n\}$  is bounded.

**Proof**: If  $\{x_n\}$  is Cauchy then  $\exists M \in \mathbb{N}$  such that for all  $n, k \geq M$ ,

$$|x_n - x_k| < 1.$$

Then, for all  $n \geq M$ ,  $|x_n - x_M| < 1$ . Hence,

$$|x_n| < |x_n - x_M| + |x_M| < |x_M| + 1.$$

Let  $B = |x_1| + \dots + |x_M| + 1$ . Then, for all  $n \in \mathbb{N}$ ,  $|x_n| \le B$ .

## Theorem 111

If  $\{x_n\}$  is Cauchy and a subsequence  $\{x_{n_k}\}$  converges, then  $\{x_n\}$  converges.

**Proof**: Suppose that  $\{x_{n_k}\}$  is a subsequence of  $\{x_n\}$  such that  $\lim_{k\to\infty} x_{n_k} = x$ . We claim that  $x_n \to x$ . Let  $\epsilon > 0$ . Since  $x_{n_k} \to x$ , there exists  $M_0 \in \mathbb{N}$  such that  $\forall k \geq M_0$ ,

$$|x_{n_k} - x| < \frac{\epsilon}{2}.$$

Since  $\{x_n\}$  is Cauchy, there exists an  $M_1 \in \mathbb{N}$  such that for all  $n \geq M_1$  and  $m \geq M_1$ ,

$$|x_n - x_m| < \frac{\epsilon}{2}.$$

Choose  $M = M_0 + M_1$ . If  $n \ge M$ , then  $n_M \ge M \ge M_0$  and  $n \ge M_1$ . Therefore,

$$|x_n - x| \le |x_n - x_{n_M}| + |x_{n_M} - x| < \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon.$$

#### Theorem 112

A sequence of real numbers  $\{x_n\}$  is Cauchy if and only if  $\{x_n\}$  is convergent.

**Proof**: ( $\Longrightarrow$ ) If  $\{x_n\}$  is Cauchy, then  $\{x_n\}$  is bounded. Therefore,  $\{x_n\}$  has a convergent subsequence by Bolzano-Weierstrass. By the previous theorem, we thus have that  $\{x_n\}$  is convergent.

( $\iff$ ) Suppose that  $\{x_n\}$  is convergent and  $x = \lim_{n \to \infty} x_n$ . Let  $\epsilon > 0$ . Since  $x_n \to x$ ,  $\exists M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0$ ,

$$|x_n - x| < \frac{\epsilon}{2}.$$

Choose  $M = M_0$ . Then, if  $n, k \geq M$ ,

$$|x_n - x_k| \le |x_n - x| + |x_k - x| < \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon.$$

Therefore,  $\{x_n\}$  is Cauchy.

## **Series**

Remark 113. Series were the original motivation for analysis.

## Definition 114

Given  $\{x_n\}$ , the symbol  $\sum_{n=1}^{\infty} x_n$  or  $\sum x_n$  is the series associated to  $\{x_n\}$ . We say  $\sum x_n$  converges if the sequence

$$\left\{ s_m = \sum_{n=1}^m x_n \right\}_{m=1}^{\infty}$$

converges. We call the terms of  $\{s_m\}$  the partial sums. If  $\lim_{m\to\infty} s_m = s$ , we write  $s = \sum x_n$  and treat  $\sum x_n$  as a number.

**Remark 115.** A series need not start at n = 1.

## Example 116

 $\sum_{n=1}^{\infty} \frac{1}{n(n+1)}$  converges.

**Proof**: We may do show this directly by consider the partial sums:

$$s_m = \sum_{n=1}^m \frac{1}{n(n+1)} = \sum_{n=1}^m \frac{1}{n} - \frac{1}{n+1}$$
$$= \left(1 + \frac{1}{2} + \dots + \frac{1}{m}\right) - \left(\frac{1}{2} + \dots + \frac{1}{m+1}\right)$$
$$= 1 - \frac{1}{m+1}.$$

Thus,  $s_m = 1 - \frac{1}{m+1} \to 1$ . Hence, the partial sums converge and thus the series converges.

## Theorem 117

If |r| < 1 then  $\sum_{n=0}^{\infty} r^n$  converges and

$$\sum_{n=0}^{\infty} r^n = \frac{1}{1-r}.$$

**Proof**: We have  $\forall m \in \mathbb{N}$ ,

$$s_m = \sum_{n=0}^{m} r^n = \frac{1 - r^{m+1}}{1 - r}$$

by induction. Since |r| < 1,  $\lim_{m \to \infty} |r|^{m+1} = 0$ . Therefore,

$$\lim_{m \to \infty} s_m = \frac{1 - 0}{1 - r} = \frac{1}{1 - r}.$$

**Remark 118.** Series of the form  $\sum_{n=0}^{\infty} \alpha(r)^n$  for  $\alpha \in \mathbb{R}$  and  $r \in \mathbb{R}$  are called geometric series.

## Theorem 119

Let  $\{x_n\}$  be a sequence and let  $M \in \mathbb{N}$ . Then,  $\sum_{n=1}^{\infty} x_n$  converges if and only if  $\sum_{n=M}^{\infty} x_n$  converges.

**Proof**: The partial sums satisfy, for all  $m \in \mathbb{N}$ ,

$$\sum_{n=1}^{m} x_n = \sum_{n=M}^{m} x_n + \sum_{n=1}^{M} x_n.$$

## **Definition 120**

 $\sum x_n$  is Cauchy if the sequence of partial sums is Cauchy.

## Theorem 121

 $\sum x_n$  is Cauchy  $\iff \sum x_n$  is convergent.

**Proof**: This follows by the analogous theorem for regular sequences of real numbers proven earlier.

## Theorem 122

 $\sum x_n$  is Cauchy if and only if  $\forall \epsilon > 0$ ,  $\exists M \in \mathbb{N}$  such that for all  $m \geq M$  and  $\ell > m$ ,

$$\left| \sum_{n=m+1}^{\ell} x_n \right| < \epsilon.$$

**Proof**: ( $\Longrightarrow$ ) Suppose  $\sum x_n$  is Cauchy. Let  $\epsilon > 0$ . Then,  $\exists M_0 \in \mathbb{N}$  such that  $\forall m, \ell \geq M_0$ ,

$$|s_m - s_\ell| < \epsilon$$
.

Choose  $M = M_0$ . Then, if  $m \ge M$  and  $\ell > m$ , then

$$\left| \sum_{n=m+1}^{\ell} x_n \right| = |s_{\ell} - s_m| < \epsilon.$$

The other direction is left as an exercise.

#### Theorem 123

If  $\sum x_n$  converges then  $\lim_{n\to\infty} x_n = 0$ .

**Proof**: Suppose  $\sum x_n$  converges. Then,  $\sum x_n$  is Cauchy. Let  $\epsilon > 0$ . Since  $\sum x_n$  is Cauchy,  $\exists M_0 \in \mathbb{N}$  such that for all  $\ell > m \ge M_0$ ,

$$\left| \sum_{n=m+1}^{\ell} x_n \right| < \epsilon.$$

Choose  $M = M_0 + 1$ . Then, if  $m \ge M \implies m - 1 \ge M_0$ . Therefore,

$$|x_m| = \left| \sum_{n=m}^m x_n \right| < \epsilon$$

by taking  $\ell = m$ .

## Theorem 124

If  $|r| \geq 1$ , then  $\sum_{n=0}^{\infty} r^n$  diverges.

**Proof**: If  $|r| \ge 1$ , then  $\lim_{m \to \infty} r^m \ne 0$ . Therefore,  $\sum_{n=0}^{\infty} r^n$  diverges, as if this wasn't the case then  $\lim_{m \to \infty} r^m = 0$  by the previous theorem which is a contradiction.

## Corollary 125

The series  $\sum_{n=0}^{\infty} \alpha(r)^n$  converges if and only if |r| < 1.

Absolute Convergence and the Comparison Test for Series

#### Recall 126

Last time we showed that if  $\sum x_n$  converges then  $\lim_{n\to\infty} x_n = 0$ .

**Question 127.** Is the converse true? Does  $\lim_{n\to\infty} x_n = 0 \implies \sum x_n$  converges?

## Theorem 128

The series  $\sum_{n=1}^{\infty} \frac{1}{n}$  does not converge.

**Proof**: We will show that there exists a subsequence of  $s_m = \sum_{n=1}^m \frac{1}{n}$  which is unbounded, which will imply the series diverges. Consider, for  $\ell \in \mathbb{N}$ ,

$$s_{2\ell} = \sum_{n=1}^{2^{\ell}} \frac{1}{n}.$$

Then.

$$\begin{split} s_{2\ell} &= 1 + \left(\frac{1}{2}\right) + \left(\frac{1}{3} + \frac{1}{4}\right) + \left(\frac{1}{5} + \dots + \frac{1}{8}\right) + \dots \left(\frac{1}{2^{\ell-1} + 1} + \dots + \frac{1}{2^{\ell}}\right) \\ &= 1 + \sum_{\lambda=1}^{\ell} \sum_{n=2^{\lambda-1} + 1}^{2^{\lambda}} \frac{1}{n} \\ &\geq 1 + \sum_{\lambda=1}^{\ell} \sum_{n=2^{\lambda-1} + 1}^{2^{\lambda}} \frac{1}{2^{\lambda}} \\ &= 1 + \sum_{\lambda=1}^{\ell} \frac{1}{2^{\lambda}} (2^{\lambda} - (2^{\lambda-1} + 1) + 1) \\ &= 1 + \sum_{\lambda=1}^{\ell} \frac{2^{\lambda-1}}{2^{\lambda}} \\ &= 1 + \frac{\ell}{2}. \end{split}$$

Thus,  $\{s_{2^\ell}\}_{\ell=1}^{\infty}$  is unbounded which implies  $\{s_{2^\ell}\}$  does not converge.

Remark 129. The series  $\sum \frac{1}{n}$  is called the harmonic series.

## Theorem 130

Let  $\alpha \in \mathbb{R}$  and  $\sum x_n$  and  $\sum y_n$  be convergent series. Then the series  $\sum (\alpha x_n + y_n)$  converges and

$$\sum (\alpha x_n + y_n) = \alpha \sum x_n + \sum y_n.$$

**Proof**: The partial sums satisfy

$$\sum_{n=1}^{m} (\alpha x_n + y_n) = \alpha \sum_{n=1}^{m} x_n + \sum_{n=1}^{m} y_n.$$


By linear properties of limits, it follows that

$$\lim_{m \to \infty} \sum_{n=1}^{m} (\alpha x_n + y_n) = \alpha \sum_{n=1}^{\infty} x_n + \sum_{n=1}^{\infty} y_n.$$

Series with non-negative terms are easier to work with than general series as then  $\{s_n\}$  is a monotone sequence.

## Theorem 131

If  $\forall n \in \mathbb{N} \ x_n \geq 0$ , then  $\sum x_n$  converges if and only if  $\{s_m\}$  is bounded.

**Proof**: If  $x_n \geq 0$  for all  $n \in \mathbb{N}$  then

$$s_{m+1} = \sum_{n=1}^{m+1} x_n = \sum_{n=1}^{m} x_n + x_{m+1} = s_m + x_{m+1} \ge s_m$$

Thus,  $\{s_m\}$  is a monotone increasing sequence. Therefore,  $\{s_m\}$  converges if and only if  $\{s_m\}$  is bounded.

## Definition 132

 $\sum x_n$  converges absolutely if  $\sum |x_n|$  converges.

## Theorem 133

If  $\sum x_n$  converges absolutely then  $\sum x_n$  converges.

**Proof**: Suppose  $\sum |x_n|$  converges. We will then show that  $\sum x_n$  is Cauchy.

Claim:  $\forall m \geq 2$ ,  $|\sum_{n=1}^m x_n| \leq \sum_{n=1}^m |x_n|$ . We prove this claim by induction. For m=2, this states that  $|x_1+x_2| \leq |x_1|+|x_2|$ , which follows by the Triangle Inequality. Suppose for all  $\left|\sum_{n=1}^\ell x_n\right| \leq \sum_{n=1}^\ell |x_n|$ . Then,

$$\left| \sum_{n=1}^{\ell+1} x_n \right| \le \left| \sum_{n=1}^{\ell} x_n \right| + |x_{\ell+1}| \le \sum_{n=1}^{\ell} |x_n| + |x_{\ell+1}| = \sum_{n=1}^{\ell+1} |x_n|.$$

We now prove that  $\sum x_n$  is Cauchy. Let  $\epsilon > 0$ . Since  $\sum |x_n|$  converges,  $\sum |x_n|$  is Cauchy. Therefore, there exists an  $M_0 \in \mathbb{N}$  such that for all  $\ell > m \ge M_0$ ,

$$\sum_{n=m+1}^{\ell} |x_n| < \epsilon.$$

Choose  $M = M_0$ . Then, for all  $\ell > m \ge M$ ,

$$\left| \sum_{n=m+1}^{\ell} x_n \right| \le \sum_{n=m+1}^{\ell} |x_n| < \epsilon.$$

Hence,  $\sum x_n$  is Cauchy, and thus converges.

**Remark 134.** We will see that  $\sum_{n=1}^{\infty} \frac{(-1)^n}{n}$  is convergent but not absolutely convergent.

Notice that it is immediately clear that this series is not absolutely convergent as  $\sum \left| \frac{(-1)^n}{n} \right| = \sum \frac{1}{n}$  (the harmonic series), which doesn't converge.

## Convergence tests

**Theorem 135** (Comparison Test)

Suppose for all  $n \in \mathbb{N}$   $0 \le x_n \le y_n$ . Then,

- 1. if  $\sum y_n$  converges, then  $\sum x_n$  converges.
- 2. if  $\sum x_n$  diverges, then  $\sum y_n$  diverges.

#### **Proof**:

1. If  $\sum y_n$  converges, then  $\{\sum_{n=1}^m y_n\}_{m=1}^\infty$  is bounded. In other words, there exists a  $B \geq 0$  such that for all  $m \in \mathbb{N}$ ,

$$\sum_{n=1}^{m} y_n \le B.$$

Thus, for all  $m \in \mathbb{N}$ ,  $\sum_{n=1}^{m} x_n \leq \sum_{n=1}^{m} y_n \leq B$ . Therefore, the partial sums of  $\{x_n\}$  are bounded, which implies  $\sum x_n$  converges.

2. If  $\sum x_n$  diverges, then  $\{\sum_{n=1}^m x_n\}_{m=1}^\infty$  is unbounded. We now prove that

$$\left\{\sum_{n=1}^{m} y_n\right\}_{m=1}^{\infty}$$

is also unbounded. Let  $B \geq 0$ . Then,  $\exists m \in \mathbb{N}$  such that

$$\sum_{n=1}^{m} x_n \ge B.$$

Therefore,  $\sum_{n=1}^{m} y_n \ge \sum_{n=1}^{m} x_n \ge B$ . Thus,  $\{\sum_{n=1}^{m} y_n\}_{m=1}^{\infty}$  is unbounded, which implies  $\sum y_n$  diverges.

Remark 136. We will see that geometric series and the Comparison Test imply everything!

Theorem 137

For  $p \in \mathbb{R}$ , the series  $\sum_{n=1}^{\infty} \frac{1}{n^p}$  converges if and only if p > 1.

**Proof**: ( $\Longrightarrow$ ) We prove this direction through contradiction. Suppose  $\sum_{n=1}^{\infty} \frac{1}{n^p}$  converges and  $p \le 1$ . Then,  $\frac{1}{n^p} \ge \frac{1}{n}$ , and  $\sum \frac{1}{n}$  diverges. Therefore, by the Comparison Test,  $\sum \frac{1}{n^p}$  also diverges. Hence, if  $\sum \frac{1}{n^p}$  converges, then p > 1.

 $(\Leftarrow)$  Suppose p > 1. We first prove that a subsequence of the partial series is bounded.

Claim 1:  $\forall k \in \mathbb{N}, s_{2^k} \leq 1 + \frac{1}{1 - 2^{-(p-1)}}$ . Proof:

$$\begin{split} s_{2^k} &= 1 + \sum_{\ell=1}^k \sum_{n=2^{\ell-1}+1}^{2^\ell} \frac{1}{n^p} \\ &\leq 1 + \sum_{\ell=1}^k \sum_{n=2^{\ell-1}+1}^{2^\ell} \frac{1}{(2^{\ell-1}+1)^p} \\ &\leq 1 + \sum_{\ell=1}^k 2^{-p(\ell-1)} (2^\ell - (2^{\ell-1}+1)+1) \\ &= 1 + \sum_{\ell=1}^k 2^{-(p-1)(\ell-1)} \\ &= 1 + \sum_{\ell=0}^{k-1} 2^{-(p-1)\ell} \\ &\leq 1 + \sum_{\ell=0}^\infty 2^{-(p-1)\ell} \\ &= 1 + \frac{1}{1 - 2^{-(p-1)}} \end{split}$$

using the fact that p-1>0, and using properties of geometric series. Thus, Claim 1 is proven. Claim 2:  $\{s_m = \sum_{n=1}^m \frac{1}{n^p}\}$  is bounded. Proof: Let  $m \in \mathbb{N}$ . Since  $2^m > m$ , we have that

$$s_m = \sum_{n=1}^m \frac{1}{n^p} \le \sum_{n=1}^{2^m} n^{-p} \le 1 + \frac{1}{1 - 2^{-(p-1)}}.$$

Hence, the partial sums are bounded, which implies  $\{s_m\}$  converges.

## The Ratio, Root, and Alternating Series Tests

We continue our study of convergence tests.

Theorem 138 (Ratio test)

Suppose  $x_n \neq 0$  for all n and

$$L = \lim_{n \to \infty} \frac{|x_{n+1}|}{|x_n|}$$

exists. Then,

1. if L < 1 then  $\sum x_n$  converges absolutely.

2. if L > 1 then  $\sum x_n$  diverges.

**Proof**: We will first prove the second part of this theorem.

2) Suppose L > 1 and  $\alpha \in (1, L)$ . Then, there exists  $M_0 \in \mathbb{N}$  such that for all  $N \geq M_0$ ,  $\frac{|x_{n+1}|}{|x_n|} \geq \alpha \geq 1$ . Thus, for all  $n \geq M_0$ ,

$$|x_{n+1}| \ge |x_n| \implies \lim_{n \to \infty} |x_n| \ne 0.$$

Therefore,  $\sum x_n$  diverges.

1) Now suppose that L < 1. Let  $\alpha \in (L,1)$ . Then, there exists  $M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0, \frac{|x_{n+1}|}{|x_n|} < \alpha$ . Therefore,  $\forall n \geq M_0, |x_{n+1}| \leq \alpha |x_n|$ . In other words, for all  $n \geq M_0$ ,

$$|x_n| \le \alpha |x_{n-1}| \le \alpha^2 |x_{n-2}| \le \dots \le \alpha^{n-M_0} |x_{M_0}|.$$

Let  $m \in \mathbb{N}$ . Then,

$$\sum_{n=1}^{m} |x_n| = \sum_{n=1}^{M_0 - 1} |x_n| + \sum_{n=M_0}^{m} |x_n|$$

$$\leq \sum_{n=1}^{M_0 - 1} |x_n| + |x_{M_0}| \sum_{n=M_0}^{m} \alpha^{n - M_0}$$

$$\leq \sum_{n=1}^{M_0 - 1} |x_n| + |x_{M_0}| \sum_{\ell=0}^{\infty} \alpha^{\ell}$$

$$= \sum_{n=1}^{M_0 - 1} |x_n| + \frac{|x_{M_0}|}{1 - \alpha}.$$

Therefore,  $\left\{\sum_{n=1}^{m}|x_n|\right\}_{m=1}^{\infty}$  is bounded, and thus  $\sum|x_n|$  converges. Hence,  $x_n$  is absolutely convergent.

Let's consider two examples where we can use the Ratio test.

Example 139

Show the series  $\sum_{n=1}^{\infty} \frac{(-1)^n}{n^2+1}$  converges absolutely.

**Proof**: Notice

$$\left|\frac{(-1)^n}{n^2+1}\right| \leq \frac{1}{n^2+1} < \frac{1}{n^2},$$

and hence

$$\lim_{n \to \infty} \left| \frac{\frac{(-1)^{n+1}}{(n+1)^2 + 1}}{\frac{(-1)^n}{n^2 + 1}} \right| < \lim_{n \to \infty} \frac{n^2}{(n+1)^2} = 1.$$

Example 140

Show that  $\forall x \in \mathbb{R}, \sum_{n=0}^{\infty} \frac{x^n}{n!}$  converges absolutely.

**Proof**: This immediately follows from the Ratio test, noting that

$$\lim_{n \to \infty} \frac{|x|^{n+1}}{(n+1)!} \cdot \frac{n!}{|x|^n} = \lim_{n \to \infty} \frac{|x|}{n+1} = 0.$$

**Remark 141.** As seen above, the Ratio test can be really helpful to use when we have a  $(-1)^n$  or a factorial in the argument. Also note that if L=1 then we the test doesn't apply.

Theorem 142 (Root test)

Let  $\sum x_n$  be a series and suppose that

$$L = \lim_{n \to \infty} |x_n|^{1/n}$$

exists. Then

1. if L < 1 then  $\sum x_n$  converges absolutely.

2. if L > 1 then  $\sum x_n$  diverges.

Proof:

1. Suppose L < 1. Let L < r < 1. Then, since  $|x_n|^{1/n} \to L$ ,  $\exists M \in \mathbb{N}$  such that  $\forall n \geq M$ ,  $|x_n|^{1/n} < r$ . Therefore, for all  $n \geq M$ ,  $|x_n| \leq r^n$ . Thus, for all  $m \in \mathbb{N}$ ,

$$\sum_{n=1}^{m} |x_n| = \sum_{n=1}^{M-1} |x_n| + \sum_{n=M}^{m} |x_n|$$

$$\leq \sum_{n=1}^{M-1} |x_n| + \sum_{n=M}^{m} r^n$$

$$\leq \sum_{n=1}^{M-1} |x_n| + \sum_{n=M}^{\infty} r^n$$

$$= \sum_{n=1}^{M-1} |x_n| + \frac{r^M}{1-r}.$$

Thus,  $\left\{\sum_{n=1}^{m}|x_n|\right\}_{m=1}^{\infty}$  is bounded, and thus  $\sum|x_n|$  converges.

2. Suppose L > 1. Then, since  $|x_n|^{1/n} \to L > 1$ , there exists an  $M \in \mathbb{N}$  such that for all  $n \ge M$ ,  $|x_n|^{1/n} > 1$ . In other words, for all  $n \ge M$ ,  $|x_n| > 1$ . Therefore,  $\lim_{n \to \infty} x_n \ne 0$ , and thus  $\sum x_n$  diverges.

**Remark 143.** Again, note that if L = 1 then the test doesn't apply.

## Theorem 144 (Alternating Series test)

Let  $\{x_n\}$  be a monotone decreasing sequence such that  $x_n \to 0$ . Then,  $\sum (-1)^n x_n$  converges.

**Proof**: Let  $s_m = \sum_{n=1}^m (-1)^n x_n$ . Then,

$$s_{2k} = \sum_{n=1}^{2k} (-1)^n x_n$$

$$= (x_2 - x_1) + (x_4 - x_3) + \dots + (x_{2k} - x_{2k-1})$$

$$\geq (x_2 - x_1) + \dots + (x_{2k} - x_{2k-1}) + (x_{2k+2} - x_{2k+1})$$

$$= s_{2(k+1)}$$

as  $\{x_n\}$  is a monotone decreasing sequence. Thus,  $\{s_{2k}\}_{k=1}^{\infty}$  is monotone decreasing. Furthermore,

$$s_{2k} = -x_1 + (x_2 - x_3) + (x_4 - x_5) + \dots + (x_{2k-2} - x_{2k-1}) + x_{2k} \ge -x_1.$$

In other words,  $\{s_{2k}\}$  is a bounded below monotone decreasing sequence. Thus,  $\{s_{2k}\}_{k=1}^{\infty}$  converges. Let  $s = \lim_{k \to \infty} s_{2k}$ . We now prove  $\{s_m\}_{m=1}^{\infty}$  converges to s.

Let  $\epsilon > 0$ . Since  $s_{2k} \to s$ ,  $\exists M_0 \in \mathbb{N}$  such that for all  $k \geq M_0$ ,

$$|s_{2k} - s| < \frac{\epsilon}{2}.$$

Since  $x_n \to 0$ ,  $\exists M_1 \in \mathbb{N}$  such that  $\forall n \geq M_1$ ,

$$|x_n| < \frac{\epsilon}{2}.$$

Choose  $M = \max\{2M_+0+1, M_1\}$ . Suppose  $m \ge M$ . If m is even, then  $\frac{m}{2} \ge M_0 + 1/2 \ge M_0$ . Therefore,

$$|s_m - s| = |s_{2, \frac{m}{2}} - s| < \frac{\epsilon}{2} < \epsilon.$$

If m is odd, let  $k = \frac{m-1}{2}$  so m = 2k+1. Then,  $m \ge M \implies k \ge M_0$  and  $m \ge M_1$ . Then,

$$\begin{aligned} |s_m - s| &= |s_{m-1} + x_m - s| \\ &\leq |s_{2k} - s + x_m| \\ &\leq |s_{2k} - s| + |x_m| < \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon. \end{aligned}$$

Thus,  $s_m \to s$ , and thus  $\sum (-1)^n x_n$  converges.

## Corollary 145

We already showed that  $\sum \frac{(-1)^n}{n}$  does not absolutely converge. However,  $\sum \frac{(-1)^n}{n}$  converges.

**Proof**: This follows immediately from the Alternating Series test.

## Theorem 146

Suppose  $\sum x_n$  converges absolutely and  $\sum x_n = x$ . Let  $\sigma : \mathbb{N} \to \mathbb{N}$  be a bijective function. Then,  $\sum x_{\sigma(n)}$  is absolutely convergent and  $\sum x_{\sigma(n)} = x$ . In other words, absolute convergence implies if we rearrange the sequence the new series will still converge to the same value of the original series.

**Proof**: We first show  $\sum |x_{\sigma(n)}|$  converges, which is equivalent to showing the partial sums  $\sum_{n=1}^{m} |x_{\sigma(n)}|$  is bounded.

Since  $\sum x_n$  converges,  $\exists B \geq 0$  such that for all  $\ell \in \mathbb{N}$ ,

$$\sum_{n=1}^{\ell} |x_n| \le B.$$

Let  $m \in \mathbb{N}$ . Then,  $\sigma(\{1,\ldots,m\})$  is a finite subset of  $\mathbb{N}$ . Thus, there exists an  $\ell \in \mathbb{N}$  such that

$$\sigma(\{1,\ldots,m\})\subset\{1,\ldots,\ell\}.$$

Thus,

$$\sum_{n=1}^{m} |x_{\sigma(n)}| = \sum_{n \in \sigma(\{1, \dots, m\})} |x_n| \le \sum_{n=1}^{\ell} |x_n| \le B.$$

Therefore,  $\sum |x_{\sigma(n)}|$  converges. Let  $x = \sum_{n=1}^{\infty} x_n$ , and let  $\epsilon > 0$ . Then,  $\exists M_0 \in \mathbb{N}$  such that  $\forall m \geq M_0$ ,

$$\left| \sum_{n=1}^{m} x_n - x \right| < \frac{\epsilon}{2}.$$

Since  $\sum |x_n|$  converges,  $\exists M_1 \in \mathbb{N}$  such that for all  $\ell > m \geq M_1$ ,

$$\sum_{n=m+1}^{\ell} |x_n| < \frac{\epsilon}{2}.$$

Let  $M_2 = \max\{M_0, M_1\}$ . Then,  $\forall \ell > m \geq M_2$ ,

$$\left| \sum_{n=1}^{m} x_n - x \right| < \frac{\epsilon}{2} \text{ and } \sum_{n=m+1}^{\ell} |x_n| < \frac{\epsilon}{2}.$$

Since  $\sigma^{-1}(\{1,\ldots,M_2\})$  is a finite set,  $\exists M_3 \in \mathbb{N}$  such that

$$\{1, \ldots, M_2\} \subset \sigma(\{1, \ldots, M_3\}).$$

Choose  $M = M_3$ . Thus, if  $m' \geq M$ ,

$$\left| \sum_{n'=1}^{m'} x_{\sigma(n')} - x \right| = \left| \sum_{n \in \sigma(\{1, \dots, m'\})} x_n - x \right|$$

$$= \left| \sum_{n=1}^{M} x_n - x + \sum_{n \in \sigma(\{1, \dots, m'\}) \setminus \{1, \dots, M\}} x_n \right|$$

$$\leq \left| \sum_{n=1}^{M} x_n - x \right| + \sum_{n=M+1}^{\max \sigma(\{1, \dots, m'\})} |x_n|$$

$$\leq \left| \sum_{n=1}^{M} x_n - x \right| + \sum_{n=M+1}^{\ell} |x_n|$$

$$\leq \left| \sum_{n=1}^{M} x_n - x \right| + \sum_{n=M+1}^{\ell} |x_n|$$

$$\leq \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon.$$

**Limits of Functions** 

## **Continuous Functions**

**Remark 147.** Continuous functions are those functions where <u>tolerable</u> changes to <u>outputs</u> accompany sufficiently <u>small</u> differences of inputs.

## **Limits of Functions**

## **Definition 148** (Cluster Point)

Let  $S \subset \mathbb{R}$ .  $x \in \mathbb{R}$  is a cluster point of S if  $\forall \delta > 0$ ,  $(x - \delta, x + \delta) \cap S \setminus \{x\} \neq \emptyset$ .

Let's look at some examples.

- 1.  $S = \{1/n \mid n \in \mathbb{N}\}$ . Here, 0 is a clusterpoint of S.
- 2. S = (0, 1). The set of cluster points of S is [0, 1].
- 3.  $S = \mathbb{Q}$ . The set of cluster points of S is  $\mathbb{R}$ .
- 4.  $S = \{0\}$ . There are no cluster points of S.
- 5.  $S = \mathbb{Z}$ . There are no cluster points of S.

#### Theorem 149

Let  $S \subset \mathbb{R}$ . Then, x is a cluster point of S if and only if there exists a sequence  $\{x_n\}$  of elements in  $S \setminus \{x\}$  such that  $x_n \to x$ .

## **Definition 150** (Function Convergence)

Let  $S \subset \mathbb{R}$ , let c be a cluster point of S, and  $f: S \to \mathbb{R}$ . We say that f(x) converges to  $L \in \mathbb{R}$  at c if  $\forall \epsilon > 0$   $\exists \delta > 0$  such that if  $x \in S$  and  $0 < |x - c| < \delta$ , then  $|f(x) - L| < \epsilon$ .

#### Notation 151

Notationally, we may write  $f(x) \to L$  as  $x \to c$ , or  $\lim_{x \to c} f(x) = L$ .

#### Theorem 152

Let c be a cluster point of  $S \subset \mathbb{R}$ , and let  $f: S \to \mathbb{R}$ . If  $f(x) \to L_1$  and  $f(x) \to L_2$  as  $x \to c$ , then  $L_1 = L_2$ .

**Proof**: We will show  $\forall \epsilon > 0$ ,  $|L_1 - L_2| < \epsilon$ . Let  $\epsilon > 0$ . Then, since  $f(x) \to L_1$  and  $f(x) \to L_2$ ,  $\exists \delta_1$  such that if  $x \in S$  and  $0 < |x - c| < \delta_1$  then

$$|f(x) - L_1| < \epsilon/2$$

and  $\exists \delta_2 > 0$  such that if  $x \in S$  and  $0 < |x - c| < \delta_2$ , then

$$|f(x) - L_2| < \epsilon/2.$$

Let  $\delta = \min\{\delta_1, \delta_2\} > 0$ . Then, since c is a cluster point of  $S, \exists x_0 \in S$  such that

$$0 < |x_0 - c| < \delta \implies |L_1 - L_2| = |L_1 - f(x_0) + f(x_0) + L_2| \le |L_1 - f(x_0)| + |f(x_0) - L_2| < \epsilon.$$

Let's see some examples of limits of functions.

## Example 153

Let f(x) = ax + b. Then, for all  $c \in \mathbb{R}$ ,  $\lim_{x \to c} f(x) = ac + b$ .

**Proof**: Let  $\epsilon > 0$ . Choose  $\delta = \frac{\epsilon}{1+|a|}$ . Then, if  $x \in \mathbb{R}$  and  $0 < |x-c| < \delta$ , then

$$|f(x) - (ac + b)| = |a(x - c)|$$

$$= |a||x - c|$$

$$< |a|\delta$$

$$= \frac{|a|}{1 + |a|}\epsilon < \epsilon.$$

## Example 154

Let  $f(x) = \sqrt{x}$ . Then,  $\forall c > 0$ ,  $\lim_{x \to c} f(x) = \sqrt{c}$ .

**Proof**: Let  $\epsilon > 0$ . Choose  $\delta = \epsilon \sqrt{c}$ . Then, if x > 0 and  $0 < |x - c| < \delta$ , then

$$|f(x) - \sqrt{c}| = |\sqrt{x} - \sqrt{c}|$$

$$= \left| \frac{(\sqrt{x} - \sqrt{c})(\sqrt{x} + \sqrt{c})}{\sqrt{x} + \sqrt{c}} \right|$$

$$= \frac{|x - c|}{\sqrt{x} + \sqrt{c}}$$

$$\leq \frac{|x - c|}{\sqrt{c}}$$

$$< \frac{\delta}{\sqrt{c}} = \epsilon.$$

## Example 155

Let  $f(x) = \begin{cases} 1 & x \neq 0 \\ 2 & x = 0 \end{cases}$ . Then,  $\lim_{x \to 0} f(x) = 1$ . Notably,  $\lim_{x \to 0} f(x) \neq f(0)$ !

**Proof**: Let  $\epsilon > 0$  and choose  $\delta = 1$ . Then, if 0 < |x - 0| < 1 then  $x \neq 0 \implies$ 

$$|f(x) - 1| = |1 - 1| = 0 < \epsilon.$$

Question 156. How do limits of functions relate to limits of sequences?

#### Theorem 157

Let  $S \subset \mathbb{R}$ , c a cluster point of S, and let  $f: S \to \mathbb{R}$ . Then, the following are equivalent:

- 1.  $\lim_{x\to c} f(x) = L$  and
- 2. for every sequence  $\{x_n\}$  in  $S \setminus \{c\}$  such that  $x_n \to c$ , we have  $f(x_n) = L$ .

**Proof**: (1.  $\Longrightarrow$  2.): Suppose  $\lim_{x\to c} f(x) = L$ . Let  $\{x_n\}$  be a sequence in  $S\setminus\{c\}$  such that  $x_n\to c$ . We want to show that  $f(x_n)\to L$ . Let  $\epsilon>0$ . Given  $\lim_{x\to c} f(x_n)=L$ ,  $\exists \delta>0$  such that if  $x\in S$  and  $0<|x-c|<\delta$  then  $|f(x)-L|<\epsilon$ . Since  $x_n\to c$ ,  $\exists M_0\in\mathbb{N}$  such that  $\forall n\geq M_0,\ 0<|x_n-c|<\delta$ .

Choose  $M = M_0$ . Then,  $\forall n \geq M$ , if  $0 < |x_n - c| < \delta$  then  $|f(x_n) - L| < \epsilon$ . Thus,  $f(x_n) \to L$ .

(2.  $\iff$  1.): Suppose 2. holds, and assume for the sake of contradiction that 1) is false. Then,  $\exists \epsilon_0 > 0$  such that  $\forall \delta > 0$ ,  $\exists x \in S$  such that

$$0 < |x - c| < \delta$$
 and  $|f(x) - L| \ge \epsilon_0$ .

Then,  $\forall n \in \mathbb{N}, \exists x_n \in S \text{ such that } 0 < |x_n - c| < \frac{1}{n} \text{ and } |f(x_n) - L| \ge \epsilon_0$ . By the Squeeze Theorem applied to

$$0 < |x_n - c| < \frac{1}{n},$$

 $x_n \to c$ . Then, by 2.,

$$0 = \lim_{n \to \infty} |f(x_n) - L| \ge \epsilon_0$$

which is a contradiction.

## Limits of Functions in Terms of Sequences and Continuity

## Theorem 158

For all  $c \in \mathbb{R}$ ,  $\lim_{x \to c} x^2 = c^2$ .

**Proof**: Let  $\{x_n\}$  be a sequence in  $\mathbb{R} \setminus \{c\}$  such that  $x_n \to c$ . Then,  $x_n^2 \to c^2$  by a theorem shown in Lecture 8. Thus,

$$\lim_{x \to c} x^2 = c^2.$$

#### Theorem 159

We show that

- 1.  $\lim_{x\to 0} \sin(1/x)$  does not exist, and
- 2.  $\lim_{x\to 0} x \sin(1/x) = 0$ .

## **Proof**:

1. Let  $x_n = \frac{2}{(2n-1)\pi}$ . Then,  $x_n \neq 0$ , and  $x_n \to 0$ . But,

$$\sin(1/x_n) = \sin\left(\frac{(2n-1)\pi}{2}\right) = (-1)^{n+1}$$

for all n. However, this sequence does not converge (i.e. the limit does not exist).

2. Suppose  $x_n \neq 0$  and  $x_n \rightarrow 0$ . Then,

$$0 \le |x_n \sin(1/x_n)| = |x_n||\sin(1/x_n)| \le |x_n|.$$

By the Squeeze Theorem,  $\lim_{n\to\infty} |x_n \sin(1/x_n)| = 0$ .

We can use the 'sequential limit' characterization to prove analogs of previous theorems for limits of sequences.

## Theorem 160

Let  $S \subset \mathbb{R}$ , c a cluster point of S, and  $f,g: S \to \mathbb{R}$ . Suppose  $\forall x \in S$ ,  $f(x) \leq g(x)$  and  $\lim_{x \to c} f(x)$  and  $\lim_{x \to c} g(x)$  exist. Then,

$$\lim_{x\to c} f(x) \leq \lim_{x\to c} g(x).$$

**Proof**: Let  $L_1 = \lim_{x \to c} f(x)$  and  $L_2 = \lim_{x \to c} g(x)$ . Let  $\{x_n\}$  be a sequence in  $S \setminus \{c\}$  such that  $x_n \to c$ . Then,  $\forall n \in \mathbb{N}, f(x_n) \leq g(x_n)$ . Therefore,

$$L_1 = \lim_{n \to \infty} f(x_n) \le \lim_{n \to \infty} g(x_n) = L_2.$$

Similarly, we have analogs of the Squeeze Theorem, limits of algebraic operations, and limits of absolute values. You may read the end of Section 3.1.3 [L] for this.

## **Definition 161**

Let  $S \subset \mathbb{R}$  and suppose c is a cluster point of  $S \cap (-\infty, c)$ . Then, we say f(x) converges to L as  $x \to c^-$  if  $\forall \epsilon > 0 \; \exists \delta > 0$  such that if  $x \in S$  and  $c - \delta < x < c$  then  $|f(x) - L| < \epsilon$ .

#### Notation 162

This is denoted  $L = \lim_{x \to c^-} f(x)$ .

#### **Definition 163**

Similarly, let  $S \subset \mathbb{R}$  and suppose c is a cluster point of  $S \cap (c, \infty)$ . Then, we say f(x) converges to L as  $x \to c^+$  if  $\forall \epsilon > 0 \ \exists \delta > 0$  such that if  $x \in S$  and  $c < x < c + \delta$  then  $|f(x) - L| < \epsilon$ .

#### Notation 164

This is denoted  $L = \lim_{x \to c^+} f(x)$ .

## Example 165

Let 
$$f(x) = \begin{cases} 1 & x > 0 \\ 0 & x < 0 \end{cases}$$
. Then,

$$\lim_{x \to 0^{-}} f(x) = 0 \text{ and } \lim_{x \to 0^{+}} f(x) = 1,$$

even though f(0) is undefined.

#### Theorem 166

Let  $S \subset \mathbb{R}$  and let c be a cluster point of  $S \cap (-\infty, c)$  and  $S \cap (c, \infty)$ . Then, c is a cluster point of S. Moreover,

$$\lim_{x\to c} f(x) = L \iff \lim_{x\to c^-} f(x) = \lim_{x\to c^+} f(x) = L.$$

#### **Continuous Functions**

As we have seen, limits do not care about f(x) when x = c. Continuity is a condition that connects  $\lim_{x\to c} f(x)$  with f(c).

## **Definition 167** (Continuous Functions)

Let  $S \subset \mathbb{R}$  and let  $c \in S$ . We say f is continuous at c if  $\forall \epsilon > 0 \ \exists \delta > 0$  such that if  $x \in S$  and  $|x - c| < \delta$  then  $|f(x) - f(c)| < \epsilon$  We say f is continuous on U for  $U \subset S$  if f is continuous at every point in U.

#### Example 168

f(x) = ax + b is continuous on  $\mathbb{R}$ .

**Proof**: Let  $\epsilon > 0$  and choose  $\delta = \frac{\epsilon}{1+|a|}$ . If  $|x-c| < \delta$ , then

$$|f(x) - f(c)| = |ax + b - (ac + b)|$$

$$= |a||x - c|$$

$$< |a|\delta$$

$$= \frac{|a|}{1 + |a|} \epsilon < \epsilon.$$

## Example 169

Show that  $f(x) = \begin{cases} 1 & x \neq 0 \\ 2 & x = 0 \end{cases}$  is *not* continuous at c = 0.

First we write the negation of the definition of continuity.

## Negation 170 (Not Continuous)

f is not continuous at c if  $\exists \epsilon_0$  such that for all  $\delta > 0$ ,  $\exists x \in S$  such that  $|x - c| < \delta$  and  $|f(x) - f(c)| \ge \epsilon_0$ .

**Proof**: Choose  $\epsilon_0 = 1$  and let  $\delta > 0$ . Then,  $x = \frac{\delta}{2}$  satisfies  $|x - 0| < \delta$  and

$$|f(x) - f(0)| = |2 - 1| \ge 1 = \epsilon_0.$$


The Continuity of Sine and Cosine and the Many Discontinuities of Dirichlet's Function

#### Theorem 171

Let  $S \subset \mathbb{R}$ ,  $c \in S$ , and  $f: S \to \mathbb{R}$ . Then,

- 1. if c is not a cluster point of f, then f is continuous at c.
- 2. if c is a cluster point of S, then f is continuous at c if and only if  $\lim_{x\to c} f(x) = f(c)$ .
- 3. f is continuous at c if and only if for every sequence  $\{x_n\}$  of elements of S such that  $x_n \to c$ , we have  $f(x_n) \to f(c)$ .

#### **Proof**:

- 1. Let  $\epsilon > 0$ . Since c is not a cluster point of S,  $\exists \delta_0 > 0$  such that  $(c \delta_0, c + \delta_0) \cap S = \{c\}$ . Choose  $\delta = \delta_0$ . If  $x \in S$  and  $|x c| < \delta \implies x = c \implies |f(x) f(c)| = 0 < \epsilon$ . Therefore, f is continuous at c.
- 2. This part of the theorem is left as an exercise (or read the short proof in the book).
- 3. ( $\Longrightarrow$ ) Suppose f is continuous at c. Let  $\{x_n\}$  be a sequence such that  $x_n \to c$ . Let  $\epsilon > 0$ . Since f is continuous at c,  $\exists \delta > 0$  such that if  $x \in S$  and  $|x c| < \delta$  then  $|f(x) f(c)| < \epsilon$ . Since  $x_n \to c$ ,  $\exists M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0$ ,  $|x_n c| < \delta$ . Choose  $M = M_0$ . Then,  $\forall n \geq M$ ,

$$|x_n - c| < \delta \implies |f(x_n) - f(c)| < \epsilon.$$

Thus,  $f(x_n) \to f(c)$ .

( $\Leftarrow$ ) Suppose that for every sequence  $\{x_n\}$  of elements of S such that  $x_n \to c$ , we have that  $f(x_n) \to f(c)$ . We will work towards a contradiction. Suppose f(x) is not continuous at c. Then,  $\exists \epsilon_0$  such that  $\forall \delta > 0$   $\exists x \in S$  such that  $|x - c| < \delta$  and  $|f(x) - f(c)| \ge \epsilon_0$ .

Thus,  $\forall n \in \mathbb{N}, \exists x_n \in S \text{ such that } |x_n - c| < \frac{1}{n} \text{ and }$ 

$$|f(x_n) - f(c)| \ge \epsilon_0.$$

Thus, by the Squeeze Theorem,  $|x_n - c| \to 0 \implies x_n \to c$ . Therefore,

$$0 = \lim_{n \to \infty} |f(x_n) - f(c)| \ge \epsilon_0$$

which is a contradiction.

#### Theorem 172

The functions  $f(x) = \sin x$  and  $g(x) = \cos x$  are continuous functions on  $\mathbb{R}$ .

**Proof**: From their definitions in terms of the unit circle, we have that  $\sin^2(x) + \cos^2(x) = 1$ . Also note the following:

- 1.  $\forall x \in \mathbb{R}, |\sin x| \le 1 \text{ and } |\cos x| \le 1$
- 2.  $\forall x \in \mathbb{R}, |\sin x| \le |x|$

#### 3. The angle formulae:

$$\sin(a+b) = \cos(a)\sin(b) + \sin(a)\cos(b) \quad \text{and} \quad \sin(a) - \sin(b) = 2\sin\left(\frac{a-b}{2}\right)\cos\left(\frac{a+b}{2}\right).$$

We now show that  $\sin x$  is continuous on  $\mathbb{R}$ . Let  $\epsilon > 0$ . Choose  $\delta = \epsilon$ . Then, if  $|x - c| < \delta$ , then

$$|\sin x - \sin c| = 2\left|\sin\frac{x-c}{2}\cos\frac{x+c}{2}\right| \le 2\left|\sin\frac{x-c}{2}\right| \le 2\frac{|x-c|}{2} = |x-c| < \delta = \epsilon.$$

Therefore,  $\sin x$  is continuous on  $\mathbb{R}$ . We now show that  $\cos x$  is continuous. Recall that  $\forall x \in \mathbb{R}$ ,  $\cos x = \sin(x + \pi/2)$ . Let  $c \in \mathbb{R}$  and let  $\{x_n\}$  be a sequence such that  $x_n \to c$ . Then,  $x_n + \pi/2 \to c + \pi/2$ . Since  $\sin x$  is continuous on  $\mathbb{R}$ ,

$$\lim_{n \to \infty} \cos x_n = \lim_{n \to \infty} \sin \left( x_n + \frac{\pi}{2} \right) = \sin \left( c + \frac{\pi}{2} \right) = \cos c.$$

Therefore,  $\cos x$  is continuous on  $\mathbb{R}$ .

#### Theorem 173

Let f be a polynomial, in other words let f be of the form

$$f(x) = a_d x^d + \dots + a_1 x + a_0.$$

Then, f is continuous on all of  $\mathbb{R}$ .

**Proof**: Let  $c \in \mathbb{R}$  and let  $\{x_n\}$  be a sequence such that  $x_n \to c$ . Then, by the limit theorem for sequences,

$$\lim_{n \to \infty} f(x_n) = \lim_{n \to \infty} (a_d x^d + \dots + a_1 x + a_0)$$

$$= a_d (\lim_{n \to \infty} x_n)^d + \dots + a_1 (\lim_{n \to \infty} x_n) + a_0$$

$$= a_d c^d + \dots + a_1 c + a_0$$

$$= f(c).$$

Thus, f is continuous at c for all  $c \in \mathbb{R}$ .

#### Theorem 174

If  $f:S\to\mathbb{R},\,g:S\to\mathbb{R}$  are continuous at  $c\in S,$  then

- 1. f + g is continuous at c,
- 2.  $f \cdot g$  is continuous at c,
- 3. and if  $\forall x \in S \ g(x) \neq 0$ , then  $\frac{f}{g}$  is continuous at c.

**Proof**: These proofs are left to the reader.

#### Theorem 175

Let  $A, B \subset \mathbb{R}$ ,  $f: B \to \mathbb{R}$ ,  $g: A \to B$ . Then, if g is continuous at c and f is continuous at g(c), then  $f \circ g$  is continuous at c.

**Proof**: Suppose  $x_n \to c$ . Then,  $g(x_n) \to g(c)$ , and thus

$$f(g(x_n)) \to f(g(c)).$$

## Example 176

These theorems allow us to say that some functions are continuous without a huge  $\epsilon - \delta$  proof:

i)  $\frac{1}{x^2}$  is continuous on  $(0,\infty)$ . This follows as  $g(x)=x^2$  is continuous on  $(0,\infty)$  and thus  $\frac{1}{g(x)}=1/x^2$  is continuous on  $(0,\infty)$ .

ii)  $(\cos \frac{1}{x^2})^2$  is continuous on  $(0, \infty)$ . This follows as  $\cos x$  is continuous on  $\mathbb{R}$ , and thus  $g(x) = \cos(1/x^2)$  is continuous on  $(0, \infty)$ . Furthermore, since  $f(x) = x^2$  is continuous on  $\mathbb{R}$ ,  $(f \circ g)(x) = (\cos 1/x^2)^2$  is continuous on  $(0, \infty)$ .

**Question 177.** Let  $f: \mathbb{R} \to \mathbb{R}$  be a function. Does there exists a point  $c \in \mathbb{R}$  such that f is continuous at c?

## Theorem 178

The function

$$f(x) = \begin{cases} 1 & x \in \mathbb{Q} \\ 0 & x \notin \mathbb{Q} \end{cases}$$

is not continuous on all of  $\mathbb{R}$ . This function is called the **Dirichlet function**.

**Proof**: We have two cases:  $c \in \mathbb{Q}$  or  $c \notin \mathbb{Q}$ .

1.  $c \in \mathbb{Q}$ . For each  $n \in \mathbb{N}$ ,  $\exists x_n \notin \mathbb{Q}$  such that  $c < x_n < c + 1/n$ , and thus  $x_n \to c$  but  $f(x_n) = 1$  for all n so

$$1 = \lim_{n \to \infty} f(x_n) \neq f(c) = 0.$$

2.  $c \notin \mathbb{Q}$ . Similarly, for each  $n \in \mathbb{N}$ ,  $\exists x_n \in \mathbb{Q}$  such that  $c < x_n < c + 1/n$ , and thus  $x_n \to c$  but  $f(x_n) = 0$  for all n so

$$0 = \lim_{n \to \infty} f(x_n) \neq f(c) = 1.$$

## The Min/Max Theorem and Bolzano's Intermediate Value Theorem

As we will see in today's lecture, continuous functions are well behaved on closed intervals of the form [a,b], with f([a,b]) = [e,f] for some  $e,f \in \mathbb{R}$ .

## **Definition 179** (Bounded Functions)

A function  $f: S \to \mathbb{R}$  is bounded if  $\exists B \geq 0$  such that for all  $x \in S$ ,

$$|f(x)| \leq B$$
.

#### Theorem 180

If  $f:[a,b]\to\mathbb{R}$  is continuous then f is bounded.

**Proof**: Suppose for the sake of contradiction that  $f:[a,b]\to\mathbb{R}$  is continuous and f is unbounded. Then,  $\forall n\in\mathbb{N}$ ,  $\exists x_n\in[a,b]$  such that  $|f(x_n)|\geq n$ . By the Bolzano-Weierstrass theorem,  $\exists$  a subsequence  $\{x_{n_k}\}_k$  of  $\{x_n\}_n$  and an  $x\in\mathbb{R}$  such that  $x_{n_k}\to x$ . Since  $a\leq x_{n_k}\leq b$  for all  $k, a\leq x\leq b$ . Given f is continuous at x by assumption,

$$f(x) = \lim_{k \to \infty} f(x_{n_k}) \implies |f(x)| = \lim_{k \to \infty} |f(x_{n_k})|$$

Therefore,  $\{|f(x_{n_k})|\}$  is bounded, and thus  $\{n_k\}$  is bounded since  $n_k \leq |f(x_{n_k})|$ . But by the definition of a subsequence, we must have  $k \leq n_k$  for all k, contradicting the boundedness of  $\{n_k\}$ .

## **Definition 181** (Absolute Minimum/Maximum)

Let  $f: S \to \mathbb{R}$ . Then, f achieves an absolute minimum at c if  $\forall x \in S$ ,  $f(x) \geq f(c)$ . Similarly, f achieves an absolute maximum at d if  $\forall x \in S$ ,  $f(x) \leq f(d)$ .

## **Theorem 182** (Min-Max Theorem)

Let  $f:[a,b]\to\mathbb{R}$ . If f is continuous, then f achieves an absolute maximum and absolute minimum.

**Remark 183.** Note that this is also called the Extreme Value Theorem or EVT for short, though to stay consistent with the Lebl's book I will be calling it the Min-Max theorem.

**Proof**: We will prove this for the absolute maximum. If f is continuous, then f is bounded by the previous theorem. Thus, the set

$$E = \{ f(x) \mid x \in [a, b] \}$$

is bounded above. Let  $L = \sup E$ . Then,

1. L is an upper bound for E, i.e.

$$\forall x \in [a, b], \ f(x) \le L.$$

2. There exists a sequence  $\{f(x_n)\}_n$  with  $x_n \in [a,b]$  such that  $f(x_n) \to L$ .

By the Bolzano-Weierstrass theorem, there exists a subsequence  $\{x_{n_k}\}_k$  of  $\{x_n\}$  and  $d \in [a, b]$  such that  $x_{n_k} \to d$  as  $k \to \infty$ . Hence,

$$f(d) = \lim_{k \to \infty} f(x_{n_k}) = \lim_{n \to \infty} f(x_n) = L$$

by the continuity of f. Thus, f achieves an absolute maximum at d.

We leave the absolute minimum proof to the reader.

Remark 184. As students of mathematics, we also care about the necessity of the hypotheses!

For example, what if  $f:[a,b]\to\mathbb{R}$  is not continuous? Does the Min-Max theorem apply? The answer is **no**. Consider

$$f(x) = \begin{cases} \frac{1}{2} & x = 0, 1\\ x & x \in (0, 1) \end{cases}.$$

Here, f neither achieves an absolute maximum nor an absolute minimum on [0,1].

What if  $f: S \to \mathbb{R}$  and S is not closed and bounded? Does the Min-Max theorem apply? Again, the answer is **no**. Consider  $f(x) = \frac{1}{x} - \frac{1}{1-x}$  on S = (0,1). Even though f is continuous on S, f neither achieves an absolute minimum nor an absolute maximum.

So far we have shown that if  $f:[a,b]\to\mathbb{R}$  is continuous, then  $f([a,b])\subset[f(c),f(d)]$  where f achieves an absolute minimum at c and an absolute maximum at d.

**Question 185.** Does f achieve all values in f(c) and f(d)?

The answer is yes, by Bolzano's Intermediate Value Theorem as we will show.

#### Theorem 186

Let  $f:[a,b]\to\mathbb{R}$ . If f(a)<0 and f(b)>0, then  $\exists c\in(a,b)$  such that f(c)=0.

**Proof**: We prove this using a bisection method. Let  $a_1 = a$  and  $b_1 = b$ , and define  $a_2, b_2$  as follows: If  $f((a_1 + b_1)/2) \ge 0$ , define  $a_2 = a_1, b_2 = \frac{a_1 + b_1}{2}$ . If  $f((a_1 + b_1)/2) < 0$ , define  $a_2 = \frac{a_1 + b_1}{2}$  and  $b_2 = b_1$ . In general, if we know  $a_n, b_n$ , we choose  $a_{n+1}$  and  $b_{n+1}$  as follows: If  $f((a_n + b_n)/2) \ge 0$ , define  $a_{n+1} = a_n, b_2 n + 1 = \frac{a_n + b_n}{2}$ . If  $f((a_n + b_n)/2) < 0$ , define  $a_{n+1} = \frac{a_n + b_n}{2}$  and  $b_{n+1} = b_n$ . Thus, we have:

- 1.  $\forall n \in \mathbb{N}, \ a \le a_n \le a_{n+1} \le b_{n+1} \le b_n \le b$ .
- 2.  $\forall n \in \mathbb{N}, b_{n+1} a_{n+1} = \frac{b_n a_n}{2}.$
- 3.  $\forall n \in \mathbb{N}, f(a_n) < 0 \text{ and } f(b_n) > 0.$

By 1.,  $\{a_n\}$  and  $\{b_n\}$  are monotone increasing and monotone decreasing respectively, both of which are bounded. Thus,  $\exists c, d \in [a, b]$  such that  $a_n \to c$  and  $b_n \to d$ . By 2.,

$$b_n - a_n = \frac{b_{n-1} - a_{n-1}}{2} = \frac{1}{4}(b_{n-2} - a_{n-2}) = \dots = \frac{1}{2^{n-1}}(b - a).$$

Thus,

$$d - c = \lim_{n \to \infty} (b_n - a_n) = \lim_{n \to \infty} \frac{1}{2^{n-1}} (b - a) = 0 \implies d = c.$$

Therefore,  $\lim_{n\to\infty} a_n = \lim_{n\to\infty} b_n = c$ . By 3.,  $f(c) = \lim_{n\to\infty} f(a_n) \le 0$  and  $f(c) = \lim_{n\to\infty} f(b_n) \ge 0$ . Therefore, f(c) = 0.

## Theorem 187 (Bolzano IVT)

Let  $f:[a,b] \to \mathbb{R}$  be continuous. If f(a) < f(b), and  $y \in (f(a),f(b))$ ,  $\exists c \in (a,b)$  such that f(c) = y. If f(b) < f(a) and  $g \in (f(b),f(a))$ ,  $\exists c \in (a,b)$  such that f(c) = y.

Remark 188. This is known as the Intermediate Value Theorem or IVT for short.

**Proof**: Suppose f(a) < f(b). Let  $y \in (f(a), f(b))$ . Define g(x) = f(x) - y. Then,  $g : [a, b] \to \mathbb{R}$  is continuous, g(a) = f(a) - y < 0 and g(b) = f(b) - y > 0. Therefore, by the previous theorem,  $\exists c \in (a, b)$  such that g(c) = 0. Therefore,  $\exists c \in (a, b)$  such that  $g(c) = f(c) - y = 0 \implies f(c) = y$ .

The other direction is analogous.

#### Theorem 189

Let  $f:[a,b]\to\mathbb{R}$  be continuous. let  $c\in[a,b]$  be where f achieves an absolute minimum and  $d\in[a,b]$  be where f achieves an absolute maximum. Then,

$$f([a,b]) = [f(c), f(d)].$$

In other words, every value between the absolute minimum value and the absolute maximum value is achieved.

**Proof**: We know that  $f([a,b]) \subseteq [f(c),f(d)]$ . Hence, we prove the other direction. By the IVT applied to  $f:[c,d] \to \mathbb{R}$ ,

$$[f(c), f(d)] \subseteq f([c, d]) \subseteq f([a, b]).$$

Therefore, f([a,b]) = [f(c), f(d)].

Of course, Bolzano IVT is false if we assume f is not continuous (as can be seen by the following diagram):

## Theorem 190

The polynomial  $f(x) = x^{2021} + x^{2020} + 9.03x + 1$  has at least one real root.

**Proof**: Notice that f(0) = 1 > 0 and f(-1) = -1 + 1 - 9.03 + 1 = -8.03 < 0. Thus, by IVT,  $\exists c \in (-1,0)$  such that f(c) = 0.

Uniform Continuity and the Definition of the Derivative

## **Uniform Continuity**

## Recall 191

Recall the definition of continuity:  $f: S \to \mathbb{R}$  is continuous on S if  $\forall c \in S$  and  $\forall \epsilon > 0$ ,  $\exists \delta = \delta(\epsilon, c) > 0$  such that  $\forall x \in S$ ,  $|x - c| < \delta \implies |f(x) - f(c)| < \epsilon$ .

Here,  $\delta(\epsilon, c)$  denotes the fact that  $\delta$  can depend on  $\epsilon$  and c.

## Example 192

Consider the function  $f(x) = \frac{1}{x}$ . f is continuous on (0,1).

**Proof**: Let  $\epsilon > 0$ . Choose  $\delta = \min\left\{\frac{c}{2}, \frac{c^2}{2}\epsilon\right\}$ . Suppose  $|x - c| < \delta$ . Then,  $|x - c| < \frac{c}{2} \implies |x| > c - |x - c| > \frac{c}{2}$ . Thus,  $\frac{1}{|x|} < \frac{2}{c}$ . Therefore,

$$\left| \frac{1}{x} - \frac{1}{c} \right| = \frac{|x - c|}{|xc|}$$

$$< \frac{\delta}{|x||c|}$$

$$< \frac{2}{c^2} \delta$$

$$\leq \frac{2}{c^2} \frac{c^2 \epsilon}{2} = \epsilon.$$

As shown in the previous example.  $\delta$  depended on **both**  $\epsilon$  and c.

## **Definition 193** (Uniformly Continuous)

Let  $f: S \to \mathbb{R}$ . Then, f is uniformly continuous on S if  $\forall \epsilon > 0$ ,  $\exists \delta = \delta(\epsilon) > 0$  such that  $\forall x, c \in S$ ,

$$|x - c| < \delta \implies |f(x) - f(c)| < \epsilon$$
.

**Remark 194.** Thus, in the definition of uniform continuity,  $\delta$  only depends on  $\epsilon$ !

#### Example 195

The function  $f(x) = x^2$  is uniformly continuous on [0, 1].

**Proof**: Let  $\epsilon > 0$ . Choose  $\delta = \frac{\epsilon}{2}$ . Then, if  $x, c \in [0, 1]$  then  $|x - c| < \delta$  implies that

$$|x^2 - c^2| = |x + c||x - c| < 2|x - c| < 2\delta = \epsilon.$$

However, there are of course continuous functions that are not uniformly continuous. For example, we will show that  $f(x) = \frac{1}{x}$  is not uniformly continuous on (0,1), but first we consider the negation of the definition.

## Negation 196 (Not Uniformly Continuous)

Let  $f: S \to \mathbb{R}$ . Then, f is not uniformly continuous on S if  $\exists \epsilon_0 > 0, \forall \delta > 0$  such that  $\exists x, c \in S$  with

$$|x-c| < \delta$$
 and  $|f(x) - f(c)| \ge \epsilon_0$ .

**Proof**: Choose  $\epsilon_0 = 2$  (in fact, any  $\epsilon_0 > 0$  will show that  $\frac{1}{x}$  is not uniformly continuous on (0,1)). Then, let  $\delta > 0$ . Choose  $c = \min\left\{\delta, \frac{1}{2}\right\}$  and  $x = \frac{c}{2}$ . Then,  $|x - c| = \frac{c}{2} \le \frac{\delta}{2} < \delta$  and

$$\left| \frac{1}{x} - \frac{1}{c} \right| = \left| \frac{2}{c} - \frac{1}{c} \right| = \frac{1}{c} \ge \frac{1}{\frac{1}{2}} = 2.$$

#### Theorem 197

Let  $f:[a,b]\to\mathbb{R}$ . Then, f is continuous if and only if f is uniformly continuous.

**Proof**:  $(\Leftarrow)$  This direction is left as an exercise to the reader.

( $\Longrightarrow$ ) Suppose f is continuous and assume for the sake of contradiction that f is not uniformly continuous. Then,  $\exists \epsilon_0 > 0$  such that for all  $n \in \mathbb{N}$ ,  $\exists x_n, c_n \in [a, b]$  such that

$$|x_n - c_n| < \frac{1}{n}$$
 and  $|f(x_n) - f(c_n)| > \epsilon_0$ .

By Bolzano-Weierstrass,  $\exists$  a subsequence  $\{x_{n_k}\}$  of  $\{x_n\}$  and  $x \in [a,b]$  such that  $\lim_{k\to\infty} x_{n_k} = x$ . Similarly, by Bolzano-Weierstrass,  $\exists$  a subsequence  $\{c_{n_k}\}$  of  $\{c_n\}$  and  $c \in [a,b]$  such that  $\lim_{k\to\infty} c_{n_k} = c$ . Note that subsequence  $\{x_{n_{k_j}}\}$  of  $\{x_{n_k}\}$  satisfies  $\lim_{j\to\infty} x_{n_{k_j}} = x$ .

Then,

$$|x - c| = \lim_{j \to \infty} |x_{n_{k_j}} - c_{n_{k_j}}| \le \lim_{j \to \infty} \frac{1}{n_{k_i}} - 0.$$

Thus, x = c. But, since f is continuous at c,

$$0 = |f(c) - f(c)| = \lim_{j \to \infty} |f(x_{n_{k_j}}) - f(c_{n_{k_j}})| \ge \epsilon_0.$$

This is a contradiction.

#### Derivative

#### **Definition 198**

Let I be an interval, let  $f: I \to \mathbb{R}$ , and let  $c \in I$ . We say that f is differentiable at c if the limit

$$\lim_{x \to c} \frac{f(x) - f(c)}{x - c}$$

exists.

## Notation 199

If f is differentiable at c, we write

$$f'(c) := \lim_{x \to c} \frac{f(x) - f(c)}{x - c}.$$

Furthermore, if f is differentiable at every  $c \in I$ , we write f' or  $\frac{df}{dx}$  for the function f'(x).

## Example 200

Consider the function f(x) = ax + b. Then, for all  $c \in \mathbb{R}$ , f'(c) = a.

**Proof**: This follows as

$$\lim_{x\to c}\frac{f(x)-f(c)}{x-c}=\lim_{x\to c}\frac{ax+b-(ac+b)}{x-c}=a\lim_{x\to c}\frac{x-c}{x-c}=\lim_{x\to c}a=a.$$

Example 201 (The Power Rule)

For all  $n \in \mathbb{N}$ , if  $f(x) = \alpha x^n$ , then for all  $c \in \mathbb{R}$ ,

$$f'(c) = \alpha n c^{n-1}.$$

**Proof**: We note that for all  $n \in \mathbb{N}$ ,

$$(x-c)\sum_{j=0}^{n-1}x^{n-1-j}c^j = \sum_{j=0}^{n-1}x^{n-j}c^j - \sum_{j=0}^{n-1}x^{n-1-j}c^{j+1}.$$

Letting  $\ell = j + 1$ , we obtain

$$(x-c)\sum_{j=0}^{n-1} x^{n-1-j}c^j = \sum_{j=0}^{n-1} x^{n-j}c^j - \sum_{\ell=1}^n x^{n-\ell}c^\ell$$
$$= x^{n-0}c^0 - x^{n-n}c^n$$
$$= x^n - c^n.$$

Therefore,

$$\lim_{x \to c} \frac{\alpha x^n - \alpha c^n}{x - c} = \alpha \lim_{x \to c} \sum_{j=0}^{n-1} x^{n-1-j} c^j = \alpha \sum_{j=0}^{n-1} c^{n-1-j} c^j = \alpha n c^{n-1}.$$

Weierstrass's Example of a Continuous and Nowhere Differentiable Function

#### Theorem 202

If  $f: I \to \mathbb{R}$  is differentiable at  $c \in I$ , then f is continuous at c.

**Proof**: Since every point of I is a cluster point of I, f is continuous at  $c \in I \iff \lim_{x \to c} f(x) = f(c)$ . Now,

$$\lim_{x \to c} f(x) = \lim_{x \to c} (f(x) - f(c) + f(c))$$

$$= \lim_{x \to c} \left( (x - c) \frac{f(x) - f(c)}{x - c} + f(c) \right)$$

$$= 0 \cdot f'(c) + f(c) = f(c).$$

Question 203. Is the converse true? Does f being continuous imply that f is differentiable?

The answer, is **no**.

#### Example 204

Let f(x) = |x|. Then, f is not differentiable at 0.

**Proof**: We find a sequence  $x_n \to 0$  such that

$$\lim_{n \to \infty} \frac{f(x_n) - f(0)}{x_n - 0}$$
 does not exist.

Let  $x_n = \frac{(-1)^n}{n}$ . Then,  $\lim_{n \to \infty} x_n = 0$ . However,

$$\frac{f(x_n) - f(0)}{x_n - 0} = \frac{|(-1)^n / n|}{(-1)^n / n} = (-1)^n,$$

and  $\lim_{n\to\infty} (-1)^n$  does not exist.

**Question 205.** If  $f: \mathbb{R} \to \mathbb{R}$  is continuous, then does there exist a  $c \in \mathbb{R}$  such that f is differentiable at c?

The answer is again no! This was shown by Weierstrass, aka the Godfather.

The basic idea is to build a continuous function that is a sum of highly oscillating functions.

Remark 206. Note that we number the upcoming theorems so we may reference them a bit later in this lecture.

## **Theorem 207** (Theorem I)

We will show the following

- 1.  $\forall x, y \in \mathbb{R}, |\cos x \cos y| \le |x y|$ .
- 2. Let  $c \in \mathbb{R}$ . Then, for all  $K \in \mathbb{N}$ ,  $\exists y \in (c + \pi/K, c + 3\pi/K)$  such that

$$|\cos(Kc) - \cos(Ky)| \ge 1.$$

## **Proof**:

1. In the proof of continuity of  $\sin x$ , we showed that  $\forall x,y \in \mathbb{R}, |\sin x - \sin y| \leq |x-y|$ . Thus,

$$|\cos x - \cos y| = |\sin(x + \pi/2) - \sin(y + \pi/2)| \le |x - y|.$$

2. The function  $f(x) = \cos(Kx)$  is a  $\frac{2\pi}{K}$ -periodic function. In particular,  $([-1,1] \setminus \cos(Kc)) \subset f(c+\pi/K,c+3\pi/K)$ .

If  $\cos Kc \ge 0$ , then we choose y such that  $\cos(Ky) = -1$ . If  $\cos(Kc) < 0$ , then we choose y such that  $\cos(Ky) = 1$ . This completes the proof

## **Theorem 208** (Theorem II)

For all  $a, b, c \in \mathbb{R}$ ,

$$|a+b+c| \ge |a| - |b| - |c|$$
.

**Proof**: We apply the Triangle Inequality twice:

$$|a| = |a+b+b+(-b)+(-c)| \le |a+b+b| + |b+c| \le |a+b+c| + |b| + |c|.$$

## Theorem 209 (Theorem III)

We will show the following:

- 1.  $\forall x \in \mathbb{R}, \sum_{k=0}^{\infty} \frac{\cos(160^k x)}{4^k}$  is absolutely convergent.
- 2. The function  $f: \mathbb{R} \to \mathbb{R}$ ,  $f(x) = \sum_{k=0}^{\infty} \frac{\cos(160^k x)}{4^k}$  is bounded and continuous.

## **Proof**:

1.  $\forall k, \left| \frac{\cos(160^k x)}{4^k} \right| \leq 4^{-k}$ . Hence, by the Comparison Test,

$$\sum_{k=0}^{\infty} \left| \frac{\cos(160^k x)}{4^k} \right| \quad \text{converges.}$$

2. For all  $x \in \mathbb{R}$ ,  $|f(x)| \le \sum_{k=0}^{\infty} \frac{|\cos(160^k x)|}{4^k} \le \sum 4^{-k} = \frac{4}{3}$ . Therefore, f is bounded.

We now show that f is continuous over  $\mathbb{R}$ . Suppose  $c \in \mathbb{R}$  and  $x_n \to c$ . Note that  $\{|f(x_n) - f(c)|\}_n$  is bounded, and thus

$$\lim_{n \to \infty} |f(x_n) - f(c)| = 0 \iff \limsup_{n \to \infty} |f(x_n) - f(c)| = 0.$$

We claim that for all  $\epsilon > 0$ ,  $\limsup_{n \to \infty} |f(x_n) - f(c)| \le \epsilon$ . Let  $\epsilon > 0$ . Choose  $M_0$  such that  $\sum_{k=M_0+1}^{\infty} 4^{-k} < \frac{\epsilon}{2}$ .

Then,

$$\limsup_{n \to \infty} |f(x_n) - f(c)| = \limsup_{n} \left| \sum_{k=0}^{M_0} \frac{\cos(160^k x_n)}{4^k} - \frac{\cos(160^k c)}{4^k} + \sum_{k=M_0+1}^{\infty} \frac{\cos(160^k x_n)}{4^k} - \frac{\cos(160^k c)}{4^k} \right| \\
\leq \limsup_{n} \sum_{k=0}^{M_0} 4^{-k} |\cos(160^k x_n) - \cos(160^k c)| + \sum_{k=M_0+1}^{\infty} 4^{-k} (|\cos(160^k x_n)| + |\cos(160^k c)|) \\
\leq \limsup_{n} \left( \sum_{k=0}^{M_0} 40^k \right) |x_n - c| + \epsilon = \epsilon.$$

Theorem 210 (Weierstrass)

The function  $f(x) = \sum_{k=0}^{\infty} \frac{\cos(160^k x)}{4^k}$  is nowhere differentiable.

**Proof**: Let  $c \in \mathbb{R}$ . We will construct a sequence  $x_n \to c$  such that  $\left\{\frac{f(x_n) - f(c)}{x_n - c}\right\}_n$  is unbounded. By Theorem I 2),  $\forall n \in \mathbb{N}$  there exists an  $x_n$  such that **a**)  $\frac{\pi}{160^n} < x_n - c < \frac{3\pi}{160^n}$  and **b**)  $|\cos(160^n c) - \cos(160^n x_n)| \ge 1$ . By **a**),  $x_n \neq 0 \forall n$  and  $|x_n - c| \le \frac{3\pi}{160^n} \to 0$ . Let  $f_k(x) = \frac{\cos(160^k x)}{4^k}$  so  $f(x) = \sum f_k(x)$ . Let  $n \in \mathbb{N}$ . Thus, denote

$$f(c) - f(x_n) = f_n(c) - f_n(x_n) + \sum_{k=0}^{n-1} (f_k(c) - f_k(x_n)) + \sum_{k=n}^{\infty} (f_k(c) - f_k(x_n))$$
  
:=  $a_n + b_n + c_n$ .

Therefore, by Theorem II,

$$|f(c) - f(x_n)| \ge |a_n| - |b_n| - |c_n|.$$

By **b**),  $|a_n| = 4^{-n} |\cos(160^k x_n) - \cos(160^k c)| \ge 4^{-n}$ . Furthermore, we have

$$|b_n| \le \sum_{k=0}^{n-1} 4^{-k} |\cos(160^k c) - \cos(160^k x_n)| \le \sum_{k=0}^{n-1} 4^{-k} \cdot 160^k |x_n - c| \le \frac{3\pi}{160^n} \sum_{k=0}^{n-1} 40^k = \frac{3\pi}{160^n} \cdot \frac{40^n - 1}{39} \le \frac{4^{-n+1}}{13}.$$

Finally, we have

$$|c_n| \le \sum_{k=n+1}^{\infty} 4^{-k} (|\cos(160^k c)| + |\cos(160^k x_n)|) \le 2 \sum_{k=n+1}^{\infty} 4^{-k} = 2 \cdot 4^{-n-1} \cdot \frac{4}{3} = 4^{-n} \frac{2}{3}.$$

Therefore, by the above inequalities, we have

$$|f(c) - f(x_n)| \ge 4^{-n} \left(1 - \frac{4}{13} - \frac{2}{3}\right) = 4^{-n} \cdot \frac{1}{39}.$$

Therefore,

$$\frac{|f(c) - f(x_n)|}{|c - x_n|} \ge \frac{160^n}{3\pi} \cdot 4^{-n} \cdot \frac{1}{39} = \frac{40^n}{117\pi}$$

Thus,  $\left\{\frac{f(x_n)-f(c)}{x_n-c}\right\}_n$  is unbounded.

Remark 211. In other words, this proof by Weierstrass shows that there exists a continuous function that is nowhere differentiable!

## Differentiation Rules, Rolle's Theorem, and the Mean Value Theorem

#### Theorem 212

Let  $f: I \to \mathbb{R}$ ,  $g: I \to \mathbb{R}$  be differentiable at  $c \in I$ . Then,

- 1. (Linearity)  $\forall \alpha \in \mathbb{R}, (\alpha f + g)'(c) = \alpha f'(c) + g'(c)$ .
- 2. (Product rule) (fg)'(c) = f'(c)g(c) + f(c)g'(c).
- 3. (Quotient rule) If  $g(x) \neq 0$  for all  $x \in I$ , then

$$\left(\frac{f}{g}\right)'(c) = \frac{f'(c)g(c) - f(c)g'(c)}{(g(c))^2}.$$

#### **Proof**:

1. We can compute this directly:

$$\lim_{x \to c} \frac{(\alpha f + g)(x) - (\alpha f + g)(c)}{x - c} = \lim_{x \to c} \alpha \frac{f(x) - f(c)}{x - c} + \frac{g(x) - g(c)}{x - c} = \alpha f'(x) + g'(x).$$

2. We first write

$$\frac{f(x)g(x)-f(c)g(c)}{x-c} = \frac{f(x)-f(c)}{x-c} \cdot g(x) + f(c) \cdot \frac{g(x)-g(c)}{x-c}$$

and use the fact that  $\lim_{x\to c} g(x) = f(c)$ .

3. The quotient rule is left as an exercise to the reader.

#### Theorem 213 (Chain Rule)

Let  $I_1, I_2$  be two intervals,  $g: I_1 \to I_2$  be differentiable at  $c \in I_1$ , and  $f: I_2 \to \mathbb{R}$  differentiable at g(c). Then,  $f \circ g: I_1 \to \mathbb{R}$  is differentiable at c and

$$(f \circ g)'(c) = f'(g(c))g'(c).$$

**Proof:** Let h(x) = f(g(x)) and d = g(c). We want to prove that h'(c) = f'(d)g'(c). Define the following

$$u(y) = \begin{cases} \frac{f(y) - f(d)}{y - x} & y \neq d \\ f'(d) & y = d \end{cases} \text{ and } v(y) = \begin{cases} \frac{g(x) - g(c)}{x - c} & x \neq c \\ g'(d) & x = c \end{cases}.$$

Then,

$$\lim_{y \to d} u(y) = \lim_{y \to d} \frac{f(y) - f(d)}{y - d} = f'(d) = u(d).$$

Similarly,

$$\lim_{x \to c} v(x) = \lim_{x \to c} \frac{g(x) - g(c)}{x - c} = g'(c) = v(c).$$

In other words, u is continuous at d and v is continuous at c. Now,

$$f(y) - f(d) = u(y)(y - d)$$

$$g(x) - g(c) = v(x)(x - c)$$

$$\implies h(x) - h(c) = f(g(x)) - f(d)$$

$$= u(g(x))(g(x) - g(c))$$

$$= u(g(x))v(x)(x - c).$$

Therefore,

$$\lim_{x \to c} \frac{h(x) - h(c)}{x - c} = \lim_{x \to c} u(g(x))v(x)$$
$$= u(g(c))v(c)$$
$$= f'(g(c))g'(c).$$

## Mean Value Theorem

**Definition 214** (Relative Maximum/Minimum)

Let  $S \subset \mathbb{R}$  and  $f: S \to \mathbb{R}$ . Then, f has a relative maximum at  $c \in S$  if  $\exists \delta > 0$  such that for all  $x \in S$ ,  $|x - c| < \delta \implies f(x) \le f(c)$ . The definition for relative maximum is analogous.

## Theorem 215

If  $f:[a,b]\to\mathbb{R}$  has a relative max or min at  $c\in(a,b)$  and f is differentiable at c, then

$$f'(c) = 0.$$

**Proof**: If f has a relative maximum at  $c \in (a, b)$  then  $\exists \delta > 0$  such that  $(c - \delta, c + \delta) \subset (a, b)$  and  $\forall x \in (c - \delta, c + \delta)$ ,  $f(x) \leq f(c)$ . Let

$$x_n = c - \frac{\delta}{2n} \in (c - \delta, c).$$

Then,  $x_n \to c$  so

$$f'(c) = \lim_{n \to \infty} \frac{f(x_n) - f(c)}{x_n - c} \ge 0.$$

Now let

$$y_n = c + \frac{\delta}{2n} \in (c, c + \delta).$$

Then,  $y_n \to c$  so

$$f'(c) = \lim_{n \to \infty} \frac{f(y_n) - f(c)}{y_n - c} \le 0.$$

Therefore, f'(c) = 0. The proof for relative minimum is similar and thus left to the reader.

Theorem 216 (Rolle)

Let  $f:[a,b]\to\mathbb{R}$  be continuous and differentiable on (a,b). If f(a)=f(b), then  $\exists c\in(a,b)$  such that f'(c)=0.

Remark 217. Are the hypotheses all necessary? This is left to the reader to figure out.

**Proof**: Let K = f(a) = f(b). Since f is continuous on [a, b],  $\exists c_1, c_2 \in [a, b]$  such that f achieves an absolute maximum at  $c_1$  and absolute minimum at  $c_2$ . If  $f(c_1) > K \implies c_1 \in (a, b)$ . Therefore,  $f'(c_1) = 0$  by the previous theorem. Similarly, if  $f(c_2) < K$ , then  $c_2 \in (a, b) \implies f'(c_2) = 0$ . If

$$f(c_1) \le K \le f(c_2) \implies f(x) = K \ \forall x \in [a,b] \implies f'(c) - 0 \ \text{ for any } c \in (a,b).$$

**Theorem 218** (Mean Value Theorem)

Let  $f:[a,b]\to\mathbb{R}$  be continuous, and let f be differentiable on (a,b). Then,  $\exists c\in(a,b)$  such that

$$f(b) - f(a) = f'(c)(b - a).$$

Remark 219. The Mean Value Theorem is sometimes denoted MVT.

**Proof**: Define  $g:[a,b]\to\mathbb{R}$  with

$$g(x) = f(x) - f(b) + \frac{f(b) - f(a)}{b - a}(b - x).$$

Then, g(a) = g(b) = 0. Thus, by Rolle's theorem,  $\exists c \in (a, b)$  with g'(c) = 0, and hence

$$0 = f'(c) - \frac{f(b) - f(a)}{b - a}.$$

We now look at some useful applications of the MVT.

#### Theorem 220

If  $f: I \to \mathbb{R}$  is differentiable and f'(x) = 0 for all  $x \in I$ , then f is constant.

**Proof**: Let  $a, b \in I$  with a < b. Then, f is continuous on [a, b] and differentiable on (a, b). Therefore,  $\exists c \in (a, b)$  such that f(b) - f(a) = (b - a)f'(c) = 0. Hence, f(b) = f(a) for all  $a, b \in I$  such that a < b.

#### Theorem 221

Let  $f: I \to \mathbb{R}$  be differentiable. Then,

- 1. f is increasing if and only if  $f'(x) \geq 0$  for all  $x \in I$  and
- 2. f is decreasing if and only if  $f'(x) \leq 0$  for all  $x \in I$ .

## **Proof**:

1.  $(\Leftarrow)$  Suppose  $f'(x) \geq 0$  for all  $x \in I$ . Let  $a, b \in I$  with a < b. Then, by MVT,  $\exists c \in (a, b)$  such that

$$f(b) - f(a) = (b - a)f'(c) \ge 0 \implies f(a) \le f(b).$$

( $\Longrightarrow$ ) Suppose f is increasing. Let  $c \in I$  and let  $\{x_n\}$  be a sequence in I such that  $x_n \to c$  such that  $\forall n, x_n < c$ . Then, for all  $n, f(x_n) - f(c) \le 0 \Longrightarrow \frac{f(x_n) - f(c)}{x_n - c} \ge 0$ . Therefore,

$$f'(c) = \lim_{n \to \infty} \frac{f(x_n) - f(c)}{x_n - c} \ge 0.$$

Now let  $\{x_n\}$  be a sequence in I such that  $x_n \to c$  such that  $\forall n, x_n > c$ . Then, for all  $n, f(x_n) - f(c) \ge 0 \implies \frac{f(x_n) - f(c)}{x_n - c} \ge 0$ . Therefore,

$$f'(c) = \lim_{n \to \infty} \frac{f(x_n) - f(c)}{x_n - c} \ge 0.$$

Hence, in either case,  $f'(c) \geq 0$ .

2. Notice that f is decreasing if and only if -f is increasing, and apply 1. to -f.

## Taylor's Theorem and the Definition of Riemann Sums

## Taylor's Theorem

Remark 222. Taylor's theorem is essentially the Mean Value Theorem for higher order derivatives.

#### **Definition 223** (*n*-times Differentiable)

We say  $f: I \to \mathbb{R}$  is n-times differentiable on  $J \subset I$  if  $f', f'', \dots, f^{(n)}$  exist at every point in J.

#### Notation 224

We denote the *n*-th derivative of f as  $f^{(n)}$  (as used above).

## Theorem 225 (Taylor)

Suppose  $f:[a,b]\to\mathbb{R}$  is continuous and has n continuous derivatives on [a,b] such that  $f^{(n+1)}$  exists on (a,b). Given  $x_0,x\in[a,b]$ , there exists a  $c\in(x_0,x)$  such that

$$f(x) = \sum_{k=0}^{n} \frac{1}{k!} f^{(k)}(x_0) (x - x_0)^k + \frac{f^{(n+1)}(c)}{(n+1)!} (x - x_0)^{n+1}.$$

Denote the large sum as  $P_n(x)$  and the last term with  $R_n(x)$ .

## Definition 226

 $P_n(x)$  is the n-th order Taylor polynomial for f at  $x_0$ .  $R_n(x)$  is the n-th order remainder term.

We will essentially apply the Mean Value Theorem n+1 times to prove Taylor's theorem.

**Proof**: Let  $x, x_0 \in [a, b]$ . If  $x = x_0$  then any c will satisfy the theorem. So, suppose  $x \neq x_0$ . Let  $M_{x,x_0} = \frac{f(x) - P_n(x)}{(x - x_0)^{n+1}}$ . Hence,

$$f(x) = P_n(x) + M_{x,x_0}(x - x_0)^{n+1}.$$

Now, for  $0 \le k \le n$ ,

$$f^k(x_0) = P_n^{(k)}(x_0).$$

Let  $g(s) = f(s) - P_n(s) - M_{x,x_0}(s-x_0)^{n+1}$  (notably, n+1-times differentiable. Then,

$$g(x_0) = f(x_0) - P_n(x_0) - M_{x,x_0}(x_0 - x_0)^{n+1} = 0$$
  

$$g'(x_0) = f'(x_0) - P'_n(x_0) - M_{x,x_0}(n+1)(x_0 - x_0)^n = 0$$
  
:

$$g^{(n)}(x_0) = f^{(n)}(x_0) - P_n^{(n)}(x_0) - M_{x,x_0}(n+1)!(x_0 - x_0) = 0.$$

Now, notice that g(x) = 0 and  $g(x_0) = 0$ . By the MVT, there exists an  $x_1 \in (x_0, x)$  such that  $g'(x_1) = 0$ . Thus,  $g'(x_0) = 0$  and  $g'(x_1) = 0$ . Therefore,  $\exists x_2 \in (x_0, x_1)$  such that  $g''(x_2) = 0$ . Continuing, we analogously find  $x_n$ 

between  $x_0$  and  $x_{n-1}$  such that  $g^{(n)}(x_n) = 0$ . Then, finally,  $g^{(n)}(x_0) = 0$  and  $g^{(n)}(x_n) = 0$  implies  $\exists c \in (x_0, x_n)$  (and thus between  $x_0$  and  $x_0$ ) such that

$$g^{(n+1)}(c) = 0.$$

We may compute

$$\frac{\mathrm{d}^{n+1}}{\mathrm{d}s^{(n+1)}} M_{x,x_0} (s-x_0)^{n+1} = M_{x,x_0} (n+1)!.$$

Furthermore,  $P_n^{(n+1)}(c) = 0$  since  $P_n$  is a polynomial of degree n. Thereforee,

$$0 = g^{(n+1)}(c) = f^{(n+1)}(c) - M_{x,x_0}(n+1)!,$$

which implies  $M_{x,x_0} = \frac{f^{(n+1)!}(c)}{(n+1)!}$  and thus

$$f(x) = P_n(x) + \frac{f^{(n+1)}(c)}{(n+1)!} (x - x_0)^{n+1}.$$

**Theorem 227** (Second Derivative Test)

Suppose  $f:(a,b)\to\mathbb{R}$  has two continuous derivatives. If  $x_0\in(a,b)$  such that  $f'(x_0)=0$  and  $f''(x_0)>0$ , then f has a strict relative minimum at  $x_0$ .

**Proof**: Since f'' is continuous at  $x_0$  and

$$\lim_{c \to x_0} f''(c) = f''(x_0) > 0,$$

we have that  $\exists \delta > 0$  such that for all  $c \in (x_0 - \delta, x_0 + \delta)$ , f''(c) > 0. Let  $x \in (x_0 - \delta, x_0 + \delta)$  (as you will show in your homework). Then, by Taylor's theorem,  $\exists c$  between x and  $x_0$  (hence  $c \in (x_0 - \delta, x_0 + \delta)$ ) such that

$$f(x) = f(x_0) + \frac{f''(c)}{2}(x - x_0)^2 \ge f(x_0),$$

with  $f(x) > f(x_0)$  if  $x \neq x_0$ .

## The Riemann Integral

Remark 228. Riemann integration is the first rigorous theory of 'area' that agrees with experience (areas of rectangles, triangles, circles), and it is the inverse of differentiation. However, it is not a complete theory of area (see Lebesque integration).

## The Riemann Integral

#### **Definition 229**

We define the set

$$C([a,b]) := \{f : [a,b] \to \mathbb{R} \mid f \text{ is continuous}\}.$$

## **Definition 230** (Partition)

A partition  $\underline{x}$  of [a, b] is a finite set

$$\underline{x} = \{a = x_0 < x_1 < \dots < x_n = b\}.$$

The norm of  $\underline{x}$ , denoted  $||\underline{x}||$ , is the number

$$\|\underline{x}\| := \max\{x_1 - x_0, x_2 - x_1, \dots, x_n - x_{n-1}\}.$$

## Definition 231 (Tag)

If  $\underline{x}$  is a partition, a tag of  $\underline{x}$  is a finite set  $\underline{\xi} = \{\xi_1, \dots, \xi_n\}$  such that

$$a = x_0 \le \xi_1 \le x_1 \le \xi_2 \le x_2 \le \dots \le x_{n-1} \le \xi_n \le x_n = b.$$

The pair  $(\underline{x},\underline{\xi})$  is referred to as a tagged partition.

#### Example 232

Consider the tagged partition  $(\underline{x}, \xi) = (\{1, 3/2, 2, 3\}, \{5/4, 7/4, 5/2\})$ . Then,

$$\|\underline{x}\| = \max\{3/2 - 1, 2 - 3/2, 3 - 2\} = 1.$$

## **Definition 233** (Riemann sum)

The Riemann sum of f corresponding to  $(\underline{x}, \xi)$  is the number

$$S_f(\underline{x},\underline{\xi}) := \sum_{k=1}^n f(\xi_k)(x_k - x_{k-1}).$$

Let's try to understand how to interpret this using a picture. For  $f \in C([a, b])$  positive,  $S_f(\underline{x}, \underline{\xi})$  is an approximate area under the graph of f. As  $||\underline{x}|| \to 0$ , we *should* expect these approximate areas to converge to a number A, which we **interpret** as the area under the curve f on the interval [a, b].

Question 234. Do these approximate sums actually converge?

We will answer this question and more during the next few lectures.

## The Riemann Integral of a Continuous Function

Theorem 235 (Riemann Integral)

Let  $f \in C([a,b])$ . Then, there exists a unique number denoted  $\int_a^b f(x) dx \in \mathbb{R}$  with the following property: for all sequences of tagged partitions  $\{(\underline{x}^r, \xi^r)\}$  such that  $\|\underline{x}^r\| \to 0$ , we have

$$\lim_{r \to \infty} S_f(\underline{x}^r, \underline{\xi}^r) = \int_a^b f(x) \, \mathrm{d}x.$$

**Remark 236.** Uniqueness follows immediately from uniqueness of limits of sequences of real numbers. All we need to prove is existence of  $\int_a^b f(x) dx$ .

Before giving the proof of the theorem, we first prove some useful facts. Note that we number the next few theorems to use them in our proof of the above theorem.

**Definition 237** (Modulus of Continuity)

For  $f \in C([a,b])$ ,  $\eta > 0$ , we define the modulus of continuous

$$w_f(\eta) = \sup\{|f(x) - f(y)| \mid |x - y| \le \eta\}.$$

Remark 238. Note that we number the following theorems to reference later.

Theorem 239 (Theorem I)

For all  $f \in C([a, b])$ ,  $\lim_{\eta \to 0} w_f(\eta) = 0$ . In other words, for all  $\epsilon > 0$ , there exists a  $\delta > 0$  such that  $\forall \eta < \delta$ ,  $w_f(\eta) < \epsilon$ .

**Proof**: Let  $\epsilon > 0$ . Since  $f \in C([a,b])$ , f is uniformly continuous on [a,b] (as continuity on a bounded interval is equivalent to uniform continuity on the same interval). Thus,  $\exists \delta_0 > 0$  such that if  $|x-y| < \delta_9$ , then  $|f(x) - f(y)| < \epsilon/2$ . Choose  $\delta = \delta_0$  and let  $\eta < \delta$ . Then, if  $|x-y| \le \eta < \delta = \delta_0$ , then

$$|f(x) - f(y)| < \frac{\epsilon}{2}.$$

Therefore,  $\epsilon/2$  is an upper bound for  $\{|f(x) - f(y)| \mid |x - y| \leq \eta\}$ . Hence,

$$w_f(\eta) \le \epsilon/2 < \epsilon$$
.

**Theorem 240** (Theorem II)

If  $(\underline{x}, \xi)$  and  $(\underline{x}', \xi')$  are tagged partitions of [a, b] such that  $\underline{x} \subset \underline{x}'$ , then if  $f \in C([a, b])$  then

$$|S_f(\underline{x},\xi) - S_f(\underline{x}',\xi')| \le w_f(||\underline{x}||)(b-a).$$

## **Definition 241** (Refinement)

If  $(\underline{x}, \xi)$  and  $(\underline{x}', \xi')$  are tagged partitions of [a, b] such that  $\underline{x} \subset \underline{x}'$ , we say  $\underline{x}'$  is a refinement of  $\underline{x}$ .

**Remark 242.** Refinements of  $\underline{x}$  are obtained by adding more partition points.

**Proof**: For  $k = 1, \ldots, n$ , let

$$\underline{y}(k) = \{x_{k-1} = x'_{\ell}, x'_{\ell+1}, \dots, x'_{m} = x_{k}\}\$$

$$\eta(k) = \{\xi'_{\ell+1}, \xi'_{\ell+2}, \dots, \xi'_{m}\}.$$

Then,

$$|f(\xi_k)(x_k - x_{k-1}) - S_f(\underline{y}(k), \underline{\eta}(k))| = \left| f(\xi_k) - \sum_{j=\ell+1}^m f(\xi_j')(x_j' - x_{j-1}') \right|$$

$$= \left| \sum_{j=\ell+1}^m (f(\xi_k) - f(\xi_j'))(x_j' - x_{j-1}') \right|$$

since  $\sum_{j=1}^{m} x'_j - x'_{j-1} = x_m - x'_{\ell} = x_k - x_{k-1}$ . Hence,

$$|f(\xi_k)(x_k - x_{k-1}) - S_f(\underline{y}(k), \underline{\eta}(k))| \le \sum_{j=\ell+1}^m |f(\xi_k) - f(\xi'_j)| (x'_j - x'_{j-1})$$

$$\le \sum_{j=\ell+1}^m w_f(|x_k - x_{k-1}|) (x'_j - x'_{j-1})$$

$$\le w_f(||\underline{x}|| (x_k - x_{k-1}).$$

Thus,

$$|S_f(\underline{x},\underline{\xi}) - S_f(\underline{x}',\underline{\xi}')| = \left| \sum_{k=1}^m (f(\xi_k)(x_k - x_{k-1}) - S_f(\underline{y}(k),\underline{\eta}(k))) \right|$$

$$\leq \sum_{k=1}^m |f(\xi_k)(x_k - x_{k-1}) - S_f(\underline{y}(k),\underline{\eta}(k))|$$

$$\leq w_f(||\underline{x}||) \sum_{k=1}^n x_k - x_1 = w_f(||\underline{x}||)(b-a).$$

**Theorem 243** (Theorem III)

If  $(\underline{x},\underline{\xi})$  and  $(\underline{x}',\underline{\xi}')$  are any two tagged partitions of [a,b] and  $f\in C([a,b])$ , then

$$|S_f(\underline{x},\underline{\xi}) - S_f(\underline{x}',\underline{\xi}')| \le (w_f(||\underline{x}|) + w_f(||\underline{x}'||))(b-a).$$

**Proof**: Let  $\underline{x}'' = \underline{x} \cup \underline{x}'$  (i.e. a common refinement), and  $\underline{\xi}''$  be a tag of  $\underline{x}''$ . Then, by Theorem II,

$$|S_f(\underline{x},\underline{\xi}) - S_f(\underline{x}',\underline{\xi}')| \le |S_f(\underline{x},\underline{\xi}) - S_f(\underline{x}'',\underline{\xi}'')| - |S_f(\underline{x}',\underline{\xi}') - S_f(\underline{x}'',\underline{\xi}'')|$$

$$\le w_f(||x||)(b-a) + w_f(||x'||)(b-a).$$

We now have the theorems necessary to prove the big theorem at the beginning of this section.

**Proof**: Let  $\{y(r), \zeta(r)\}_r$  be a sequence of tagged partitions with  $\|\underline{y}(r)\| \to 0$  as  $r \to \infty$ .

Claim 1:  $\{S_f(\underline{y}(r),\underline{\zeta}(r))\}_r$  is a Cauchy sequence. Proof: Let  $\epsilon > 0$ . By Theorem I,  $\exists \delta > 0$  such that  $\forall \eta < \delta$ ,

$$w_f(\eta) < \frac{\epsilon}{2(b-a)}.$$

Since  $||y(r)|| \to 0$ ,  $\exists M_0 \in \mathbb{N}$  such that  $\forall r \geq M_0$ ,

$$||y(r)|| < \delta.$$

Choose  $M = M_0$ . Then, if  $r, s \ge M = M_0$ ,

$$|S_f(y(r),\zeta(r)) - S_f(y(s),\zeta(r))| \le (w(||y(r)|| + w(||y(s)||))(b-a))$$

by Theorem III. Hence, by the above inequalities, it follows that

$$|S_f(\underline{y}(r),\underline{\zeta}(r)) - S_f(\underline{y}(s),\underline{\zeta}(r))| < \left(\frac{\epsilon}{2(b-a)} + \frac{\epsilon}{2(b-a)}\right)(b-a) = \epsilon.$$

This proves Claim 1. Let  $L = \lim_{r\to\infty} S_f(\underline{y}(r),\underline{\zeta}(r))$ , which exists as Cauchy sequences of real numbers are convergent sequences.

Claim 2: Let  $\{(\underline{x}(r),\underline{\xi}(r))\}_r$  be **any** sequence of partitions with  $\|\underline{x}(r)\| \to 0$ . Then,

$$\lim_{r \to \infty} S_f(\underline{x}(r), \underline{\xi}(r)) = L.$$

With  $(y(r), \zeta(r))$  as before, we have by the Triangle Inequality and Theorem III that

$$|S_f(\underline{x}(r),\underline{\xi}(r)) - L| \le |S_f(\underline{x}(r),\underline{\xi}(r)) - S_f(\underline{y}(r),\underline{\zeta}(r))| + |S_f(\underline{y}(r),\underline{\zeta}(r)) - L|$$

$$\le (w_f(||\underline{x}(r)||) + w_f(||y(r)||))(b - a) + |S_f(y(r),\zeta(r)) - L| \to 0$$

as  $r \to \infty$  by Theorem I and by the definition of L. Thus, by the Squeeze Theorem,

$$|S_f(\underline{x}(r), \xi(r)) - L| \to 0 \text{ as } r \to 0.$$

## Properties of the Riemann Integral

#### Notation 244

We will often abbreviate  $\int_a^b f(x) dx$  to  $\int_a^b f$ .

**Theorem 245** (Linearity)

If  $f, g \in C([a, b])$  and  $\alpha \in \mathbb{R}$ , then

$$\int_{a}^{b} (\alpha f + g) = \alpha \int_{a}^{b} f + \int_{a}^{b} g.$$

**Proof**: Let  $\{(\underline{x}(r),\underline{\xi}(r))\}_r$  be a sequence of tagged partitions such that  $\|\underline{x}(r)\| \to 0$ . Then,

$$S_{\alpha f+g}(x(r), \xi(r)) = \alpha S_f(x(r), \xi(r)) + S_g(x(r), \xi(r)).$$

Therefore,

$$\int_{a}^{b} (\alpha f + g) = \lim_{r \to \infty} S_{\alpha f + g}(\underline{x}(r), \underline{\xi}(r))$$

$$= \lim_{r \to \infty} (\alpha S_{f}(\underline{x}(r), \underline{\xi}(r)) + S_{g}(\underline{x}(r), \underline{\xi}(r))$$

$$= \alpha \int_{a}^{b} f + \int_{a}^{b} g.$$

The Fundamental Theorem of Calculus, Integration by Parts, and Change of Variable Formula

Theorem 246 (Additivity)

If  $f \in C([a, b])$  and a < c < b, then

$$\int_a^b f = \int_a^c f + \int_c^b f.$$

**Proof**: Let  $\{(\underline{y}(r),\underline{\zeta}(r))\}_r$  and  $\{(\underline{z}(r),\underline{\eta}(r))\}_r$  be tagged partitions of [a,c] and [c,b] respectively such that  $\|\underline{y}(r)\| \to 0$  and  $\|\underline{z}(r)\| \to 0$ . Define

$$\underline{x}(r) = \underline{y}(r) \cup \underline{z}(r)$$

$$\xi(r) = \zeta(r) \cup \eta(r),$$

a sequence of tagged partitions of [a, b]. Then,

$$\|\underline{x}(r)\| \le \|\underline{y}(r)\| + \|\underline{z}(r)\| \to 0.$$

Thus,

$$\int_{a}^{b} f = \lim_{t \to \infty} S_{f}(\underline{x}(r), \underline{\xi}(r))$$

$$= \lim_{r \to \infty} (S_{f}(\underline{y}(r), \underline{\zeta}(r)) + S_{f}(\underline{z}(r), \underline{\eta}(r)))$$

$$= \int_{a}^{c} f + \int_{c}^{b} f.$$

Theorem 247

Let  $f \in C([a, b])$ , and

$$m_f = \inf\{f(x) \mid x \in [a, b]\} \in \mathbb{R}$$

$$M_f = \sup\{f(x) \mid x \in [a, b]\} \in \mathbb{R}.$$

Then,

$$m_f(b-a) \le \int_a^b f \le M_f(b-a).$$

**Proof**: Let  $\{(\underline{x}(r),\underline{\xi}(r))\}_r$  be a sequence of tagged partitions with  $\|\underline{x}(r)\| \to 0$ . Then,

$$S_f(\underline{x}(r),\underline{\xi}(r)) = \sum_{k=1}^n f(\xi_k(r))(x_k(r) - x_{k-1}(r)) \ge m_f \sum_{k=1}^n (x_k(r) - x_{k-1}(r)) = m_f(b-a).$$

Similarly,

$$S_f(\underline{x}(r),\underline{\xi}(r)) = \sum_{k=1}^n f(\xi_k(r))(x_k(r) - x_{k-1}(r)) \le M_f \sum_{k=1}^n (x_k(r) - x_{k-1}(r)) = M_f(b-a).$$

Therefore, for all r,

$$m_f(b-a) \le S_f(\underline{x}(r),\underline{\xi}(r)) \le M_f(b-a) \implies m_f(b-a) \le \int_a^b f \le M_f(b-a).$$

## Theorem 248

Suppose  $f \in C([a, b])$  and  $g \in C([a, b])$ .

1. If  $\forall x \in [a, b]$   $f(x) \leq g(x)$ , then

$$\int_{a}^{b} f \le \int_{a}^{b} g.$$

2. (Triangle Inequality for integrals):  $|\int_a^b f| \leq \int_a^b |f|.$ 

#### **Proof**:

1. Let  $\{(\underline{x}(r),\underline{\xi}(r))\}_r$  be a sequence of tagged partitions such that  $\|\underline{x}(r)\| \to 0$ . Then, for all  $r \in \mathbb{N}$ ,

$$S_f(\underline{x}(r), \underline{\xi}(r)) = \sum_{j=1}^n f(\xi_j(r))(x_j(r) - x_{j-1}(r))$$

$$\leq \sum_{j=1}^n g(\xi_j(r))(x_j(r) - x_{j-1}(r))$$

$$= S_g(\underline{x}(r), \underline{\xi}(r)).$$

Then, letting  $r \to \infty$ , we get that

$$\int_{a}^{b} f \le \int_{a}^{b} g.$$

2. Notice that  $\pm f(x) \leq |f(x)|$  for all x, and thus

$$\pm \int_a^b f \le \int_a^b |f| \implies -\int_a^b f \le \int_a^b f \le \int_a^b |f|.$$

Therefore,  $\left| \int_a^b f \right| \leq \int_a^b |f|$ .

Remark 249. There are some conventions that are worth noting:

- 1.  $\int_a^a f := 0$ . This is consistent with our definitions and theorems thus far as  $\lim_{b\to a} |\int_a^b f| = 0$ .
- 2.  $\int_{a}^{b} f = -\int_{b}^{a} f$ .

## **Fundamental Theorem of Calculus**

**Theorem 250** (Fundamental Theorem of Calculus)

Suppose  $f \in C([a, b])$ .

1. If  $F:[a,b]\to\mathbb{R}$  is differentiable and F'=f, then

$$\int_{a}^{b} f = F(b) - F(a).$$

2. The function  $G(x) := \int_a^x f$  is differentiable on [a,b] and

$$\begin{cases} G' = f \\ G(a) = 0 \end{cases}.$$

Remark 251. We sometimes abbreviate the Fundamental Theorem of Calculus to FTC.

## **Proof**:

1. Let  $\{(\underline{x}(r))\}_r$  be a sequence of partitions with  $\|\underline{x}\| \to 0$ . Then, by the Mean Value Theorem,  $\forall r \forall j$ , there exists a  $\xi_j(r) \in [x_{j-1}(r), x_j(r)]$  such that

$$F(x_i(r)) - F(x_{i-1}(r)) = F'(\xi_i(r))(x_i(r) - x_{i-1}(r)) = f(\xi_i(r))(x_i(r) - x_{i-1}(r)).$$

Thus,

$$\int_{a}^{b} f = \lim_{r \to \infty} \sum_{j=1}^{n(r)} f(\xi_{j}(r))(x_{j}(r) - x_{j-1}(r))$$

$$= \lim_{r \to \infty} \sum_{j=1}^{n(r)} F(x_{j}(r)) - F(x_{j-1}(r))$$

$$= \lim_{r \to \infty} (F(b) - F(a)) = F(b) - F(a).$$

2. Let  $c \in [a, b]$ . We wish to show that

$$\lim_{x \to c} \frac{\int_a^x f - \int_a^c f}{x - c} = f(c).$$

Let  $\epsilon > 0$ . Then, since f is continuous at c,  $\exists \delta_0 > 0$  such that

$$|t-c| < \delta_0 \implies |f(t) - f(c)| < \epsilon/2.$$

Choose  $\delta = \delta_0$ . Suppose  $0 < x - c < \delta$ . If  $t \in [c, x]$ , then

$$|t - c| \le |x - c| < \delta = \delta_0.$$

Thus,

$$\left| \frac{1}{x-c} \int_{c}^{x} f(t) dt - f(c) \right| = \left| \frac{1}{x-c} \int_{c}^{t} f(t) dt - \frac{1}{x-c} \int_{x}^{c} f(c) dt \right|$$

$$= \frac{1}{x-c} \left| \int_{c}^{x} (f(t) - f(c)) dt \right|$$

$$\leq \frac{1}{x-c} \int_{c}^{x} |f(t) - f(c)| dt$$

$$\leq \frac{1}{x-c} \int_{c}^{x} \epsilon/2 dt$$

$$= \frac{1}{x-c} \cdot \frac{\epsilon}{2} (x-c) = \frac{\epsilon}{2}.$$

A similar argument holds for  $0 < c - x < \delta$ . Thus,

$$0 < |x - c| < \delta \implies \left| \frac{\int_a^x f - \int_a^c f}{x - c} - f(c) \right| \le \frac{\epsilon}{2} < \epsilon.$$

Theorem 252 (Integration by Parts)

Suppose  $f,g\in C([a,b])$  and  $f',g'\in C([a,b]).$  Then,

$$\int_a^b f'g = (f(b)g(b) - f(a)g(a)) - int_a^b fg'.$$

**Proof**: We have

$$(fg)' = f'g + fg'.$$

Therefore, by the Fundamental Theorem of Calculus,

$$f(b)g(b) - f(a)g(a) = \int_a^b f'g + \int_a^b fg'.$$

Remark 253. We sometimes abbreviate Integration By Parts as IBP.

Lemma 254 (Riemann-Lebesgue)

Suppose  $f \in C([-\pi, \pi])$  and  $f' \in C([-\pi, \pi])$  with  $f \ 2\pi$ -periodic with  $f(-\pi) = f(\pi)$ . For  $n \in \mathbb{N} \cup \{0\}$ , let

$$a_n = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x) \sin(nx) dx$$
$$b_n = \frac{1}{\pi} \int_{-\pi}^{\pi} f(x) \cos(nx) dx.$$

Then,

$$\lim_{n \to \infty} a_n = \lim_{n \to \infty} b_n = 0.$$

**Definition 255** (Fourier Coefficients)

The  $a_n, b_n$  defined in the above lemma are referred to as the Fourier coefficients of f.

**Proof**: Using IBP, we have

$$|b_n| = \frac{1}{\pi} \left| \int_{-\pi}^{\pi} f(x) \cos(nx) \, dx \right|$$

$$= \frac{1}{\pi} \left| \int_{-\pi}^{\pi} (\frac{1}{n} \sin(nx))' f(x) \, dx \right|$$

$$= \left| \frac{1}{n} (f(\pi) \sin(n\pi) - f(-pi) \sin(n(-\pi))) - \frac{1}{n} \int_{-\pi}^{\pi} \sin(nx) f'(x) \, dx \right|.$$

Notice that  $\sin(n\pi) = \sin(n(-\pi)) = 0$  for all  $n \in \mathbb{N}$ . Hence,

$$|b_n| \le \frac{1}{n} \int_{-\pi}^{\pi} |\sin(nx)| |f'(x)| \, \mathrm{d}x$$
$$\le \frac{1}{n} \int_{-\pi}^{\pi} |f'| \to 0.$$

By the Squeeze Theorem,  $|b_n| \to 0$ . A similar arguments works for  $a_n$ .

Theorem 256 (Change of Variables)

Let  $\varphi:[a,b]\to[c,d]$  be continuously differentiable with  $\varphi'>0$  on  $[a,b],\ \varphi(a)=c,$  and  $\varphi(b)=d.$  Then,

$$\int_{c}^{d} f(u) du = \int_{a}^{b} f(\varphi(x))\varphi'(x) dx.$$

**Proof**: Let  $F:[a,b] \to \mathbb{R}$  such that F'=f. Then,

$$F(\varphi(x))' = f(\varphi(x)).$$

Hence, by the FTC,

$$\int_{a}^{b} f(\varphi(x))\varphi'(x) dx = \int_{a}^{b} F(\varphi(x))' dx$$
$$= F(\varphi(b)) - F(\varphi(a))$$
$$= F(d) - F(c).$$

Furthermore, by the FTC,

$$\int_{c}^{d} f(u) du = \int_{c}^{d} F(u)' du = F(d) - F(c).$$

Pointwise and Uniform Convergence of Sequences of Functions

## **Sequences of Function**

## Power Series

Remark 257. Power series motivate the general discussion of sequences of functions.

## **Definition 258** (Power series)

A power series about  $x_0$  is a series of the form

$$\sum_{m=0}^{\infty} a_m (x - x_0)^m.$$

## Theorem 259

Suppose

$$R = \lim_{m \to \infty} |a_m|^{1/n}$$

exists, and let

$$p = \begin{cases} \frac{1}{R} & R > 0\\ \infty & R = 0. \end{cases}$$

Then,  $\sum a_m(x-x_0)^m$  converges absolutely if  $|x-x_0| < p$  and diverges if  $|x-x_0| > p$ .

## **Definition 260** (Radius of Convergence)

In the above theorem, we define p to be the radius of convergence.

**Proof**: We have

$$\lim_{n \to \infty} |a_m (x - x_0)^m|^{1/m} = R|x - x_0|,$$

and the theorem follows by the Root test.

Suppose  $\sum a_m(x-x_0)^m$  is a power series with radius of convergence p. Furthermore, define  $f:(x_0-p,x_0+p)\to\mathbb{R}$  such that

$$f(x) := \sum_{m=0}^{\infty} a_m (x - x_0)^m.$$

Then, f is a limit of a sequence of functions

$$f(x) = \lim_{n \to \infty} f_n(x),$$

for  $x \in (x_0 - p, x_0 + p)$  and where

$$f_n(x) = \sum_{m=0}^n a_m (x - x_0)^m.$$

## Example 261

For example, we have

$$f(x) = \frac{1}{1-x} = \sum_{m=0}^{\infty} x^m.$$

Question 262. This concept begs a number of questions:

- 1. Is f continuous?
- 2. Is f differentiable, and does  $f' = \lim_{n \to \infty} f'_n$ ?
- 3. If 1. is true, does

$$\int_{a}^{b} f = \lim_{n \to \infty} \int_{a}^{b} f_{n}?$$

These questions will be the key motivator for the last section of this course.

## Pointwise and Uniform Convergence

We now consider a setting far more general than power series.

## **Definition 263** (Pointwise Convergence)

For  $n \in \mathbb{N}$ , let  $f_n : S \to \mathbb{R}$ . Let  $f : S \to \mathbb{R}$ . We say that  $\{f_n\}$  converges pointwise to f if for all  $x \in S$ ,

$$\lim_{n \to \infty} f_n(x) = f(x).$$

Let's consider some examples.

1. Let  $f_n(x) = x^n$  on [0,1]. Then,

$$\lim_{n \to \infty} f_n(x) = \begin{cases} 0 & x \in [0, 1) \\ 1 & x = 1 \end{cases}.$$

Thus,  $\{f_n\}$  converges to the above pointwise function. Hence, notice that a sequence of continuous functions may not converge pointwise to a continuous function!

2. Let  $f_n(x) = \sum_{m=0}^n x^m$  for  $x \in (-1, 1)$ . Then,

$$\lim_{n \to \infty} f_n(x) = \lim_{n \to \infty} \sum_{m=0}^{n} x^m = \frac{1}{1 - x}.$$

Hence, pointwise, this sequence converges to its power series (see the above example).

3. Let  $f_n(x):[0,1]\to\mathbb{R}$  be defined by

$$f_n(x) = \begin{cases} 4n^2x & x \in [0, \frac{1}{2n}] \\ 4n - 4n^2x & x \in [\frac{1}{2n}, \frac{1}{n}] \\ 0 & x \in [\frac{1}{n}, 1] \end{cases}$$

We can picture this sequence (on the next page)

Then,  $\lim_{n\to\infty} f_n(0) = \lim_{n\to\infty} 0 = 0$ . Let  $x \in (0,1]$ . Let  $N \in \mathbb{N}$  such that  $\frac{1}{N} < x$ . Then, for all  $n \ge N$ ,


$$f_n(x) = 0.$$

Therefore,

$${f_n(x)} = f_1(x), \dots, f_{N-1}(x), 0, 0, 0, \dots$$

Hence,  $\lim_{n\to\infty} f_n(x) = 0$  for all  $x \in [0,1]$ . Thus,  $\{f_n\}$  converges pointwise to f(x) = 0 on [0,1].

## **Definition 264** (Uniform Convergence)

For  $n \in \mathbb{N}$ , let  $f_n : S \to \mathbb{R}$ , and let  $f : S \to \mathbb{R}$ . Then, we say  $f_n$  converges to f uniformly or **converges** uniformly to f if  $\forall \epsilon > 0 \ \exists M \in \mathbb{N}$  such that for all  $n \geq M \ \forall x \in S$ ,

$$|f_n(x) - f(x)| < \epsilon$$

## Theorem 265

If  $f_n: S \to \mathbb{R}$ ,  $f: S \to \mathbb{R}$ , and  $f_n \to f$  uniformly, then  $f_n \to f$  pointwise.

**Proof**: Let  $c \in S$  and let  $\epsilon > 0$ . Then,  $f_n \to f$  uniformly implies that there exists  $M_0 \in \mathbb{N}$  such that for all  $n \geq M, \forall x \in S, |f_n(x) - f(x)| < \epsilon$ . Choose  $M = M_0$ . Then,  $\forall n \geq M$ ,

$$|f_n(c) - f(c)| < \epsilon.$$

Thus,  $\lim_{n\to\infty} f_n(c) = f(c)$  for all  $c \in S$ , and therefore  $f_n \to f$  pointwise.

Uniform Convergence, the Weierstrass M-Test, and Interchanging Limits

## Theorem 266

Let  $f_n(x) = x^n$ , and let  $f(x) = \begin{cases} 0 & x \in [0, 1) \\ 1 & x = 1 \end{cases}$ .

- 1.  $\forall 0 < b < 1, f_n \to f$  uniformly on [0, b].
- 2.  $f_n$  does not converge to f uniformly on [0,1].

## **Proof**:

1. Let  $\epsilon > 0$ . Since  $b \in (0,1)$ ,  $b^n \to 0$ . Therefore,  $\exists M_0 \in \mathbb{N}$  such that for all  $n \geq M_0$ ,  $b^n < \epsilon$ . Choose  $M = M_0$ . Then,  $\forall n \geq M, \forall x \in [0,b]$ ,

$$|f_n(x) - f(x)| = |f_n(x)| = x^n \le b^n < \epsilon.$$

Thus,  $f_n \to f$  uniformly on [0, b].

Before proving the other part, we first note the following negation:

## Negation 267 (Not Uniformly Convergent)

 $f_n: S \to \mathbb{R}$  does not converge to  $f: S \to \mathbb{R}$  uniformly if  $\exists \epsilon_0 > 0$  such that  $\forall M \in \mathbb{N}, \exists n \geq M$  and  $\exists x \in S$  with  $|f_n(x) - f(x)| \geq \epsilon_0$ .

2. Hence, for our example, choose  $\epsilon_0 = \frac{1}{4}$ . Let  $M \in \mathbb{N}$  and choose  $x = \left(\frac{1}{2}\right)^{\frac{1}{M}} \in (0,1)$ . Thus,

$$|f_M(x) - f(x)| = f_M(x) = \frac{1}{2} > \epsilon_0.$$

## Theorem 268 (Weierstrass M-test)

let  $f_j: S \to \mathbb{R}$  and suppose  $\exists M_j > 0$  such that

- a)  $\forall x \in S, |f_j(x)| \leq M_j$ .
- b)  $\sum_{j=1}^{\infty} M_j$  converges.

Then,

- 1.  $\forall x \in S, \sum_{j=1}^{\infty} f_j(x)$  converges absolutely.
- 2. Let  $f(x) = \sum_{j=1}^{\infty} f_j(x)$  for  $x \in S$ . Then,

$$\sum_{j=1}^{n} f_j \to f \text{ uniformly on } S.$$

## Proof:

1. The first part follows from a), b), and the Comparison Test.

2. Let  $\epsilon > 0$ . Since  $\sum M_j$  converges,  $\exists N_0 \in \mathbb{N}$  such that  $\forall n \geq N_0$ ,

$$\sum_{j=n+1}^{\infty} M_j = \left| \sum_{j=1}^{\infty} M_j - \sum_{j=1}^n M_j \right| < \epsilon.$$

Choose  $N = N_0$ . Then, for all  $n \ge N$  and  $\forall x \in S$ ,

$$\left| f(x) - \sum_{j=1}^{n} f_j(x) \right| = \left| \sum_{j=n+1}^{\infty} f_j(x) \right|$$

$$\leq \sum_{j=n+1}^{\infty} |f_j(x)|$$

$$\leq \sum_{j=n+1}^{\infty} M_j < \epsilon.$$

Thus,  $\sum_{j=1}^{n} f_j \to f$  uniformly on S.

## Interchange of Limits

Remark 269. In general, limits cannot be interchanged.

## Example 270

For instance, consider the following example:

$$\begin{split} \lim_{n\to\infty} \lim_{k\to\infty} \frac{n/k}{n/k+1} &= \lim_{n\to\infty} \frac{0}{0+1} = 0 \\ \lim_{k\to\infty} \lim_{n\to\infty} \frac{n/k}{n/k+1} &= \lim_{k\to\infty} 1 = 1. \end{split}$$

Question 271. Hence, we ask three questions about interchanging limits:

- 1. If  $f_n: S \to \mathbb{R}$ ,  $f_n$  continuous and  $f_n \to f$  pointwise or uniform, then is f continuous?
- 2. If  $f_n:[a,b]\to\mathbb{R}$ ,  $f_n$  differentiable, and  $f_n\to f$  with  $f'_n\to g$ , then is f differentiable and does g=f'?
- 3. If  $f_n:[a,b]\to\mathbb{R}$ , with  $f_n$  and f continuous such that  $f_n\to f$ , then does

$$\int_a^b f_n = \int_a^b f?$$

The answer to the above questions are all **yes**, if the convergence is uniform.

Question 272. What if the convergence is only pointwise?

If convergence is only pointwise, the answer to the above questions are all **no**, which we will show next time.

## Power Series and the Weierstrass Approximation Theorem

Last time, we asked three questions about interchanging limits:

Question 273. Hence, we ask three questions about interchanging limits:

- 1. If  $f_n: S \to \mathbb{R}$ ,  $f_n$  continuous and  $f_n \to f$  pointwise or uniform, then is f continuous?
- 2. If  $f_n:[a,b]\to\mathbb{R}$ ,  $f_n$  differentiable, and  $f_n\to f$  with  $f'_n\to g$ , then is f differentiable and does g=f'?
- 3. If  $f_n:[a,b]\to\mathbb{R}$ , with  $f_n$  and f continuous such that  $f_n\to f$ , then does

$$\int_a^b f_n = \int_a^b f?$$

The answer to the above questions are all **no**, if the convergence is pointwise as seen by the following counterexamples:

- 1. Let  $f_n(x) = x^n$  on [0,1] is continuous  $\forall n$ . As we noted earlier,  $f_n(x) \to f(x) = \begin{cases} 0 & x \in [0,1) \\ 1 & x = 1 \end{cases}$ . Notice that f is not continuous.
- 2. Let  $f_n(x) = \frac{x^{n+1}}{n+1}$  on [0,1]. Then,  $f_n \to 0$  pointwise on [0,1]. However,

$$f'_n(x) \to g(x) = \begin{cases} 0 & x \in [0,1) \\ 1 & x = 1 \end{cases}$$
.

Thus,  $g(x) \neq (0)' = 0$  at x = 1.

3. Consider the functions

$$f_n(x) = \begin{cases} 4n^2x & x \in [0, \frac{1}{2n}] \\ 4n - 4n^2x & x \in [\frac{1}{2n}, \frac{1}{n}] \\ 0 & x \in [\frac{1}{n}, 1] \end{cases}$$

as described in the previous lecture. Then,  $f_n(x) \to 0$  pointwise on [0,1] as we showed last time. However,

$$\int_{0}^{1} f_{n} = \frac{1}{2} (\text{base})(\text{height}) = \frac{1}{2n} \cdot 2n = 1 \neq 0 = \int_{0}^{1} 0.$$

We now prove that the answer to the three questions above is yes if convergence is uniform.

## Theorem 274

If  $f_n: S \to \mathbb{R}$  is continuous for all  $n, f: S \to \mathbb{R}$ , and  $f_n \to f$  uniformly, then f is continuous.

**Proof**: Let  $c \in S$  and let  $\epsilon > 0$ . Since  $f_n \to f$  uniformly,  $\exists M \in \mathbb{N}$  such that  $\forall n \geq M, \forall y \in S$ ,

$$|f_n(y) - f(y)| < \frac{\epsilon}{3}$$

Since  $f_M: S \to \mathbb{R}$  is continuous,  $\exists \delta_0 > 0$  such that  $\forall |x - c| < \delta_0$ ,

$$|f_M(x) - f_M(c)| < \frac{\epsilon}{3}.$$

Choose  $\delta = \delta_0$ . If  $|x - c| < \delta$ , then

$$|f(x) - f(c)| \le |f(x) + f_M(x)| + |f_M(c) - f(c)| + |f_M(x) - f_M(c)|$$
  
 $< \frac{\epsilon}{3} + \frac{\epsilon}{3} + \frac{\epsilon}{3} = \epsilon.$ 

## Theorem 275

If  $f_n:[a,b]\to\mathbb{R}$  is continuous for all  $n,\,f:[a,b]\to\mathbb{R}$  and  $f_n\to f$  uniformly, then

$$\int_a^b f_n \to \int_a^b f.$$

**Proof**: Let  $\epsilon > 0$ . Since  $f_n \to f$  uniform,  $\exists M_0 \in \mathbb{N}$  such that  $\forall n \geq M_0, \forall x \in [a, b]$ ,

$$|f_n(x) - f(x)| < \frac{\epsilon}{b-a}.$$

Then, for all  $n \geq M = M_0$ , we have

$$\left| \int_{a}^{b} f_{n} - \int_{a}^{b} f \right| \leq \int_{a}^{b} |f_{n} - f| < \int_{a}^{b} \frac{\epsilon}{b - a} = \epsilon.$$

Remark 276. Notationally, this states that

$$\lim_{n \to \infty} \int_a^b f_n = \int_a^b \lim_{n \to \infty} f_n = \int_a^b f.$$

## Theorem 277

If  $f_n:[a,b]\to\mathbb{R}$  is continuously differentiable,  $f:[a,b]\to\mathbb{R},\,g:[a,b]\to\mathbb{R},$  and

$$f_n \to f$$
 pointwise,

$$f'_n \to g$$
 uniformly,

then f is continuously differentiable and g = f'.

**Proof**: By the FTC,  $\forall n \forall x \in [a, b]$ ,

$$f_n(x) - f_n(a) = \int_a^x f_n'.$$

Thus, by the previous two theorems,

$$f(x) - f(a) = \lim_{n \to \infty} (f_n(x) - f_n(a))$$
$$= \lim_{n \to \infty} \int_a^x f'_n$$
$$= \int_a^x g.$$

Therefore,  $f(x) = f(a) + \int_a^x g$ . Thus, by the FTC, f is differentiable and  $f' = (\int_a^x g)' = g$ .

We now return back to our study of power series, answering some questions we asked at the beginning of Lecture 23.

#### Theorem 278

Let  $\sum_{j=0}^{\infty} a_j(x-x_0)^j$  be a power series of radius of convergence  $p \in (0,\infty]$ . Then,  $\forall r \in (0,p), \sum_{j=0}^{\infty} a_j(x-x_0)^j$  converges uniformly on  $[x_0-r,x_0+r]$ .

**Proof**: Let  $r \in [0, p)$ . Then,  $\forall j \in \mathbb{N} \cup \{0\}, \forall x \in [x_0 - r, x_0 + r],$ 

$$|a_i(x-x_0)^j| \le |a_i|r^j =: M_i.$$

Now,

$$\lim_{j \to \infty} j \to \infty M_j^{1/j} = \lim_{j \to \infty} |a_j|^{1/j} r = \begin{cases} \frac{r}{p} & p < \infty \\ 0 & p = \infty \end{cases}$$

since  $p^{-1} = \lim_{j \to \infty} |a_j|^{1/j}$ . Since r < p, we have

$$\lim_{j \to \infty} M_j^{1/j} < 1 \implies \sum_{j=0}^{\infty} M_j \text{ converges.}$$

By the Weierstrass M-test, it follows that  $\sum_{j=0}^{\infty} a_j(x-x_0)^j$  converges uniformly on  $[x_0-r,x_0+r]$ .

## Theorem 279

Let  $\sum_{j=0}^{\infty} a_j(x-x_0)^j$  be a power series with radius of convergence  $p \in (0,\infty]$ . Then,

1.  $\forall c \in (x_0 - p, x_0 + p), \sum_{j=0}^{\infty} a_j (x - x_0)^j$  is differentiable at c and

$$\frac{\mathrm{d}}{\mathrm{d}x} \sum_{j=0}^{\infty} a_j (x - x_0)^j = \sum_{j=0}^{\infty} j a_j (x - x_0)^{j-1}.$$

2.  $\forall a, b \text{ such that } x_0 - p < a < b < x_0 + p,$ 

$$\int_{a}^{b} \sum_{j=0}^{\infty} a_{J}(x - x_{0})^{j} dx = \sum_{j=0}^{\infty} a_{j} \left( \frac{(b - x_{0})^{j+1}}{j+1} - \frac{(a - x_{0})^{j+1}}{j+1} \right).$$

Remark 280. Since

$$\lim_{j \to \infty} ((j+1)|a_{j+1}|)^{1/j} = \lim_{j \to \infty} \left( ((j+1)|a_{j+1}|^{1/(j+1)})^{(j+1)/j} = \lim_{k \to \infty} |a_k|^{1/k} = p,$$

1. implies  $\sum a_j(x-x_0)^j$  is infinitely differentiable and

$$k!a_k = \left(\frac{\mathrm{d}^k}{\mathrm{d}x^k} \sum a_j (x - x_0)^j\right)\Big|_{x = x_0}.$$

## Weierstrass Approximation Theorem

**Remark 281.** This theorem essentially states: "Every continuous function on [a,b] is almost a polynomial."

**Theorem 282** (Weierstrass Approximation Theorem)

If  $f \in C([a,b])$ , there exists a sequence of polynomials  $\{P_n\}$  such that

$$P_n \to f$$
 uniformly on  $[a, b]$ .

The idea of the proof is to choose a suitable sequence of polynomials  $\{Q_n\}_n$  such that  $Q_n$  behaves like a 'Dirac delta function' as  $nto\infty$ . Then, the sequence of polynomials  $P_n(x) = \int_0^1 Q_n(x-t)f(t) dt$  converges to f(x) as  $n \to \infty$ . We will prove this momentarily, but first we need to do the ground work.

Notice that we only need to consider a = 0 and b = 1, with f(0) = f(1) = 0. If we prove this case, then for a general  $\tilde{f} \in C([0,1])$ ,  $\exists$  a sequence of polynomials

$$P_n(x) \to \tilde{f}(x) - \tilde{f}(0) - x(\tilde{f}(1) - \tilde{f}(0))$$
 uniformly.

Hence,

$$\tilde{P}_n(x) = P_n(x) + \tilde{f}(0) + x(\tilde{f}(1) - \tilde{f}(0)) \rightarrow \tilde{f}(x)$$
 uniformly.

## Theorem 283

Let  $c_n := (\int_{-1}^1 (1 - x^2)^n dx)^{-1} > 0$ , and let

$$Q_n(x) = c_n(1 - x^2)^n.$$

Then,

- 1.  $\forall n, \int_{-1}^{1} Q_n = 1.$
- 2.  $\forall n, Q_n(x) \ge 0 \text{ on } [-1, 1], \text{ and }$
- 3.  $\forall \delta \in (0,1), Q_n \to 0$  uniformly on  $\delta \leq |x| \leq 1$ .

Before we prove this, here is a picture of  $Q_n$ :

#### **Proof**:

- 2. Immediately clear.
- 1.  $\int_{-1}^{1} Q_n = c_n \int_{-1}^{1} (1 x^2)^n dx = 1$  by definition of  $c_n$ .
- 3. We first estimate  $c_n$ . We have for all  $n \in \mathbb{N}$  and  $\forall x \in [-1, 1]$ ,

$$(1 - x^2)^n \ge 1 - nx^2.$$

We proved this way earlier in the course by induction, but it also follows from the calculus we have proven as

$$g(x) = (1 - x^2)^n - (1 - nx^2)$$

satisfies g(0) = 0, and

$$g'(x) = n \cdot 2x(1 - (1 - x^2)^{n-1}) \ge 0$$

in [0,1]. Thus,  $g(x) \ge 0$  by the MVT.

Then,

$$\frac{1}{c_n} = \int_{-1}^{1} (1 - x^2)^n \, dx$$

$$= 2 \int_{0}^{1} (1 - x^2)^n \, dx$$

$$> 2 \int_{0}^{1/\sqrt{n}} (1 - x^2)^n \, dx$$

$$\ge 2 \int_{0}^{1/\sqrt{n}} (1 - nx^2) \, dx$$

$$= 2 \left( \frac{1}{\sqrt{n}} - \frac{n}{3} \cdot n^{-3/2} \right)$$

$$= \frac{4}{3} \sqrt{n} > \sqrt{n}.$$

Therefore,  $c_n < \sqrt{n}$ .

Let  $\delta > 0$ . We note  $\lim_{n \to \infty} \sqrt{n} (1 - \delta^2)^n = 0$ . Then,

$$\lim_{n \to \infty} (\sqrt{n} (1 - \delta^2)^n)^{1/n} = \lim_{n \to \infty} (n^{1/n})^{1/2} (1 - \delta^2)$$
$$= 1 - \delta^2 < 1.$$

Therefore,

$$\lim_{n \to \infty} \sqrt{n} (1 - \delta^2)^n = 0.$$

Let  $\epsilon > 0$ , and choose  $M \in \mathbb{N}$  such that for all  $n \geq M$ ,

$$\sqrt{n}(1-\delta^2)^n < \epsilon.$$

Then,  $\forall n \geq M$  and  $\forall \delta \leq |x| \leq 1$ ,

$$|c_n(1-x^2)^n| < \sqrt{n}(1-x^2)^n \le \sqrt{n}(1-\delta^2)^n < \epsilon.$$

We now prove the Weierstrass Approximation Theorem.

**Proof**: Suppose  $f \in C([0,1])$ , f(0) = f(1) = 0. We extend f to an element of  $C(\mathbb{R})$  by setting f(x) = 0 for all  $x \notin [0,1]$ . We furthermore define

$$P_n(x) = \int_0^1 f(t)Q_n(t-x) dt$$
$$= \int_0^1 f(t)c_n(1-(t-x)^2)^n dt.$$

Note that  $P_n(x)$  is in fact a polynomial.

Furthermore, observe that for  $x \in [0, 1]$ ,

$$P_n(x) = \int_0^1 f(t)Q_n(t-x) dt$$
$$= \int_{-x}^{1-x} f(x+t)Q_n(t) dt$$
$$= \int_{-1}^1 f(x+t)Q_n(t) dt.$$

The second equality is true by a change of variable, and the last equality is true as f(x+t) = 0 for  $t \notin [-x, 1-x]$ .

We now prove  $P_n \to f$  uniformly on [0,1]. Let  $\epsilon > 0$ . Since f is uniformly continuous on [0,1],  $\exists \delta > 0$  such that  $\forall |x-y| \leq \delta$ ,  $|f(x)-f(y)| < \frac{\epsilon}{2}$ . Let  $C = \sup\{f(x) \mid x \in [0,1]\}$ , which exists by the Min/Max theorem i.e. the EVT. Choose  $M \in \mathbb{N}$  such that  $\forall n \geq M$ ,

$$\sqrt{n}(1-\delta^2)^n < \frac{\epsilon}{8C}.$$

Thus,  $\forall n \geq M, \forall x \in [0,1]$ , by the previous theorem,

$$\begin{split} |P_n(x) - f(x)| &= \left| \int_{-1}^1 (f(x-t) - f(t)) Q_n(t) \, \mathrm{d}t \right| \\ &\leq \int_{-1}^1 |f(x-t) - f(x)| Q_n(t) \, \mathrm{d}t \\ &\leq \int_{|t| \leq \delta} |f(x-t) - f(x)| Q_n(t) \, \mathrm{d}t + \int_{\delta \leq |t| \leq 1} |f(x-t) - f(x)| Q_n(t) \, \mathrm{d}t \\ &\leq \frac{\epsilon}{2} \int_{|t| \leq \delta} Q_n(t) \, \mathrm{d}t + \sqrt{n} (1 - \delta^2)^n \int_{\|\delta| \leq |t| \leq 1} 2C \\ &< \frac{\epsilon}{2} + 4C\sqrt{n} (1 - \delta^2)^n \\ &< \frac{\epsilon}{2} + \frac{\epsilon}{2} = \epsilon. \end{split}$$

In the last minute of the course, Casey Rodriguez stated: "This was quite an experience; teaching to an empty room. I hope you did get something out of this class. Unfortunately I wasn't able to meet a lot of you, and that's one of the best parts of teaching...."

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.100A / 18.1001 Real Analysis Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.