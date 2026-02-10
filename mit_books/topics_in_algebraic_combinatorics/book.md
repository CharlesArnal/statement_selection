## 8 A glimpse of Young tableaux.

We defined in Section 6 Young's lattice Y, the poset of all partitions of all nonnegative integers, ordered by containment of their Young diagrams.

Young's lattice

Here we will be concerned with the counting of certain walks in the Hasse diagram (considered as a graph) of Y. Note that since Y is infinite, we cannot talk about its eigenvalues and eigenvectors. We need different techniques for counting walks. (It will be convenient to denote the length of a walk by n, rather than by  $\ell$  as in previous sections.)

Note that Y is a graded poset (of infinite rank), with  $Y_i$  consisting of all partitions of i. In other words, we have  $Y = Y_0 \cup Y_1 \cup \cdots$  (disjoint union), where every maximal chain intersects each level  $Y_i$  exactly once. We call  $Y_i$  the ith level of Y.

Since the Hasse diagram of Y is a simple graph (no loops or multiple edges), a walk of length n is specified by a sequence  $\lambda^0, \lambda^1, \ldots, \lambda^n$  of vertices

of Y. We will call a walk in the Hasse diagram of a poset a Hasse walk. Each  $\lambda^i$  is a partition of some integer, and we have either (a)  $\lambda^i < \lambda^{i+1}$  and  $|\lambda^i| = |\lambda^{i+1}| - 1$ , or (b)  $\lambda^i > \lambda^{i+1}$  and  $|\lambda^i| = |\lambda^{i+1}| + 1$ . A step of type (a) is denoted by U (for "up," since we move up in the Hasse diagram), while a step of type (b) is denoted by D (for "down"). If the walk W has steps of types  $A_1, A_2, \ldots, A_n$ , respectively, where each  $A_i$  is either U or D, then we say that W is of type  $A_n A_{n-1} \cdots A_2 A_1$ . Note that the type of a walk is written in the opposite order to that of the walk. This is because we will soon regard U and D as linear transformations, and we multiply linear transformations right-to-left (opposite to the usual left-to-right reading order). For instance (abbreviating a partition  $(\lambda_1, \ldots, \lambda_m)$  as  $\lambda_1 \cdots \lambda_m$ ), the walk  $\emptyset, 1, 2, 1, 11, 111, 211, 221, 22, 21, 31, 41$  is of type  $UUDDUUUUDUU = U^2D^2U^4DU^2$ .

There is a nice combinatorial interpretation of walks of type  $U^n$  which begin at  $\emptyset$ . Such walks are of course just saturated chains  $\emptyset = \lambda^0 < \lambda^1 < \cdots < \lambda^n$ . In other words, they may be regarded as sequences of Young diagrams, beginning with the empty diagram and adding one new square at each step. An example of a walk of type  $U^5$  is given by

We can specify this walk by taking the final diagram and inserting an i into square s if s was added at the ith step. Thus the above walk is encoded by the "tableau"

| 1 | 2 |  |  |  |  |
|---|---|--|--|--|--|
| 3 | 5 |  |  |  |  |
| 4 |   |  |  |  |  |

Such an object  $\tau$  is called a *standard Young tableaux* (or SYT). It consists of the Young diagram D of some partition  $\lambda$  of an integer n, together with the numbers  $1, 2, \ldots, n$  inserted into the squares of D, so that each number appears exactly once, and every row and column is *increasing*. We call  $\lambda$  the shape of the SYT  $\tau$ , denoted  $\lambda = \operatorname{sh}(\tau)$ . For instance, there are five SYT of

shape (2,2,1), given by

| 1 | 2 | 1 | 2 | 1 | 3 |   | 1 | 3 | 1 | 4 |
|---|---|---|---|---|---|---|---|---|---|---|
| 3 | 4 | 3 | 5 | 2 | 4 |   | 2 | 5 | 2 | 5 |
| 5 |   | 4 |   | 5 |   | - | 4 |   | 3 |   |

Let  $f^{\lambda}$  denote the number of SYT of shape  $\lambda$ , so for instance  $f^{(2,2,1)}=5$ . The numbers  $f^{\lambda}$  have many interesting properties; for instance, there is a famous explicit formula for them known as the Frame-Robinson-Thrall hook formula. We will be concerned with their connection to counting walks in Young's lattice. If  $w=A_nA_{n-1}\cdots A_1$  is some word in U and D and  $\lambda \vdash n$ , then let us write  $\alpha(w,\lambda)$  for the number of Hasse walks in Y of type w which start at the empty partition  $\emptyset$  and end at  $\lambda$ . For instance,  $\alpha(UDUU,11)=2$ , the corresponding walks being  $\emptyset,1,2,1,11$  and  $\emptyset,1,11,1,11$ . Thus in particular  $\alpha(U^n,\lambda)=f^{\lambda}$  [why?]. In a similar fashion, since the number of Hasse walks of type  $D^nU^n$  which begin at  $\emptyset$ , go up to a partition  $\lambda \vdash n$ , and then back down to  $\emptyset$  is given by  $(f^{\lambda})^2$ , we have

$$\alpha(D^n U^n, \emptyset) = \sum_{\lambda \vdash n} (f^{\lambda})^2. \tag{40}$$

Our object is to find an explicit formula for  $\alpha(w,\lambda)$  of the form  $f^{\lambda}c_w$ , where  $c_w$  does not depend on  $\lambda$ . (It is by no means a priori obvious that such a formula should exist.) In particular, since  $f^{\emptyset} = 1$ , we will obtain by setting  $\lambda = \emptyset$  a simple formula for the number of (closed) Hasse walks of type w from  $\emptyset$  to  $\emptyset$  (thus including a simple formula for (40)).

There is an easy condition for the existence of any Hasse walks of type w from  $\emptyset$  to  $\lambda$ , given by the next lemma.

**8.1 Lemma.** Suppose  $w = D^{s_k}U^{r_k} \cdots D^{s_2}U^{r_2}D^{s_1}U^{r_1}$ , where  $r_i \geq 0$  and  $s_i \geq 0$ . Let  $\lambda \vdash n$ . Then there exists a Hasse walk of type w from  $\emptyset$  to  $\lambda$  if and only if:

$$\sum_{i=1}^{k} (r_i - s_i) = n$$

$$\sum_{i=1}^{j} (r_i - s_i) \ge 0 \text{ for } 1 \le j \le k.$$

**Proof.** Since each U moves up one level and each D moves down one level, we see that  $\sum_{i=1}^k (r_i - s_i)$  is the level at which a walk of type w beginning at  $\emptyset$  ends. Hence  $\sum_{i=1}^k (r_i - s_i) = |\lambda| = n$ .

After  $\sum_{i=1}^{j} (r_i + s_i)$  steps we will be at level  $\sum_{i=1}^{j} (r_i - s_i)$ . Since the lowest level is level 0, we must have  $\sum_{i=1}^{j} (r_i - s_i) \ge 0$  for  $1 \le j \le k$ .

The easy proof that the two conditions of the lemma are *sufficient* for the existence of a Hasse walk of type w from  $\emptyset$  to  $\lambda$  is left to the reader.  $\square$ 

If w is a word in U and D satisfying the conditions of Lemma 8.1, then we say that w is a valid  $\lambda$ -word. (Note that the condition of being a valid  $\lambda$ -word depends only on  $|\lambda|$ .)

The proof of our formula for  $\alpha(w, \lambda)$  will be based on linear transformations analogous to those defined by (18) and (19). As in Section 4 let  $\mathbb{R}Y_j$  be the real vector space with basis  $Y_j$ . Define two linear transformations  $U_i : \mathbb{R}Y_i \to \mathbb{R}Y_{i+1}$  and  $D_i : \mathbb{R}Y_i \to \mathbb{R}Y_{i-1}$  by

$$U_i(\lambda) = \sum_{\substack{\mu \vdash i+1\\ \lambda < \mu}} \mu$$

$$D_i(\lambda) = \sum_{\substack{\nu \vdash i-1 \\ \nu \le \lambda}} \nu,$$

for all  $\lambda \vdash i$ . For instance (using abbreviated notation for partitions)

 $U_{21}(54422211) = 64422211 + 55422211 + 54432211 + 54422221 + 544222111$ 

$$D_{21}(54422211) = 44422211 + 54322211 + 54422111 + 5442221.$$

It is clear [why?] that if r is the number of distinct (i.e., unequal) parts of  $\lambda$ , then  $U_i(\lambda)$  is a sum of r+1 terms and  $D_i(\lambda)$  is a sum of r terms. The next lemma is an analogue for Y of the corresponding result for  $B_n$  (Lemma 4.6).

**8.2 Lemma.** For any  $i \ge 0$  we have

$$D_{i+1}U_i - U_{i-1}D_i = I_i, (41)$$

the identity linear transformation on  $\mathbb{R}Y_i$ .

**Proof.** Apply the left-hand side of (41) to a partition  $\lambda$  of i, expand in terms of the basis  $Y_i$ , and consider the coefficient of a partition  $\mu$ . If  $\mu \neq \lambda$  and  $\mu$  can be obtained from  $\lambda$  by adding one square s to (the Young diagram of)  $\lambda$  and then removing a (necessarily different) square t, then there is exactly one choice of s and t. Hence the coefficient of  $\mu$  in  $D_{i+1}U_i(\lambda)$  is equal to 1. But then there is exactly one way to remove a square from  $\lambda$  and then add a square to get  $\mu$ , namely, remove t and add s. Hence the coefficient of  $\mu$  in  $U_{i-1}D_i(\lambda)$  is also 1, so the coefficient of  $\mu$  when the left-hand side of (41) is applied to  $\lambda$  is 0.

If now  $\mu \neq \lambda$  and we cannot obtain  $\mu$  by adding a square and then deleting a square from  $\lambda$  (i.e.,  $\mu$  and  $\lambda$  differ in more than two rows), then clearly when we apply the left-hand side of (41) to  $\lambda$ , the coefficient of  $\mu$  will be 0.

Finally consider the case  $\lambda = \mu$ . Let r be the number of distinct (unequal) parts of  $\lambda$ . Then the coefficient of  $\lambda$  in  $D_{i+1}U_i(\lambda)$  is r+1, while the coefficient of  $\lambda$  in  $U_{i-1}D_i(\lambda)$  is r, since there are r+1 ways to add a square to  $\lambda$  and then remove it, while there are r ways to remove a square and then add it back in. Hence when we apply the left-hand side of (41) to  $\lambda$ , the coefficient of  $\lambda$  is equal to 1.

Combining the conclusions of the three cases just considered shows that the left-hand side of (41) is just  $I_i$ , as was to be proved.  $\square$ 

We come to one of the main results of this section.

**8.3 Theorem.** Let  $\lambda$  be a partition and  $w = A_n A_{n-1} \cdots A_1$  a valid  $\lambda$ -word. Let  $S_w = \{i : A_i = D\}$ . For each  $i \in S_w$ , let  $a_i$  be the number of D's in w to the right of  $A_i$ , and let  $b_i$  be the number of U's in w to the right of  $A_i$ . Then

$$\alpha(w,\lambda) = f^{\lambda} \prod_{i \in S_w} (b_i - a_i). \tag{42}$$

Before proving Theorem 8.3, let us give an example. Suppose  $w = U^3D^2U^2DU^3 = UUUDDUUDUUU$  and  $\lambda = (2, 2, 1)$ . Then  $S_w = \{4, 7, 8\}$  and  $a_4 = 0$ ,  $b_4 = 3$ ,  $a_7 = 1$ ,  $b_7 = 5$ ,  $a_8 = 2$ ,  $b_8 = 5$ . We have also seen earlier that  $f^{221} = 5$ . Thus

$$\alpha(w,\lambda) = 5(3-0)(5-1)(5-2) = 180.$$

**Proof of Theorem 8.3.** Write  $[\lambda]f$  for the coefficient of  $\lambda$  in  $f \in \mathbb{R}Y_i$ . We illustrate the proof for the special case  $w = DU^{\gamma}DU^{\beta}DU^{\alpha}$ , where  $\alpha, \beta, \gamma \geq 0$ , from which the general case will be clear. By the definition of w we have

$$\begin{array}{rcl} \alpha(w,\lambda) & = & [\lambda]w(\varnothing) \\ & = & [\lambda]DU^{\gamma}DU^{\beta}DU^{\alpha}(\varnothing). \end{array}$$

We will use the identity (easily proved by induction on i)

$$DU^i = U^i D + iU^{i-1}. (43)$$

Thus

$$w(\emptyset) = DU^{\gamma}DU^{\beta}DU^{\alpha}(\emptyset)$$
  
=  $DU^{\gamma}DU^{\beta}(U^{\alpha}D + \alpha U^{\alpha-1})(\emptyset)$   
=  $\alpha DU^{\gamma}DU^{\alpha+\beta-1}(\emptyset),$ 

since  $D(\emptyset) = 0$ . Continuing, we obtain

$$\begin{split} w(\varnothing) &= \alpha D U^{\gamma} (U^{\alpha+\beta-1}D + (\alpha+\beta-1)U^{\alpha+\beta-2})(\varnothing) \\ &= \alpha(\alpha+\beta-1)DU^{\alpha+\beta+\gamma-2}(\varnothing) \\ &= \alpha(\alpha+\beta-1)(U^{\alpha+\beta+\gamma-2}D + (\alpha+\beta+\gamma-2)U^{\alpha+\beta+\gamma-3})(\varnothing) \\ &= \alpha(\alpha+\beta-1)(\alpha+\beta+\gamma-2)U^{\alpha+\beta+\gamma-3}(\varnothing). \end{split}$$

The coefficient of  $\lambda$  in  $U^{\alpha+\beta+\gamma-3}(\emptyset)$  is  $f^{\lambda}$ , so we get

$$[\lambda]DU^{\gamma}DU^{\beta}DU^{\alpha}(\emptyset) = \alpha(\alpha + \beta - 1)(\alpha + \beta + \gamma - 2)f^{\lambda},$$

which is equivalent to (42).  $\square$ 

An interesting special case of the previous theorem allows us to evaluate equation (40).

**8.4 Corollary.** We have

$$\alpha(D^nU^n,\emptyset) = \sum_{\lambda \vdash n} (f^{\lambda})^2 = n!$$

**Proof.** When  $w = D^n U^n$  in Theorem 8.3 we have  $S_w = \{n+1, n+2, \ldots, 2n\}$ ,  $a_i = n-i$ , and  $b_i = n$ , from which the proof is immediate.  $\square$ 

NOTE (for those familiar with the representation theory of finite groups). It can be shown that the numbers  $f^{\lambda}$ , for  $\lambda \vdash n$ , are the degrees of the irreducible representations of the symmetric group  $\mathcal{S}_n$ . Given this, Corollary 8.4 is a special case of the result that the sum of the squares of the degrees of the irreducible representations of a finite group G is equal to the order |G| of G. There are many other intimate connections between the representation theory of  $\mathcal{S}_n$ , on the one hand, and the combinatorics of Young's lattice and Young tableaux, on the other. There is also an elegant combinatorial proof of Corollary 8.4, known as the *Robinson-Schensted correspondence*, with many fascinating properties and with deep connections with representation theory.

We now consider a variation of Theorem 8.3 in which we are not concerned with the type w of a Hasse walk from  $\emptyset$  to w, but only with the number of steps. For instance, there are three Hasse walks of length three from  $\emptyset$  to the partition 1, given by  $\emptyset$ , 1,  $\emptyset$ , 1;  $\emptyset$ , 1, 2, 1; and  $\emptyset$ , 1, 11, 1. Let  $\beta(\ell, \lambda)$  denote the number of Hasse walks of length  $\ell$  from  $\emptyset$  to  $\lambda$ . Note the two following easy facts:

(F1) 
$$\beta(\ell, \lambda) = 0$$
 unless  $\ell \equiv |\lambda| \pmod{2}$ .

(F2)  $\beta(\ell, \lambda)$  is the coefficient of  $\lambda$  in the expansion of  $(D + U)^{\ell}(\emptyset)$  as a linear combination of partitions.

Because of (F2) it is important to write  $(D+U)^{\ell}$  as a linear combination of terms  $U^iD^j$ , just as in the proof of Theorem 8.3 we wrote a word w in U

and D in this form. Thus define integers  $b_{ij}(\ell)$  by

$$(D+U)^{\ell} = \sum_{i,j} b_{ij}(\ell) U^i D^j. \tag{44}$$

Just as in the proof of Theorem 8.3, the numbers  $b_{ij}(\ell)$  exist and are well-defined.

**8.5 Lemma.** We have  $b_{ij}(\ell) = 0$  if  $\ell - i - j$  is odd. If  $\ell - i - j = 2m$  then

$$b_{ij}(\ell) = \frac{\ell!}{2^m i! j! m!}.$$
 (45)

**Proof.** The assertion for  $\ell - i - j$  odd is equivalent to (F1) above, so assume  $\ell - i - j$  is even. The proof is by induction on  $\ell$ . It's easy to check that (45) holds for  $\ell = 1$ . Now assume true for some fixed  $\ell \geq 1$ . Using (44) we obtain

$$\sum_{i,j} b_{ij} (\ell+1) U^{i} D^{j} = (D+U)^{\ell+1}$$

$$= (D+U) \sum_{i,j} b_{ij} (\ell) U^{i} D^{j}$$

$$= \sum_{i,j} b_{ij} (\ell) (DU^{i} D^{j} + U^{i+1} D^{j}).$$

In the proof of Theorem 8.3 we saw that  $DU^i = U^iD + iU^{i-1}$  (see equation (43)). Hence we get

$$\sum_{i,j} b_{ij}(\ell+1)U^i D^j = \sum_{i,j} b_{ij}(\ell)(U^i D^{j+1} + iU^{i-1}D^j + U^{i+1}D^j). \tag{46}$$

As mentioned after (44), the expansion of  $(D+U)^{\ell+1}$  in terms of  $U^iD^j$  is unique. Hence equating coefficients of  $U^iD^j$  on both sides of (46) yields the recurrence

$$b_{ij}(\ell+1) = b_{i,j-1}(\ell) + (i+1)b_{i+1,j}(\ell) + b_{i-1,j}(\ell).$$
(47)

It is a routine matter to check that the function  $\ell!/2^m i! j! m!$  satisfies the same recurrence (47) as  $b_{ij}(\ell)$ , with the same intial condition  $b_{00}(0) = 1$ . From this the proof follows by induction.  $\square$ 

From Lemma 8.5 it is easy to prove the following result.

**8.6 Theorem.** Let  $\ell \geq n$  and  $\lambda \vdash n$ , with  $\ell - n$  even. Then

$$\beta(\ell,\lambda) = \binom{\ell}{n} (1 \cdot 3 \cdot 5 \cdots (\ell-n-1)) f^{\lambda}.$$

**Proof.** Apply both sides of (44) to  $\emptyset$ . Since  $U^iD^j(\emptyset) = 0$  unless j = 0, we get

$$(D+U)^{\ell}(\emptyset) = \sum_{i} b_{i0}(\ell) U^{i}(\emptyset)$$
$$= \sum_{i} b_{i0}(\ell) \sum_{\lambda \vdash i} f^{\lambda} \lambda.$$

Since by Lemma 8.5 we have  $b_{i0}(\ell) = {\ell \choose i} (1 \cdot 3 \cdot 5 \cdots (\ell - i - 1))$  when  $\ell - i$  is even, the proof follows from (F2).  $\square$ 

NOTE. The proof of Theorem 8.6 only required knowing the value of  $b_{i0}(\ell)$ . However, in Lemma 8.5 we computed  $b_{ij}(\ell)$  for all j. We could have carried out the proof so as only to compute  $b_{i0}(\ell)$ , but the general value of  $b_{ij}(\ell)$  is so simple that we have included it too.

**8.7 Corollary.** The total number of Hasse walks in Y of length 2m from  $\emptyset$  to  $\emptyset$  is given by

$$\beta(2m, \emptyset) = 1 \cdot 3 \cdot 5 \cdots (2m - 1).$$

**Proof.** Simply substitute  $\lambda = \emptyset$  (so n = 0) and  $\ell = 2m$  in Theorem 8.6.  $\square$ 

The fact that we can count various kinds of Hasse walks in Y suggests that there may be some finite graphs related to Y whose eigenvalues we can also compute. This is indeed the case, and we will discuss the simplest case here. Let  $Y_{j-1,j}$  denote the restriction of Young's lattice Y to ranks j-1 and j. Identify  $Y_{j-1,j}$  with its Hasse diagram, regarded as a (bipartite)

graph. Let  $p(i) = |Y_i|$ , the number of partitions of i. (The function p(i) has been extensively studied, beginning with Euler, though we will not discuss its fascinating properties here.)

**8.8 Theorem.** The eigenvalues of  $Y_{j-1,j}$  are given as follows: 0 is an eigenvalue of multiplicity p(j) - p(j-1); and for  $1 \le s \le j$ , the numbers  $\pm \sqrt{s}$  are eigenvalues of multiplicity p(j-s) - p(j-s-1).

**Proof.** Let A denote the adjacency matrix of  $Y_{j-1,j}$ . Since  $\mathbb{R}Y_{j-1,j} = \mathbb{R}Y_{j-1} \oplus \mathbb{R}Y_j$  (vector space direct sum), any vector  $v \in \mathbb{R}Y_{j-1,j}$  can be written uniquely as  $v = v_{j-1} + v_j$ , where  $v_i \in \mathbb{R}Y_i$ . The matrix A acts on the vector space  $\mathbb{R}Y_{j-1,j}$  as follows [why?]:

$$\mathbf{A}(v) = D(v_j) + U(v_{j-1}). \tag{48}$$

Just as Theorem 4.7 followed from Lemma 4.6, we deduce from Lemma 8.2 that for any i we have that  $U_i : \mathbb{R}Y_i \to \mathbb{R}Y_{i+1}$  is one-to-one and  $D_i : \mathbb{R}Y_i \to \mathbb{R}Y_{i-1}$  is onto. It follows in particular that

$$\dim(\ker(D_i)) = \dim \mathbb{R}Y_i - \dim \mathbb{R}Y_{i-1}$$
$$= p(i) - p(i-1),$$

where ker denotes kernel.

Case 1. Let  $v \in \ker(D_j)$ , so  $v = v_j$ . Then  $\mathbf{A}v = Dv = 0$ . Thus  $\ker(D_j)$  is an eigenspace of  $\mathbf{A}$  for the eigenvalue 0, so 0 is an eigenvalue of multiplicity at least p(j) - p(j-1).

Case 2. Let  $v \in \ker(D_s)$  for some  $0 \le s \le j-1$ . Let

$$v^* = \pm \sqrt{j - s} U^{j-1-s}(v) + U^{j-s}(v).$$

Note that  $v^* \in \mathbb{R}Y_{j-1,j}$ , with  $v_{j-1}^* = \pm \sqrt{j-s}U^{j-1-s}(v)$  and  $v_j^* = U^{j-s}(v)$ . Using equation (43), we compute

$$\begin{aligned} \boldsymbol{A}(v^*) &= U(v_{j-1}^*) + D(v_j^*) \\ &= \pm \sqrt{j-s} U^{j-s}(v) + D U^{j-s}(v) \\ &= \pm \sqrt{j-s} U^{j-s}(v) + U^{j-s} D(v) + (j-s) U^{j-s-1}(v) \end{aligned}$$

$$= \pm \sqrt{j - s} U^{j-s}(v) + (j - s) U^{j-s-1}(v)$$
  
= \pm \left(\sqrt{j - s}\right) v^\*. (49)

It's easy to verify (using the fact that U is one-to-one) that if  $v(1), \ldots, v(t)$  is a basis for  $\ker(D_s)$ , then  $v(1)^*, \ldots, v(t)^*$  are linearly independent. Hence by (49) we have that  $\pm \sqrt{j-s}$  is an eigenvalue of  $\mathbf{A}$  of multiplicity at least  $t = \dim(\ker(D_s)) = p(s) - p(s-1)$ .

We have found a total of

$$p(j) - p(j-1) + 2\sum_{s=0}^{j-1} (p(s) - p(s-1)) = p(j-1) + p(j)$$

eigenvalues of A. (The factor 2 above arises from the fact that both  $+\sqrt{j-s}$  and  $-\sqrt{j-s}$  are eigenvalues.) Since the graph  $Y_{j-1,j}$  has p(j-1)+p(j) vertices, we have found all its eigenvalues.  $\square$ 

An elegant combinatorial consequence of Theorem 8.8 is the following.

**8.9 Corollary.** Fix  $j \geq 1$ . The number of ways to choose a partition  $\lambda$  of j, then delete a square from  $\lambda$  (keeping it a partition), then insert a square, then delete a square, etc., for a total of m insertions and m deletions, ending back at  $\lambda$ , is given by

$$\sum_{s=1}^{j} [p(j-s) - p(j-s-1)]s^{m}, \ m > 0.$$
 (50)

**Proof.** Exactly half the closed walks in  $Y_{j-1,j}$  of length 2m begin at an element of  $Y_j$  [why?]. Hence if  $Y_{j-1,j}$  has eigenvalues  $\theta_1, \ldots, \theta_r$ , then by Corollary 1.3 the desired number of walks is given by  $\frac{1}{2}(\theta_1^{2m} + \cdots + \theta_r^{2m})$ . Using the values of  $\theta_1, \ldots, \theta_r$  given by Theorem 8.8 yields (50).  $\square$ 

For instance, when j = 7, equation (50) becomes  $4 + 2 \cdot 2^m + 2 \cdot 3^m + 4^m + 5^m + 7^m$ . When m = 1 we get 30, the number of edges of the graph  $Y_{6,7}$  [why?].

---

## 4 The Sperner property.

In this section we consider a surprising application of certain adjacency matrices to some problems in extremal set theory. An important role will also be played by finite groups. In general, extremal set theory is concerned with finding (or estimating) the most or least number of sets satisfying given settheoretic or combinatorial conditions. For example, a typical easy problem in extremal set theory is the following: What is the most number of subsets of an *n*-element set with the property that any two of them intersect? (Can you solve this problem?) The problems to be considered here are most conveniently formulated in terms of partially ordered sets, or posets for short. Thus we begin with discussing some basic notions concerning posets.

**4.1 Definition.** A poset (short for partially ordered set) P is a finite set, also denoted P, together with a binary relation denoted  $\leq$  satisfying the following axioms:

- (P1) (reflexivity)  $x \le x$  for all  $x \in P$
- (P2) (antisymmetry) If  $x \leq y$  and  $y \leq x$ , then x = y.
- (P3) (transitivity) If  $x \leq y$  and  $y \leq z$ , then  $x \leq z$ .

One easy way to obtain a poset is the following. Let P be any collection of sets. If  $x, y \in P$ , then define  $x \leq y$  in P if  $x \subseteq y$  as sets. It is easy to see that this definition of  $\leq$  makes P into a poset. If P consists of all subsets of an n-element set S, then P is called a (finite) boolean algebra of rank n and is denoted by  $B_S$ . If  $S = \{1, 2, ..., n\}$ , then we denote  $B_S$  simply by  $B_n$ . Boolean algebras will play an important role throughout this section.

There is a simple way to represent small posets pictorially. The *Hasse diagram* of a poset P is a planar drawing, with elements of P drawn as dots. If x < y in P (i.e.,  $x \le y$  and  $x \ne y$ ), then y is drawn "above" x (i.e., with a larger vertical coordinate). An edge is drawn between x and y if y covers x, i.e., x < y and no element z is in between, i.e., no z satisfies x < z < y. By the transitivity property (P3), all the relations of a finite

poset are determined by the cover relations, so the Hasse diagram determines P. (This is not true for infinite posets; for instance, the real numbers  $\mathbb{R}$  with their usual order is a poset with no cover relations.) The Hasse diagram of the boolean algebra  $B_3$  looks like

We say that two posets P and Q are isomorphic if there is a bijection (one-to-one and onto function)  $\varphi: P \to Q$  such that  $x \leq y$  in P if and only if  $\varphi(x) \leq \varphi(y)$  in Q. Thus one can think that two posets are isomorphic if they differ only in the names of their elements. This is exactly analogous to the notion of isomorphism of groups, rings, etc. It is an instructive exercise to draw Hasse diagrams of the one poset of order (number of elements) one (up to isomorphism), the two posets of order two, the five posets of order three, and the sixteen posets of order four. More ambitious readers can try the 63 posets of order five, the 318 of order six, the 2045 of order seven, the 16999 of order eight, the 183231 of order nine, the 2567284 of order ten, the 46749427 of order eleven, the 1104891746 of order twelve, the 33823827452 of order thirteen, and the 1338193159771 of order fourteen. Beyond this the number is not currently known.

A chain C in a poset is a totally ordered subset of P, i.e., if  $x, y \in C$  then either  $x \leq y$  or  $y \leq x$  in P. A finite chain is said to have length n if it has n+1 elements. Such a chain thus has the form  $x_0 < x_1 < \cdots < x_n$ . We say that a finite poset is graded of rank n if every maximal chain has length n. (A chain is maximal if it's contained in no larger chain.) For instance, the boolean algebra  $B_n$  is graded of rank n [why?]. A chain  $y_0 < y_1 < \cdots < y_j$  is said to be saturated if each  $y_{i+1}$  covers  $y_i$ . Such a chain need not be maximal since there can be elements of P smaller than  $y_0$  or greater than  $y_j$ . If P is graded of rank n and  $x \in P$ , then we say that x has rank y, denoted y if some (or equivalently, every) saturated chain of y with top element y has length y. Thus [why?] if we let y if y if y if y if y if y if we let y if y if y if y if y if y if we let y if y if y if y if y if we let y if y if y if y if y if y if y if we let y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y if y i

disjoint union  $P = P_0 \cup P_1 \cup \cdots \cup P_n$ , and every maximal chain of P has the form  $x_0 < x_1 < \cdots < x_n$  where  $\rho(x_j) = j$ . We write  $p_j = |P_j|$ , the number of elements of P of rank j. For example, if  $P = B_n$  then  $\rho(x) = |x|$  (the cardinality of x as a set) and

$$p_j = \#\{x \subseteq \{1, 2, \dots, n\} : |x| = j\} = \binom{n}{j}.$$

(Note that we use both |S| and #x for the cardinality of the finite set S.)

We say that a graded poset P of rank n (always assumed to be finite) is rank-symmetric if  $p_i = p_{n-i}$  for  $0 \le i \le n$ , and rank-unimodal if  $p_0 \le p_1 \le \cdots \le p_j \ge p_{j+1} \ge p_{j+2} \ge \cdots \ge p_n$  for some  $0 \le j \le n$ . If P is both rank-symmetric and rank-unimodal, then we clearly have

$$p_0 \le p_1 \le \cdots \le p_m \ge p_{m+1} \ge \cdots \ge p_n$$
, if  $n = 2m$ 

$$p_0 \le p_1 \le \dots \le p_m = p_{m+1} \ge p_{m+2} \ge \dots \ge p_n$$
, if  $n = 2m + 1$ .

We also say that the sequence  $p_0, p_1, \ldots, p_n$  itself or the polynomial  $F(q) = p_0 + p_1 q + \cdots + p_n q^n$  is symmetric or unimodal, as the case may be. For instance,  $B_n$  is rank-symmetric and rank-unimodal, since it is well-known (and easy to prove) that the sequence  $\binom{n}{0}, \binom{n}{1}, \ldots, \binom{n}{n}$  (the nth row of Pascal's triangle) is symmetric and unimodal. Thus the polynomial  $(1+q)^n$  is symmetric and unimodal.

A few more definitions, and then finally some results! An antichain in a poset P is a subset A of P for which no two elements are comparable, i.e., we can never have  $x, y \in A$  and x < y. For instance, in a graded poset P the "levels"  $P_j$  are antichains [why?]. We will be concerned with the problem of finding the largest antichain in a poset. Consider for instance the boolean algebra  $B_n$ . The problem of finding the largest antichain in  $B_n$  is clearly equivalent to the following problem in extremal set theory: Find the largest collection of subsets of an n-element set such that no element of the collection contains another. A good guess would be to take all the subsets of cardinality  $\lfloor n/2 \rfloor$  (where  $\lfloor x \rfloor$  denotes the greatest integer  $\leq x$ ), giving a total of  $\binom{n}{\lfloor n/2 \rfloor}$  sets in all. But how can we actually prove there is no larger collection? Such a proof was first given by Emmanuel Sperner in 1927 and is known as Sperner's theorem. We will give two proofs of Sperner's theorem

in this section; one proof uses linear algebra and will be applied to certain other situations, while the other proof is an elegant combinatorial argument due to David Lubell in 1966, which we present for its "cultural value." Our extension of Sperner's theorem to certain other situations will involve the following crucial definition.

**4.2 Definition.** Let P be a graded poset of rank n. We say that P has the *Sperner property* or is a *Sperner poset* if

$$\max\{|A|: A \text{ is an antichain of } P\} = \max\{|P_i|: 0 \le i \le n\}.$$

In other words, no antichain is larger than the largest level  $P_i$ .

Thus Sperner's theorem is equivalent to saying that  $B_n$  has the Sperner property. Note that if P has the Sperner property there may still be antichains of maximum cardinality other than the biggest  $P_i$ ; there just can't be any bigger antichains.

**4.3 Example.** A simple example of a graded poset that fails to satisfy the Sperner property is the following:

We now will discuss a simple combinatorial condition which guarantees that certain graded posets P are Sperner. We define an order-matching from  $P_i$  to  $P_{i+1}$  to be a one-to-one function  $\mu: P_i \to P_{i+1}$  satisfying  $x < \mu(x)$  for all  $x \in P_i$ . Clearly if such an order-matching exists then  $p_i \leq p_{i+1}$  (since  $\mu$  is one-to-one). Easy examples show that the converse is false, i.e., if  $p_i \leq p_{i+1}$  then there need not exist an order-matching from  $P_i$  to  $P_{i+1}$ . We similarly define an order-matching from  $P_i$  to  $P_{i-1}$  to be a one-to-one function  $\mu: P_i \to P_{i-1}$  satisfying  $\mu(x) < x$  for all  $x \in P_i$ .

**4.4 Proposition.** Let P be a graded poset of rank n. Suppose there exists an integer  $0 \le j \le n$  and order-matchings

$$P_0 \to P_1 \to P_2 \to \cdots \to P_j \leftarrow P_{j+1} \leftarrow P_{j+2} \leftarrow \cdots \leftarrow P_n.$$
 (17)

Then P is rank-unimodal and Sperner.

**Proof.** Since order-matchings are one-to-one it is clear that

$$p_0 \le p_1 \le \cdots \le p_j \ge p_{j+1} \ge p_{j+2} \ge \cdots \ge p_n$$
.

Hence P is rank-unimodal.

Define a graph G as follows. The vertices of G are the elements of P. Two vertices x, y are connected by an edge if one of the order-matchings  $\mu$  in the statement of the proposition satisfies  $\mu(x) = y$ . (Thus G is a subgraph of the Hasse diagram of P.) Drawing a picture will convince you that G consists of a disjoint union of paths, including single-vertex paths not involved in any of the order-matchings. The vertices of each of these paths form a chain in P. Thus we have partitioned the elements of P into disjoint chains. Since P is rank-unimodal with biggest level  $P_j$ , all of these chains must pass through  $P_j$  [why?]. Thus the number of chains is exactly  $p_j$ . Any antichain A can intersect each of these chains at most once, so the cardinality |A| of A cannot exceed the number of chains, i.e.,  $|A| \leq p_j$ . Hence by definition P is Sperner.

It is now finally time to bring some linear algebra into the picture. For any (finite) set S, we let  $\mathbb{R}S$  denote the real vector space consisting of all formal linear combinations (with real coefficients) of elements of S. Thus S is a basis for  $\mathbb{R}S$ , and in fact we could have simply defined  $\mathbb{R}S$  to be the real vector space with basis S. The next lemma relates the combinatorics we have just discussed to linear algebra and will allow us to prove that certain posets are Sperner by the use of linear algebra (combined with some finite group theory).

**4.5 Lemma.** Suppose there exists a linear transformation  $U : \mathbb{R}P_i \to \mathbb{R}P_{i+1}$  (U stands for "up") satisfying:

- U is one-to-one.
- For all  $x \in P_i$ , U(x) is a linear combination of elements  $y \in P_{i+1}$  satisfying x < y. (We then call U an order-raising operator.)

Then there exists an order-matching  $\mu: P_i \to P_{i+1}$ .

Similarly, suppose there exists a linear transformation  $U: \mathbb{R}P_i \to \mathbb{R}P_{i+1}$  satisfying:

- U is onto.
- U is an order-raising operator.

Then there exists an order-matching  $\mu: P_{i+1} \to P_i$ .

**Proof.** Suppose  $U: \mathbb{R}P_i \to \mathbb{R}P_{i+1}$  is a one-to-one order-raising operator. Let [U] denote the matrix of U with respect to the bases  $P_i$  of  $\mathbb{R}P_i$  and  $P_{i+1}$  of  $\mathbb{R}P_{i+1}$ . Thus the columns of [U] are indexed by the elements  $x_1, \ldots, x_{p_i}$  of  $P_i$  (in some order) and the rows by the elements  $y_1, \ldots, y_{p_{i+1}}$  of  $P_{i+1}$ . Since U is one-to-one, the rank of [U] is equal to  $p_i$  (the number of columns). Since the column rank of a matrix equals its row rank, [U] must have  $p_i$  linearly independent rows. Say we have labelled the elements of  $P_{i+1}$  so that the first  $p_i$  rows of [U] are linearly independent.

Let  $A = (a_{ij})$  be the  $p_i \times p_i$  matrix whose rows are the first  $p_i$  rows of [U]. (Thus A is a square submatrix of [U].) Since the rows of A are linearly independent, we have

$$\det(A) = \sum \pm a_{\pi(1),1} \cdots a_{\pi(p_i),p_i} \neq 0,$$

where the sum is over all permutations  $\pi$  of  $1, \ldots, p_i$ . Thus some term  $\pm a_{\pi(1),1} \cdots a_{\pi(p_i),p_i}$  of the above sum in nonzero. Since U is order-raising, this means that [why?]  $x_k < y_{\pi(k)}$  for  $1 \le k \le p_i$ . Hence the map  $\mu: P_i \to P_{i+1}$  defined by  $\mu(x_k) = y_{\pi(k)}$  is an order-matching, as desired.

The case when U is onto rather than one-to-one is proved by a completely analogous argument.  $\square$ 

We now want to apply Proposition 4.4 and Lemma 4.5 to the boolean algebra  $B_n$ . For each  $0 \le i < n$ , we need to define a linear transformation  $U_i : \mathbb{R}(B_n)_i \to \mathbb{R}(B_n)_{i+1}$ , and then prove it has the desired properties. We simply define  $U_i$  to be the simplest possible order-raising operator, namely,

for  $x \in (B_n)_i$ , let

$$U_i(x) = \sum_{\substack{y \in (B_n)_{i+1} \\ y > x}} y. \tag{18}$$

Note that since  $(B_n)_i$  is a basis for  $\mathbb{R}(B_n)_i$ , equation (18) does indeed define a unique linear transformation  $U_i : \mathbb{R}(B_n)_i \to \mathbb{R}(B_n)_{i+1}$ . By definition  $U_i$  is order-raising; we want to show that  $U_i$  is one-to-one for i < n/2 and onto for  $i \ge n/2$ . There are several ways to show this using only elementary linear algebra; we will give what is perhaps the simplest proof, though it is quite tricky. The idea is to introduce "dual" operators  $D_i : \mathbb{R}(B_n)_i \to (B_n)_{i-1}$  to the  $U_i$ 's (D stands for "down"), defined by

$$D_i(y) = \sum_{\substack{x \in (B_n)_{i-1} \\ x < y}} x,$$
(19)

for all  $y \in (B_n)_i$ . Let  $[U_i]$  denote the matrix of  $U_i$  with respect to the bases  $(B_n)_i$  and  $(B_n)_{i+1}$ , and similarly let  $[D_i]$  denote the matrix of  $D_i$  with respect to the bases  $(B_n)_i$  and  $(B_n)_{i-1}$ . A key observation which we will use later is that

$$[D_{i+1}] = [U_i]^t, (20)$$

i.e., the matrix  $[D_{i+1}]$  is the transpose of the matrix  $[U_i]$  [why?]. Now let  $I_i : \mathbb{R}(B_n)_i \to \mathbb{R}(B_n)_i$  denote the identity transformation on  $\mathbb{R}(B_n)_i$ , i.e.,  $I_i(u) = u$  for all  $u \in \mathbb{R}(B_n)_i$ . The next lemma states (in linear algebraic terms) the fundamental combinatorial property of  $B_n$  which we need. For this lemma set  $U_n = 0$  and  $D_0 = 0$  (the 0 linear transformation between the appropriate vector spaces).

## **4.6 Lemma.** Let $0 \le i \le n$ . Then

$$D_{i+1}U_i - U_{i-1}D_i = (n-2i)I_i. (21)$$

(Linear transformations are multiplied right-to-left, so AB(u) = A(B(u)).)

**Proof.** Let  $x \in (B_n)_i$ . We need to show that if we apply the left-hand side of (21) to x, then we obtain (n-2i)x. We have

$$D_{i+1}U_i(x) = D_{i+1} \left( \sum_{\substack{|y|=i+1\\x \subset y}} y \right)$$

$$= \sum_{\substack{|y|=i+1\\x \in y}} \sum_{\substack{|z|=i\\z \in y}} z.$$

If  $x, z \in (B_n)_i$  satisfy  $|x \cap z| < i - 1$ , then there is no  $y \in (B_n)_{i+1}$  such that  $x \subset y$  and  $z \subset y$ . Hence the coefficient of z in  $D_{i+1}U_i(x)$  when it is expanded in terms of the basis  $(B_n)_i$  is 0. If  $|x \cap z| = i - 1$ , then there is one such y, namely,  $y = x \cup z$ . Finally if x = z then y can be any element of  $(B_n)_{i+1}$  containing x, and there are n - i such y in all. It follows that

$$D_{i+1}U_i(x) = (n-i)x + \sum_{\substack{|z|=i\\|x\cap z|=i-1}} z.$$
 (22)

By exactly analogous reasoning (which the reader should check), we have for  $x \in (B_n)_i$  that

$$U_{i-1}D_i(x) = ix + \sum_{\substack{|z|=i\\|x\cap z|=i-1}} z.$$
 (23)

Subtracting (23) from (22) yields  $(D_{i+1}U_i-U_{i-1}D_i)(x)=(n-2i)x$ , as desired.

**4.7 Theorem.** The operator  $U_i$  defined above is one-to-one if i < n/2 and is onto if  $i \ge n/2$ .

**Proof.** Recall that  $[D_i] = [U_{i-1}]^t$ . From linear algebra we know that a (rectangular) matrix times its transpose is *positive semidefinite* (or just *semidefinite* for short) and hence has nonnegative (real) eigenvalues. By Lemma 4.6 we have

$$D_{i+1}U_i = U_{i-1}D_i + (n-2i)I_i.$$

Thus the eigenvalues of  $D_{i+1}U_i$  are obtained from the eigenvalues of  $U_{i-1}D_i$  by adding n-2i. Since we are assuming that n-2i>0, it follows that the eigenvalues of  $D_{i+1}U_i$  are strictly positive. Hence  $D_{i+1}U_i$  is invertible (since it has no 0 eigenvalues). But this implies that  $U_i$  is one-to-one [why?], as desired.

The case  $i \ge n/2$  is done by a "dual" argument (or in fact can be deduced directly from the i < n/2 case by using the fact that the poset  $B_n$  is "self-dual," though we will not go into this). Namely, from the fact that

$$U_i D_{i+1} = D_{i+2} U_{i+1} + (2i+2-n)I_{i+1}$$

we get that  $U_iD_{i+1}$  is invertible, so now  $U_i$  is onto, completing the proof.  $\square$ 

Combining Proposition 4.4, Lemma 4.5, and Theorem 4.7, we obtain the famous theorem of Sperner.

## **4.8 Corollary.** The boolean algebra $B_n$ has the Sperner property.

It is natural to ask whether there is a less indirect proof of Corollary 4.8. In fact, several nice proofs are known; we give one due to David Lubell, mentioned before Definition 4.2.

**Lubell's proof of Sperner's theorem.** First we count the total number of maximal chains  $\emptyset = x_0 < x_1 < \cdots < x_n = \{1, \dots, n\}$  in  $B_n$ . There are n choices for  $x_1$ , then n-1 choices for  $x_2$ , etc., so there are n! maximal chains in all. Next we count the number of maximal chains  $x_0 < x_1 < \cdots < x_i = x < \cdots < x_n$  which contain a given element x of rank i. There are i choices for  $x_1$ , then i-1 choices for  $x_2$ , up to one choice for  $x_i$ . Similarly there are n-i choices for  $x_{i+1}$ , then n-2 choices for  $x_{i+2}$ , etc., up to one choice for  $x_n$ . Hence the number of maximal chains containing x is i!(n-i)!.

Now let A be an antichain. If  $x \in A$ , then let  $C_x$  be the set of maximal chains of  $B_n$  which contain x. Since A is an antichain, the sets  $C_x$ ,  $x \in A$  are pairwise disjoint. Hence

$$|\bigcup_{x \in A} C_x| = \sum_{x \in A} |C_x|$$
$$= \sum_{x \in A} (\rho(x))!(n - \rho(x))!$$

Since the total number of maximal chains in the  $C_x$ 's cannot exceed the total number n! of maximal chains in  $B_n$ , we have

$$\sum_{x \in A} (\rho(x))!(n - \rho(x))! \le n!$$

Divide both sides by n! to obtain

$$\sum_{x \in A} \frac{1}{\binom{n}{\rho(x)}} \le 1.$$

Since  $\binom{n}{i}$  is maximized when  $i = \lfloor n/2 \rfloor$ , we have

$$\frac{1}{\binom{n}{\lfloor n/2\rfloor}} \le \frac{1}{\binom{n}{\rho(x)}},$$

for all  $x \in A$  (or all  $x \in B_n$ ). Thus

$$\sum_{x \in A} \frac{1}{\binom{n}{\lfloor n/2 \rfloor}} \le 1,$$

or equivalently,

$$|A| \le \binom{n}{\lfloor n/2 \rfloor}.$$

Since  $\binom{n}{\lfloor n/2 \rfloor}$  is the size of the largest level of  $B_n$ , it follows that  $B_n$  is Sperner.

In view of the above elegant proof of Lubell, the reader may be wondering what was the point of giving a rather complicated and indirect proof using linear algebra. Admittedly, if all we could obtain from the linear algebra machinery we have developed was just another proof of Sperner's theorem, then it would have been hardly worth the effort. But in the next section we will show how Theorem 4.7, when combined with a little finite group theory, can be used to obtain many interesting combinatorial results for which simple, direct proofs are not known.

---

## 5 Group actions on boolean algebras.

Let us begin by reviewing some facts from group theory. Suppose that X is an n-element set and that G is a group. We say that G acts on the set X if for every element  $\pi$  of G we associate a permutation (also denoted  $\pi$ ) of X, such that for all  $x \in X$  and  $\pi, \sigma \in G$  we have

$$\pi(\sigma(x)) = (\pi\sigma)(x).$$

Thus [why?] an action of G on X is the same as a homomorphism  $\varphi: G \to \mathfrak{S}_X$ , where  $\mathfrak{S}_X$  denotes the symmetric group of all permutations of X. We sometimes write  $\pi \cdot x$  instead of  $\pi(x)$ .

- **5.1 Example.** (a) Let the real number  $\alpha$  act on the xy-plane by rotation counterclockwise around the origin by an angle of  $\alpha$  radians. It is easy to check that this defines an action of the group  $\mathbb{R}$  of real numbers (under addition) on the xy-plane.
- (b) Now let  $\alpha \in \mathbb{R}$  act by translation by a distance  $\alpha$  to the right (i.e., adding  $(\alpha, 0)$ ). This yields a completely different action of  $\mathbb{R}$  on the xy-plane.
- (c) Let  $X = \{a, b, c, d\}$  and  $G = \mathbb{Z}_2 \times \mathbb{Z}_2 = \{(0, 0), (0, 1), (1, 0), (1, 1)\}$ . Let G act as follows:

$$(0,1)\cdot a = b, \ \ (0,1)\cdot b = a, \ \ (0,1)\cdot c = c, \ \ (0,1)\cdot d = d$$

$$(1,0)\cdot a = a, \ \ (1,0)\cdot b = b, \ \ (1,0)\cdot c = d, \ \ (1,0)\cdot d = c.$$

The reader should check that this does indeed define an action. In particular, since (1,0) and (0,1) generate G, we don't need to define the action of (0,0) and (1,1) — they are uniquely determined.

(d) Let X and G be as in (c), but now define the action by

$$(0,1) \cdot a = b$$
,  $(0,1) \cdot b = a$ ,  $(0,1) \cdot c = d$ ,  $(0,1) \cdot d = c$ 

$$(1,0)\cdot a = c, \ \ (1,0)\cdot b = d, \ \ (1,0)\cdot c = a, \ \ (1,0)\cdot d = b.$$

Again one can check that we have an action of  $\mathbb{Z}_2 \times \mathbb{Z}_2$  on  $\{a, b, c, d\}$ .

Recall what is meant by an *orbit* of the action of a group G on a set X. Namely, we say that two elements x, y of X are G-equivalent if  $\pi(x) = y$  for some  $\pi \in G$ . The relation of G-equivalence is an equivalence relation, and the equivalence classes are called orbits. Thus x and y are in the same orbit if  $\pi(x) = y$  for some  $\pi \in G$ . The orbits form a partition of X, i.e, they are pairwise-disjoint, nonempty subsets of X whose union is X. The orbit containing x is denoted Gx; this is sensible notation since Gx consists of all elements  $\pi(x)$  where  $\pi \in G$ . Thus Gx = Gy if and only if x and y are G-equivalent (i.e., in the same G-orbit). The set of all G-orbits is denoted X/G.

- **5.2 Example.** (a) In Example 5.1(a), the orbits are circles with center (0,0) (including the degenerate circle whose only point is (0,0)).
- (b) In Example 5.1(b), the orbits are horizontal lines. Note that although in (a) and (b) the same group G acts on the same set X, the orbits are different.
  - (c) In Example 5.1(c), the orbits are  $\{a, b\}$  and  $\{c, d\}$ .
- (d) In Example 5.1(d), there is only one orbit  $\{a, b, c, d\}$ . Again we have a situation in which a group G acts on a set X in two different ways, with different orbits.

We wish to consider the situation where  $X = B_n$ , the boolean algebra of rank n (so  $|B_n| = 2^n$ ). We begin by defining an *automorphism* of a poset P to be an isomorphism  $\varphi : P \to P$ . (This definition is exactly analogous to the definition of an automorphism of a group, ring, etc.) The set of all automorphisms of P forms a group, denoted Aut(P) and called the automorphism group of P, under the operation of composition of functions (just as is the case for groups, rings, etc.)

Now consider the case  $P = B_n$ . Any permutation  $\pi$  of  $\{1, \ldots, n\}$  acts on  $B_n$  as follows: If  $x = \{i_1, i_2, \ldots, i_k\} \in B_n$ , then

$$\pi(x) = \{\pi(i_1), \pi(i_2), \dots, \pi(i_k)\}.$$
(24)

This action of  $\pi$  on  $B_n$  is an automorphism [why?]; in particular, if |x| = i, then also  $|\pi(x)| = i$ . Equation (24) defines an action of the symmetric group

 $\mathfrak{S}_n$  of all permutations of  $\{1,\ldots,n\}$  on  $B_n$  [why?]. (In fact, it is not hard to show that *every* automorphism of  $B_n$  is of the form (24) for  $\pi \in \mathfrak{S}_n$ .) In particular, any subgroup G of  $\mathfrak{S}_n$  acts on  $B_n$  via (24) (where we restrict  $\pi$  to belong to G). In what follows this action is always meant.

**5.3 Example.** Let n = 3, and let G be the subgroup of  $\mathfrak{S}_3$  with elements e and (1,2). Here e denotes the identity permutation, and (using disjoint cycle notation) (1,2) denotes the permutation which interchanges 1 and 2, and fixes 3. There are six orbits of G (acting on  $B_3$ ). Writing e.g. 13 as short for  $\{1,3\}$ , the six orbits are  $\{\emptyset\}$ ,  $\{1,2\}$ ,  $\{3\}$ ,  $\{12\}$ ,  $\{13,23\}$ , and  $\{123\}$ .

We now define the class of posets which will be of interest to us here. Later we will give some special cases of particular interest.

- **5.4 Definition.** Let G be a subgroup of  $\mathfrak{S}_n$ . Define the *quotient poset*  $B_n/G$  as follows: The elements of  $B_n/G$  are the orbits of G. If  $\mathcal{O}$  and  $\mathcal{O}'$  are two orbits, then define  $\mathcal{O} \leq \mathcal{O}'$  in  $B_n/G$  if there exist  $x \in \mathcal{O}$  and  $y \in \mathcal{O}'$  such that  $x \leq y$  in  $B_n$ . (It's easy to check that this relation  $\leq$  is indeed a partial order.)
- **5.5 Example.** (a) Let n = 3 and G be the group of order two generated by the cycle (1, 2), as in Example 5.2. Then the Hasse diagram of  $B_3/G$  is shown below, where each element (orbit) is labeled by one of its elements.

(b) Let n=5 and G be the group of order five generated by the cycle (1,2,3,4,5). Then  $B_5/G$  has Hasse diagram

One simple property of a quotient poset  $B_n/G$  is the following.

**5.6 Proposition.** The quotient poset  $B_n/G$  defined above is graded of rank n and rank-symmetric.

**Proof.** We leave as an exercise the easy proof that  $B_n/G$  is graded of rank n, and that the rank of an element  $\mathcal{O}$  of  $B_n/G$  is just the rank in  $B_n$  of any of the elements x of  $\mathcal{O}$ . Thus the number of elements  $p_i(B_n/G)$  of rank i is equal to the number of orbits  $\mathcal{O} \in (B_n)_i/G$ . If  $x \in B_n$ , then let  $\bar{x}$  denote the set-theoretic complement of x, i.e.,

$$\bar{x} = \{1, \dots, n\} - x = \{1 \le i \le n : i \not\in x\}.$$

Then  $\{x_1, \ldots, x_j\}$  is an orbit of *i*-element subsets of  $\{1, \ldots, n\}$  if and only if  $\{\bar{x}_1, \ldots, \bar{x}_j\}$  is an orbit of (n-i)-element subsets [why?]. Hence  $|(B_n)_i/G| = |(B_n)_{n-i}/G|$ , so  $B_n/G$  is rank-symmetric.  $\square$ 

Let  $\pi \in \mathfrak{S}_n$ . We associate with  $\pi$  a linear transformation (still denoted  $\pi$ )  $\pi : \mathbb{R}(B_n)_i \to \mathbb{R}(B_n)_i$  by the rule

$$\pi\left(\sum_{x\in(B_n)_i} c_x x\right) = \sum_{x\in(B_n)_i} c_x \pi(x),$$

where each  $c_x$  is a real number. (This defines an action of  $\mathfrak{S}_n$ , or of any subgroup G of  $\mathfrak{S}_n$ , on the vector space  $\mathbb{R}(B_n)_i$ .) The matrix of  $\pi$  with

respect to the basis  $(B_n)_i$  is just a permutation matrix, i.e., a matrix with one 1 in every row and column, and 0's elsewhere. We will be interested in elements of  $\mathbb{R}(B_n)_i$  which are fixed by every element of a subgroup G of  $\mathfrak{S}_n$ . The set of all such elements is denoted  $\mathbb{R}(B_n)_i^G$ , so

$$\mathbb{R}(B_n)_i^G = \{ v \in \mathbb{R}(B_n)_i : \pi(v) = v \text{ for all } \pi \in G \}.$$

**5.7 Lemma.** A basis for  $\mathbb{R}(B_n)_i^G$  consists of the elements

$$v_{\mathcal{O}} := \sum_{x \in \mathcal{O}} x,$$

where  $\mathcal{O} \in (B_n)_i/G$ , the set of G-orbits for the action of G on  $(B_n)_i$ .

**Proof.** First note that if  $\mathcal{O}$  is an orbit and  $x \in \mathcal{O}$ , then by definition of orbit we have  $\pi(x) \in \mathcal{O}$  for all  $\pi \in G$ . Since  $\pi$  permutes the elements of  $(B_n)_i$ , it follows that  $\pi$  permutes the elements of  $\mathcal{O}$ . Thus  $\pi(v_{\mathcal{O}}) = v_{\mathcal{O}}$ , so  $v_{\mathcal{O}} \in \mathbb{R}(B_n)_i^G$ . It is clear that the  $v_{\mathcal{O}}$ 's are linearly independent since any  $x \in (B_n)_i$  appears with nonzero coefficient in exactly one  $v_{\mathcal{O}}$ .

It remains to show that the  $v_{\mathcal{O}}$ 's span  $\mathbb{R}(B_n)_i^G$ , i.e., any  $v = \sum_{x \in (B_n)_i} c_x x \in \mathbb{R}(B_n)_i^G$  can be written as a linear combination of  $v_{\mathcal{O}}$ 's. Now a vector  $v \in \mathbb{R}(B_n)_i$  will belong to  $\mathbb{R}(B_n)_i^G$  if and only if its coefficients are constant on G-orbits and hence if and only if it is a linear combination of  $v_{\mathcal{O}}$ 's for the various G-orbits  $\mathcal{O}$ .

Now let us consider the effect of applying the order-raising operator  $U_i$  to an element v of  $\mathbb{R}(B_n)_i^G$ .

**5.8 Lemma.** If 
$$v \in \mathbb{R}(B_n)_i^G$$
, then  $U_i(v) \in \mathbb{R}(B_n)_{i+1}^G$ .

**Proof.** Note that since  $\pi \in G$  is an automorphism of  $B_n$ , we have x < y in  $B_n$  if and only if  $\pi(x) < \pi(y)$  in  $B_n$ . It follows [why?] that if  $x \in (B_n)_i$  then

$$U_i(\pi(x)) = \pi(U_i(x)).$$

Since  $U_i$  and  $\pi$  are linear transformations, it follows by linearity that  $U_i\pi(u) = \pi U_i(u)$  for all  $u \in \mathbb{R}(B_n)_i$ . (In other words,  $U_i\pi = \pi U_i$ .) Then

$$\pi(U_i(v)) = U_i(\pi(v))$$

$$= U_i(v),$$

so  $U_i(v) \in \mathbb{R}(B_n)_{i+1}^G$ , as desired.  $\square$ 

We come to the main result of this section, and indeed our main result on the Sperner property.

**5.9 Theorem.** Let G be a subgroup of  $\mathfrak{S}_n$ . Then the quotient poset  $B_n/G$  is graded of rank n, rank-symmetric, rank-unimodal, and Sperner.

**Proof.** Let  $P = B_n/G$ . We have already seen in Proposition 5.6 that P is graded of rank n and rank-symmetric. We want to define order-raising operators  $\hat{U}_i : \mathbb{R}P_i \to \mathbb{R}P_{i+1}$  and order-lowering operators  $\hat{D}_i : \mathbb{R}P_i \to \mathbb{R}P_{i-1}$ . Let us first consider just  $\hat{U}_i$ . The idea is to identify the basis element  $v_{\mathcal{O}}$  of  $\mathbb{R}B_n^G$  with the basis element  $\mathcal{O}$  of  $\mathbb{R}P$ , and to let  $\hat{U}_i : \mathbb{R}P_i \to \mathbb{R}P_{i+1}$  correspond to the usual order-raising operator  $U_i : \mathbb{R}(B_n)_i \to \mathbb{R}(B_n)_{i+1}$ . More precisely, suppose that the order-raising operator  $U_i$  for  $B_n$  given by (18) satisfies

$$U_i(v_{\mathcal{O}}) = \sum_{\mathcal{O}' \in (B_n)_{i+1}/G} c_{\mathcal{O},\mathcal{O}'} v_{\mathcal{O}'}, \tag{25}$$

where  $\mathcal{O} \in (B_n)_i/G$ . (Note that by Lemma 5.8,  $U_i(v_{\mathcal{O}})$  does indeed have the form given by (25).) Then define the linear operator  $\hat{U}_i : \mathbb{R}((B_n)_i/G) \to \mathbb{R}((B_n)_i/G)$  by

$$\hat{U}_i(\mathcal{O}) = \sum_{\mathcal{O}' \in (B_n)_{i+1}/G} c_{\mathcal{O},\mathcal{O}'} \mathcal{O}'.$$

We claim that  $\hat{U}_i$  is order-raising. We need to show that if  $c_{\mathcal{O},\mathcal{O}'} \neq 0$ , then  $\mathcal{O}' > \mathcal{O}$  in  $B_n/G$ . Since  $v_{\mathcal{O}'} = \sum_{x' \in \mathcal{O}'} x'$ , the only way  $c_{\mathcal{O},\mathcal{O}'} \neq 0$  in (25) is for some  $x' \in \mathcal{O}'$  to satisfy x' > x for some  $x \in \mathcal{O}$ . But this is just what it means for  $\mathcal{O}' > \mathcal{O}$ , so  $\hat{U}_i$  is order-raising.

Now comes the heart of the argument. We want to show that  $\hat{U}_i$  is one-to-one for i < n/2. Now by Theorem 4.7,  $U_i$  is one-to-one for i < n/2. Thus the restriction of  $U_i$  to the subspace  $\mathbb{R}(B_n)_i^G$  is one-to-one. (The restriction of a one-to-one function is always one-to-one.) But  $U_i$  and  $\hat{U}_i$  are exactly the same transformation, except for the names of the basis elements on which they act. Thus  $\hat{U}_i$  is also one-to-one for i < n/2.

An exactly analogous argument can be applied to  $D_i$  instead of  $U_i$ . We obtain one-to-one order-lowering operators  $\hat{D}_i : \mathbb{R}(B_n)_i^G \to \mathbb{R}(B_n)_{i-1}^G$  for i > n/2. It follows from Proposition 4.4, Lemma 4.5, and (20) that  $B_n/G$  is rank-unimodal and Sperner, completing the proof.  $\square$ 

We will consider two interesting applications of Theorem 5.9. For our first application, we let  $n = \binom{m}{2}$  for some  $m \geq 1$ , and let  $M = \{1, \ldots, m\}$ . Let  $X = \binom{M}{2}$ , the set of all two-element subsets of M. Think of the elements of X as (possible) edges of a graph with vertex set M. If  $B_X$  is the boolean algebra of all subsets of X (so  $B_X$  and  $B_n$  are isomorphic), then an element x of  $B_X$  is a collection of edges on the vertex set M, in other words, just a simple graph on M. Define a subgroup G of  $\mathfrak{S}_X$  as follows: Informally, G consists of all permutations of the edges  $\binom{M}{2}$  that are induced from permutations of the vertices M. More precisely, if  $\pi \in \mathfrak{S}_m$ , then define  $\hat{\pi} \in \mathfrak{S}_X$  by  $\hat{\pi}(\{i,j\}) = \{\pi(i), \pi(j)\}$ . Thus G is isomorphic to  $\mathfrak{S}_m$ .

When are two graphs  $x, y \in B_X$  in the same orbit of the action of G on  $B_X$ ? Since the elements of G just permute vertices, we see that x and y are in the same orbit if we can obtain x from y by permuting vertices. This is just what it means for two simple graphs x and y to be isomorphic — they are the same graph except for the names of the vertices (thinking of edges as pairs of vertices). Thus the elements of  $B_X/G$  are isomorphism classes of simple graphs on the vertex set M. In particular,  $\#(B_X/G)$  is the number of nonisomorphic m-vertex simple graphs, and  $\#((B_X/G)_i)$  is the number of nonisomorphic such graphs with i edges. We have  $x \leq y$  in  $B_X/G$  if there is some way of labelling the vertices of x and y so that every edge of x is an edge of y. Equivalently, some spanning subgraph of y (i.e., a subgraph of y with all the vertices of y) is isomorphic to x. Hence by Theorem 5.9 there follows the following result, which is by no means obvious and has no known non-algebraic proof.

- **5.10 Theorem.** (a) Fix  $m \ge 1$ . Let  $p_i$  be the number of nonisomorphic simple graphs with m vertices and i edges. Then the sequence  $p_0, p_1, \ldots, p_{\binom{m}{2}}$  is symmetric and unimodal.
- (b) Let T be a collection of nonisomorphic simple graphs with m vertices such that no element of T is isomorphic to a subset of another element of

T. Then |T| is maximized by taking T to consist of all nonisomorphic simple graphs with  $\lfloor \frac{1}{2} {m \choose 2} \rfloor$  edges.

Our second example of the use of Theorem 5.9 is somewhat more subtle and will be the topic of the next section.

---

## Circulant Hadamard Matrices

R. Stanley

An  $n \times n$  matrix H is a *Hadamard matrix* if its entries are  $\pm 1$  and its rows are orthogonal. Equivalently, its entries are  $\pm 1$  and  $HH^t = nI$ . In particular,

$$\det H = \pm n^{n/2}. (1)$$

It is easy to see that if H is an  $n \times n$  Hadamard matrix then n = 1, n = 2, or n = 4m for some integer m. It is conjectured that the converse is true, i.e., for every such n there exists an  $n \times n$  Hadamard matrix.

An  $n \times n$  matrix  $A = (b_{ij})$  is a *circulant* if it has the form  $b_{ij} = a_{i-j}$  for some  $a_0, a_1, \ldots, a_{n-1}$ , where the subscript i - j is taken modulo n. For instance,

$$A = \left[ \begin{array}{cccc} a & b & c & d \\ d & a & b & c \\ c & d & a & b \\ b & c & d & a \end{array} \right]$$

is a circulant. Let  $A = (a_{i-j})$  be an  $n \times n$  circulant, and let  $\zeta = e^{2\pi i/n}$ , a primitive nth root of unity. It is straightforward to compute that for  $0 \leq j < n$  the column vector  $[1, \zeta^j, \zeta^{2j}, \ldots, \zeta^{(n-1)j}]^t$  is an eigenvector of A with eigenvalue  $a_0 + \zeta^j a_1 + \zeta^{2j} a_2 + \cdots + \zeta^{(n-1)j} a_{n-1}$ . Hence

$$\det(A) = \prod_{j=0}^{n-1} (a_0 + \zeta^j a_1 + \zeta^{2j} a_2 + \dots + \zeta^{(n-1)j} a_{n-1}).$$
 (2)

NOTE. The determinant of a circulant matrix is an example of a group determinant, where the group is the cyclic group of order n. In 1880 Dedekind suggested generalizing the case of circulants (and more generally group determinants for abelian groups) to arbitrary groups. It was this suggestion that led Frobenius to the creation group of representation theory. See [1] and the references therein.

Note that the matrix

$$\begin{bmatrix}
-1 & 1 & 1 & 1 \\
1 & -1 & 1 & 1 \\
1 & 1 & -1 & 1 \\
1 & 1 & 1 & -1
\end{bmatrix}$$

is both a Hadamard matrix and a circulant.

**Conjecture** (source?). Let H be an  $n \times n$  circulant Hadamard matrix. Then n = 1 or n = 4.

The main work on this conjecture is due to Richard Turyn [2]. He showed that there does not exist a circulant Hadamard matrix of order 8m, and he also excluded certain other orders of the form 4(2m+1). Turyn's proofs use the machinery of algebraic number theory. Here we will give a proof for the special case  $n=2^k$ ,  $k \geq 3$ , where the algebraic number theory can be "dumbed down" to elementary commutative algebra and field theory. It would be interesting to find similar proofs for other values of n.

**Theorem 1.** There does not exist a circulant Hadamard matrix H of order  $2^k$ , k > 3.

From now on we assume  $n=2^k$  and  $\zeta=e^{2\pi i/2^k}$ . Clearly  $\zeta$  is a zero of the polynomial  $p_k(x)=x^{2^{k-1}}+1$ . We will be working in the ring  $\mathbb{Z}[\zeta]$ , the smallest subring of  $\mathbb{C}$  containing  $\mathbb{Q}$  and  $\zeta$ . Write  $\mathbb{Q}(\zeta)$  for the quotient field of  $\mathbb{Z}[\zeta]$ , i.e., the field obtained by adjoining  $\zeta$  to  $\mathbb{Q}$ .

**Lemma 2.** The polynomial  $p_k(x)$  is irreducible over  $\mathbb{Q}$ .

*Proof.* If  $p_k(x)$  is reducible then so is  $p_k(x+1)$ . Recall that by Gauss' lemma, an integral polynomial that factors over  $\mathbb{Q}$  also factors over  $\mathbb{Z}$ . If  $p(x), q(x) \in \mathbb{Z}[x]$ , write  $p(x) \equiv q(x) \pmod{2}$  to mean that the coefficients of p(x) - q(x) are even. Now

$$p_k(x+1) \equiv (x+1)^{2^{k-1}} + 1 \equiv x^{2^{k-1}} \pmod{2}.$$

Hence any factorization of  $p_k(x+1)$  over  $\mathbb{Z}$  into two factors of degree at least one has the form  $p_k(x+1) = (x^r + 2a)(x^s + 2b)$ , where  $r+s = 2^{k-1}$  and a, b

are polynomial of degrees less than r and s, respectively. Hence the constant term of  $p_k(x+1)$  is divisible by 4, a contradiction.

It follows by elementary field theory that every element  $u \in \mathbb{Z}[\zeta]$  can be uniquely written in the form

$$u = b_0 + b_1 \zeta + b_2 \zeta^2 + \dots + b_{n/2-1} \zeta^{n/2-1}, \ b_i \in \mathbb{Z}.$$

The basis for our proof of Theorem 1 is the two different ways to compute  $\det H$  given by equations (1) and (2), yielding the formula

$$\prod_{j=0}^{n-1} (a_0 + \zeta^j a_1 + \zeta^{2j} a_2 + \dots + \zeta^{(n-1)j} a_{n-1}) = \pm n^{n/2} = \pm 2^{2^{k-1}}.$$
 (3)

Thus we have a factorization in  $\mathbb{Z}[\zeta]$  of  $2^{2^{k-1}}$ . Algebraic number theory is concerned with factorization of algebraic integers (and ideals) in algebraic number fields, so we have a vast amount of machinery available to show that no factorization (3) is possible (under the assumption that each  $a_j = \pm 1$ ). Compare Kummer's famous approach toward Fermat's Last Theorem (which led to his creation of algebraic number theory), in which he considered the equation  $x^n + y^n = z^n$  as  $\prod_{\tau^n=1} (x + \tau y) = z^n$ .

We are continuing to assume that  $H = (a_{j-i})$  is an  $n \times n$  circulant Hadamard matrix. We will denote the eigenvalues of H by

$$\gamma_j = a_0 + a_1 \zeta^j + a_2 \zeta^{2j} + \dots + a_{n-1} \zeta^{(n-1)j}$$

**Lemma 3.** For  $0 \le j \le n-1$  we have

$$|\gamma_j| = \sqrt{n}$$
.

Thus all the factors appearing on the left-hand side of (3) have absolute value  $\sqrt{n}$ .

First proof (naive). Let  $H_i$  denote the *i*th row of H, and let  $\cdot$  denote the usual dot product. Then

$$\gamma_{j}\bar{\gamma}_{j} = (a_{0} + a_{1}\zeta^{j} + \dots + a_{n-1}\zeta^{(n-1)j})(a_{0} + a_{1}\zeta^{-j} + \dots + a_{n-1}\zeta^{-(n-1)j})$$

$$= H_{1} \cdot H_{1} + (H_{1} \cdot H_{2})\zeta^{j} + (H_{2} \cdot H_{3})\zeta^{2j} + \dots + (H_{1} \cdot H_{n})\zeta^{(n-1)j}.$$

By the Hadamard property we have  $H_1 \cdot H_1 = n$ , while  $H_1 \cdot H_k = 0$  for  $2 \le k \le n$ , and the proof follows.

Second proof (algebraic). The matrix  $\frac{1}{\sqrt{n}}H$  is a real orthogonal matrix. By linear algebra, all its eigenvalues have absolute value 1. Hence all eigenvalues  $\gamma_j$  of H have absolute value  $\sqrt{n}$ .

Lemma 4. We have

$$2 = (1 - \zeta)^{n/2} u,\tag{4}$$

where u is a unit in  $\mathbb{Z}[\zeta]$ .

*Proof.* Put x = 1 in

$$x^{n/2} + 1 = \prod_{\substack{j=0 \ j \text{ odd}}}^{n-1} (x - \zeta^j)$$

to get  $2 = \prod_{i} (1 - \zeta^{j})$ . Since

$$1 - \zeta^{j} = (1 - \zeta)(1 + \zeta + \dots + \zeta^{j-1}),$$

it suffices to show that  $1+\zeta+\cdots+\zeta^{j-1}$  is a unit when j is odd. Let  $j\bar{j}\equiv 1\,(\mathrm{mod}\,n)$ . Then

$$(1 + \zeta + \dots + \zeta^{j-1})^{-1} = \frac{1 - \zeta}{1 - \zeta^{j}}$$
$$= \frac{1 - (\zeta^{j})^{\bar{j}}}{1 - \zeta^{j}} \in \mathbb{Z}[\zeta],$$

as desired.

**Lemma 5.** We have  $\mathbb{Z}[\zeta]/(1-\zeta) \cong \mathbb{F}_2$ .

*Proof.* Let  $R = \mathbb{Z}[\zeta]/(1-\zeta)$ . The integer 2 is not a unit in  $\mathbb{Z}[\zeta]$ , e.g., because 1/2 is not an algebraic integer. Thus by Lemma 4,  $1-\zeta$  is also not a unit. Hence  $R \neq 0$ .

For all j we have  $\zeta^j = 1$  in R since  $\zeta^j - 1 = (\zeta - 1)(\zeta^{j-1} + \cdots + 1)$ . Hence all elements of R can be written as ordinary integers m. But 0 = 2 in R by Lemma 4, so the only elements of R are 0 and 1.

**Lemma 6.** For all  $0 \le j \le n-1$  there is an integer  $h_j \ge 0$  such that

$$a_0 + a_1 \zeta^j + a_2 \zeta^{2j} + \dots + a_{n-1} \zeta^{(n-1)j} = v_j (1 - \zeta)^{h_j},$$

where  $v_i$  is a unit in  $\mathbb{Z}[\zeta]$ .

*Proof.* Since 2 is a multiple of  $1-\zeta$  by Lemma 4, we have by (3) that

$$\prod_{j=0}^{n-1} (a_0 + a_1 \zeta^j + a_2 \zeta^{2j} + \dots + a_{n-1} \zeta^{(n-1)j}) = 0$$

in  $\mathbb{Z}[\zeta]/(1-\zeta)$ . Since  $\mathbb{Z}[\zeta]/(1-\zeta)$  is a domain by Lemma 6, some factor  $a_0+a_1\zeta^j+\cdots+a_{n-1}\zeta^{(n-1)j}$  is divisible by  $1-\zeta$ . Divide this factor and the right-hand side of (4) by  $1-\zeta$ , and iterate the procedure. We continue to divide a factor of the left-hand side and the right-hand side by  $1-\zeta$  until the right-hand side becomes the unit u. Hence each factor of the original product has the form  $v(1-\zeta)^h$ , where v is a unit.

**Corollary 7.** Either  $\gamma_0/\gamma_1 \in \mathbb{Z}[\zeta]$  or  $\gamma_1/\gamma_0 \in \mathbb{Z}[\zeta]$ . (In fact, both  $\gamma_0/\gamma_1 \in \mathbb{Z}[\zeta]$  and  $\gamma_1/\gamma_0 \in \mathbb{Z}[\zeta]$ , as will soon become apparent, but we don't need this fact here.)

*Proof.* By the previous lemma, each  $\gamma_j$  has the form  $v_j(1-\zeta)^{h_j}$ . If  $h_0 \geq h_1$  then  $\gamma_0/\gamma_1 \in \mathbb{Z}[\zeta]$ ; otherwise  $\gamma_1/\gamma_0 \in \mathbb{Z}[\zeta]$ .

We now need to appeal to a result of Kronecker on elements of  $\mathbb{Z}[\zeta]$  of absolute value one. For completeness we include a proof of this result, beginning with a lemma.

**Lemma 8.** Let  $\theta$  be an algebraic integer such that  $\theta$  and all its conjugates have absolute value one. Then  $\theta$  is a root of unity.

Proof. Suppose the contrary. Let  $deg(\theta) = d$ , i.e.,  $[\mathbb{Q}(\theta) : \mathbb{Q}] = d$ . Now  $\theta$ ,  $\theta^2$ ,  $\theta^3$ ,... are all distinct and hence infinitely many of them have the property that no two are conjugate. Each  $\theta^j \in \mathbb{Q}[\theta]$  and so is the root of a monic integral polynomial of degree at most d. If  $\theta_1, \theta_2, \ldots, \theta_d$  are the conjugates of  $\theta$ , then all the conjugates of  $\theta^j$  are among  $\theta^j_1, \theta^j_2, \ldots, \theta^j_d$ . Hence each  $\theta^j$ 

satisfies the hypothesis that all its conjugates have absolute value 1 (and  $\theta^j$  is an algebraic integer). Thus the rth elementary symmetric function  $e_r$  in  $\theta^j$  and its conjugates has at most  $\binom{d}{r}$  terms, each of absolute value 1, so  $|e_r| \leq \binom{d}{r}$ . Moreover,  $e_r \in \mathbb{Z}$  since  $\theta^j$  is an algebraic integer. It follows that there are only finitely many possible polynomials that can be the irreducible monic polynomials with roots one of the  $\theta^j$ 's, contradicting the fact that there are infinitely many  $\theta^j$ 's for which no two are conjugate.

**Theorem 9** (Kronecker). Let  $\tau$  be any root of unity and  $\alpha \in \mathbb{Q}[\tau]$  with  $|\alpha| = 1$ . Then  $\alpha$  is a root of unity.

*Proof.* We use the basic fact from Galois theory that the Galois group of the extension field  $\mathbb{Q}(\tau)/\mathbb{Q}$  is abelian. Let  $\beta$  be a conjugate of  $\alpha$ , so  $\beta = w(\alpha)$  for some automorphism w of  $\mathbb{Q}(\tau)$ . Apply w to the equation  $\alpha\bar{\alpha} = 1$ . Since complex conjugation is an automorphism of  $\mathbb{Q}(\tau)$  it commutes with w, so we obtain  $\beta\bar{\beta} = 1$ . Hence all the conjugates of  $\alpha$  have absolute value one, so  $\alpha$  is a root of unity by the previous lemma.

We now have all the ingredients to complete the proof of Theorem 1. Note that we have yet to use the hypothesis that  $a_i = \pm 1$ . By Lemma 3 we have

$$|\gamma_1/\gamma_0| = |\gamma_0/\gamma_1| = 1.$$

Hence by Corollary 7 and Theorem 9 we have  $\gamma_0 = \zeta^{-r} \gamma_1$  for some r. Expand  $\gamma_0$  and  $\zeta^{-r} \gamma_1$  uniquely as integer linear combinations of  $1, \zeta, \zeta^2, \ldots, \zeta^{\frac{n}{2}-1}$ :

$$\gamma_0 = a_0 + a_1 + \dots + a_{n-1} = \pm n/2$$

$$\zeta^{-r}\gamma_1 = \zeta^{-r}((a_0 - a_{n/2}) + (a_1 - a_{n/2+1})\zeta + \dots)$$

$$= (a_r - a_{n/2+r}) + (a_{r+1} - a_{n/2+r+1})\zeta + \dots$$

Equating coefficients of  $\zeta^0$  yields  $\pm n/2 = a_r - a_{n/2+r}$ . Since each  $a_i = \pm 1$ , we must have  $n \leq 4$ , completing the proof.

## References

- [1] T. Y. Lam, Representations of finite groups: A hundred years, Part I, *Notices Amer. Math. Soc.* **45** (1998), 361-372; www.ams.org/notices/199803/lam.pdf.
- [2] R. Turyn, Character sums and difference sets, *Pacific J. Math.* **15** (1965), 319–346.

---

## 6 Young diagrams and q-binomial coefficients.

A partition  $\lambda$  of an integer  $n \geq 0$  is a sequence  $\lambda = (\lambda_1, \lambda_2, \ldots)$  of integers  $\lambda_i \geq 0$  satisfying  $\lambda_1 \geq \lambda_2 \geq \cdots$  and  $\sum_{i\geq 1} \lambda_i = n$ . Thus all but finitely many  $\lambda_i$  are equal to 0. Each  $\lambda_i > 0$  is called a part of  $\lambda$ . We sometimes suppress 0's from the notation for  $\lambda$ , e.g., (5,2,2,1), (5,2,2,1,0,0,0), and  $(5,2,2,1,0,0,\ldots)$  all represent the same partition  $\lambda$  (of 10, with four parts). If  $\lambda$  is a partition of n, then we denote this by  $\lambda \vdash n$  or  $|\lambda| = n$ .

**6.1 Example.** There are seven partitions of 5, namely (writing e.g. 221 as short for (2, 2, 1)): 5, 41, 32, 311, 221, 2111, and 11111.

The subject of partitions of integers has been extensively developed, and we will only be concerned here with a small part related to our previous discussion. Given positive integers m and n, let L(m,n) denote the set of all partitions with at most m parts and with largest part at most n. For instance,  $L(2,3) = \{\emptyset, 1, 2, 3, 11, 21, 31, 22, 32, 33\}$ . (Note that we are denoting by  $\emptyset$ the unique partition  $(0,0,\ldots)$  with no parts.) If  $\lambda=(\lambda_1,\lambda_2,\ldots)$  and  $\mu=$  $(\mu_1, \mu_2, \ldots)$  are partitions, then define  $\lambda \leq \mu$  if  $\lambda_i \leq \mu_i$  for all i. This makes the set of all partitions into a very interesting poset, denoted Y and called Young's lattice (named after the British mathematician Alfred Young, 1873– 1940). (It is called "Young's lattice" rather than "Young's poset" because it turns out to have certain properties which define a lattice. However, these properties are irrelevant to us here, so we will not bother to define the notion of a lattice.) We will be looking at some properties of Y in Section 8. The partial ordering on Y, when restricted to L(m,n), makes L(m,n) into a poset which also has some fascinating properties. The diagrams below show L(1,4), L(2,2), and L(2,3).

There is a nice geometric way of viewing partitions and the poset L(m, n). The Young diagram (somtimes just called the diagram) of a partition  $\lambda$  is a left-justified array of squares, with  $\lambda_i$  squares in the *i*th row. For instance, the Young diagram of (4, 3, 1, 1) looks like:

If dots are used instead of boxes, then the resulting diagram is called a Ferrers diagram. The advantage of Young diagrams over Ferrers diagrams is that we can put numbers in the boxes of a Young diagram, which we will do in Section 7. Observe that L(m,n) is simply the set of Young diagrams D fitting in an  $m \times n$  rectangle (where the upper-left (northwest) corner of D is the same as the northwest corner of the rectangle), ordered by inclusion. We will always assume that when a Young diagram D is contained in a rectangle R, the northwest corners agree. It is also clear from the Young diagram point of view that L(m,n) and L(n,m) are isomorphic partially ordered sets, the isomorphism being given by transposing the diagram (i.e., interchanging rows

and columns). If  $\lambda$  has Young diagram D, then the partition whose diagram is  $D^t$  (the transpose of D) is called the *conjugate* of  $\lambda$  and is denoted  $\lambda'$ . For instance, (4,3,1,1)' = (4,2,2,1), with diagram

**6.2 Proposition.** L(m,n) is graded of rank mn and rank-symmetric. The rank of a partition  $\lambda$  is just  $|\lambda|$  (the sum of the parts of  $\lambda$  or the number of squares in its Young diagram).

**Proof.** As in the proof of Proposition 5.6, we leave to the reader everything except rank-symmetry. To show rank-symmetry, consider the complement  $\bar{\lambda}$  of  $\lambda$  in an  $m \times n$  rectangle R, i.e., all the squares of R except for  $\lambda$ . (Note that  $\bar{\lambda}$  depends on m and n, and not just  $\lambda$ .) For instance, in L(4,5), the complement of (4,3,1,1) looks like

If we rotate the diagram of  $\bar{\lambda}$  by 180° then we obtain the diagram of a partition  $\tilde{\lambda} \in L(m,n)$  satisfying  $|\lambda| + |\tilde{\lambda}| = mn$ . This correspondence between  $\lambda$  and  $\tilde{\lambda}$  shows that L(m,n) is rank-symmetric.  $\square$ 

Our main goal in this section is to show that L(m, n) is rank-unimodal and Sperner. Let us write  $p_i(m, n)$  as short for  $p_i(L(m, n))$ , the number of elements of L(m, n) of rank i. Equivalently,  $p_i(m, n)$  is the number of partitions of i with largest part at most n and with at most m parts, or, in other words, the number of distinct Young diagrams with i squares which fit inside an  $m \times n$  rectangle (with the same northwest corner, as explained previously). Though not really necessary for this goal, it is nonetheless interesting to obtain some information on these numbers  $p_i(m, n)$ . First let us consider the total number |L(m, n)| of elements in L(m, n).

**6.3 Proposition.** We have 
$$|L(m,n)| = {m+n \choose m}$$
.

**Proof.** We will give an elegant combinatorial proof, based on the fact that  $\binom{m+n}{m}$  is equal to the number of sequences  $a_1, a_2, \ldots, a_{m+n}$ , where each  $a_j$  is either N or E, and there are m N's (and hence n E's) in all. We will associate a Young diagram D contained in an  $m \times n$  rectangle R with such a sequence as follows. Begin at the lower left-hand corner of R, and trace out the southeast boundary of D, ending at the upper right-hand corner of R. This is done by taking a sequence of unit steps (where each square of R is one unit in length), each step either north or east. Record the sequence of steps, using N for a step to the north and E for a step to the east.

Example. Let m = 5, n = 6,  $\lambda = (4, 3, 1, 1)$ . Then R and D are given by:

| × | × | × | × |  |
|---|---|---|---|--|
| × | × | × |   |  |
| × |   |   |   |  |
| × |   |   |   |  |
|   |   |   |   |  |

The corresponding sequence of N's and E's is NENNEENENEE.

It is easy to see (left to the reader) that the above correspondence gives a bijection between Young diagrams D fitting in an  $m \times n$  rectangle R, and sequences of m N's and n E's. Hence the number of diagrams is equal to  $\binom{m+n}{m}$ , the number of sequences.  $\square$ 

We now consider how many elements of L(m, n) have rank i. To this end,

let q be an indeterminate; and given  $j \geq 1$  define  $[j] = 1 + q + q^2 + \cdots + q^{j-1}$ . Thus [1] = 1, [2] = 1 + q,  $[3] = 1 + q + q^2$ , etc. Note that [j] is a polynomial in q whose value at q = 1 is just j (denoted  $[j]_{q=1} = j$ ). Next define  $[j]! = [1][2] \cdots [j]$  for  $j \geq 1$ , and set [0]! = 1. Thus [1]! = 1, [2]! = 1 + q,  $[3]! = (1+q)(1+q+q^2) = 1+2q+2q^2+q^3$ , etc., and  $[j]!_{q=1} = j!$ . Finally define for  $k \geq j \geq 0$ ,

$$\begin{bmatrix} k \\ j \end{bmatrix} = \frac{[k]!}{[j]![k-j]!}.$$

The expression  $\begin{bmatrix} k \\ j \end{bmatrix}$  is called a *q-binomial coefficient* (or *Gaussian coefficient*). Since  $[r]!_{q=1} = r!$ , it is clear that

$$\begin{bmatrix} k \\ j \end{bmatrix}_{q=1} = \binom{k}{j}.$$

One sometimes says that  $\begin{bmatrix} k \\ j \end{bmatrix}$  is a "q-analogue of the binomial coefficient  $\binom{k}{j}$ ."

**6.4 Example.** We have 
$$\begin{bmatrix} k \\ j \end{bmatrix} = \begin{bmatrix} k \\ k-j \end{bmatrix}$$
 [why?]. Moreover, 
$$\begin{bmatrix} k \\ 0 \end{bmatrix} = \begin{bmatrix} k \\ k \end{bmatrix} = 1$$
 
$$\begin{bmatrix} k \\ 1 \end{bmatrix} = \begin{bmatrix} k \\ k-1 \end{bmatrix} = [k] = 1 + q + q^2 + \dots + q^{k-1}$$
 
$$\begin{bmatrix} 4 \\ 2 \end{bmatrix} = \frac{[4][3][2][1]}{[2][1][2][1]} = 1 + q + 2q^2 + q^3 + q^4$$
 
$$\begin{bmatrix} 5 \\ 2 \end{bmatrix} = \begin{bmatrix} 5 \\ 3 \end{bmatrix} = 1 + q + 2q^2 + 2q^3 + 2q^4 + q^5 + q^6.$$

In the above example,  $\begin{bmatrix} k \\ j \end{bmatrix}$  was always a polynomial in q (and with nonnegative integer coefficients). It is not obvious that this is always the case, but it will follow easily from the following lemma.

**6.5** Lemma. We have

whenever  $k \geq 1$ , with the "initial conditions"  $\begin{bmatrix} 0 \\ 0 \end{bmatrix} = 1$ ,  $\begin{bmatrix} k \\ j \end{bmatrix} = 0$  if j < 0 or j > k (the same initial conditions satisfied by the binomial coefficients  $\binom{k}{j}$ ).

**Proof.** This is a straightforward computation. Specifically, we have

$$\begin{bmatrix} k-1 \\ j \end{bmatrix} + q^{k-j} \begin{bmatrix} k-1 \\ j-1 \end{bmatrix} = \frac{[k-1]!}{[j]![k-1-j]!} + q^{k-j} \frac{[k-1]!}{[j-1]![k-j]!}$$

$$= \frac{[k-1]!}{[j-1]![k-1-j]!} \left( \frac{1}{[j]} + \frac{q^{k-j}}{[k-j]} \right)$$

$$= \frac{[k-1]!}{[j-1]![k-1-j]!} \frac{[k-j] + q^{k-j}[j]}{[j][k-j]}$$

$$= \frac{[k-1]!}{[j-1]![k-1-j]!} \frac{[k]}{[j][k-j]}$$

$$= \begin{bmatrix} k \\ j \end{bmatrix}. \square$$

Note that if we put q = 1 in (26) we obtain the well-known formula

$$\binom{k}{j} = \binom{k-1}{j} + \binom{k-1}{j-1},$$

which is just the recurrence defining Pascal's triangle. Thus equation (26) may be regarded as a q-analogue of the Pascal triangle recurrence.

We can regard equation (26) as a recurrence relation for the q-binomial coefficients. Given the initial conditions of Lemma 6.5, we can use (26) inductively to compute  $\begin{bmatrix} k \\ j \end{bmatrix}$  for any k and j. From this it is obvious by induction that the q-binomial coefficient  $\begin{bmatrix} k \\ j \end{bmatrix}$  is a polynomial in q with nonnegative integer coefficients. The following theorem gives an even stronger result, namely, an explicit combinatorial interpretation of the coefficients.

**6.6 Theorem.** Let  $p_i(m, n)$  denote the number of elements of L(m, n) of rank i. Then

$$\sum_{i>0} p_i(m,n)q^i = \begin{bmatrix} m+n\\m \end{bmatrix}. \tag{27}$$

(NOTE. The sum on the left-hand side is really a *finite* sum, since  $p_i(m, n) = 0$  if i > mn.)

**Proof.** Let P(m,n) denote the left-hand side of (27). We will show that

$$P(0,0) = 1$$
, and  $P(m,n) = 0$  if  $m < 0$  or  $n < 0$  (28)

$$P(m,n) = P(m,n-1) + q^{n}P(m-1,n).$$
(29)

Note that equations (28) and (29) completely determine P(m,n). On the other hand, substituting k=m+n and j=m in (26) shows that  $\begin{bmatrix} m+n \\ m \end{bmatrix}$  also satisfies (29). Moreover, the initial conditions of Lemma 6.5 show that  $\begin{bmatrix} m+n \\ m \end{bmatrix}$  also satisfies (28). Hence (28) and (29) imply that  $P(m,n) = \begin{bmatrix} m+n \\ m \end{bmatrix}$ , so to complete the proof we need only establish (28) and (29).

Equation (28) is clear, since L(0, n) consists of a single point (the empty partition  $\emptyset$ ), so  $\sum_{i\geq 0} p_i(0,n)x^i = 1$ ; while L(m,n) is empty (or undefined, if you prefer) if m < 0 or n < 0,

The crux of the proof is to show (29). Taking the coefficient of  $q^i$  of both sides of (29), we see [why?] that (29) is equivalent to

$$p_i(m,n) = p_i(m,n-1) + p_{i-n}(m-1,n).$$
(30)

Consider a partition  $\lambda \vdash i$  whose Young diagram D fits in an  $m \times n$  rectangle R. If D does not contain the upper right-hand corner of R, then D fits in an  $m \times (n-1)$  rectangle, so there are  $p_i(m,n-1)$  such partitions  $\lambda$ . If on the other hand D does contain the upper right-hand corner of R, then D contains the whole first row of R. When we remove the first row of R, we have left a Young diagram of size i-n which fits in an  $(m-1) \times n$  rectangle. Hence there are  $p_{i-n}(m-1,n)$  such  $\lambda$ , and the proof follows [why?].  $\square$ 

Note that if we set q = 1 in (27), then the left-hand side becomes |L(m, n)| and the right-hand side  $\binom{m+n}{m}$ , agreeing with Proposition 6.3.

NOTE: There is another well-known interpretation of  $\begin{bmatrix} k \\ j \end{bmatrix}$ , this time not of its coefficients (regarded as a polynomial in q), but rather at its values for certain q. Namely, suppose q is the power of a prime. Recall that there is a field  $\mathbb{F}_q$  (unique up to isomorphism) with q elements. Then one can show

that  $\begin{bmatrix} k \\ j \end{bmatrix}$  is equal to the number of j-dimensional subspaces of a k-dimensional vector space over the field  $\mathbb{F}_q$ . We will not discuss the proof here since it is not relevant for our purposes.

As the reader may have guessed by now, the poset L(m,n) is isomorphic to a quotient poset  $B_s/G$  for a suitable integer s>0 and finite group G acting on  $B_s$ . Actually, it is clear that we must have s=mn since L(m,n) has rank mn and in general  $B_s/G$  has rank s. What is not so clear is the right choice of s. To this end, let s0 denote an s1 rectangle of squares. For instance, s3 is given by the 15 squares of the diagram

We now define the group  $G = G_{mn}$  as follows. It is a subgroup of the group  $\mathfrak{S}_R$  of all permutations of the squares of R. A permutation  $\pi$  in G is allowed to permute the elements in each row of R in any way, and then to permute the rows themselves of R in any way. The elements of each row can be permuted in n! ways, so since there are m rows there are a total of  $n!^m$  permutations preserving the rows. Then the m rows can be permuted in m! ways, so it follows that the order of  $G_{mn}$  is given by  $m!n!^m$ . (The group  $G_{mn}$  is called the wreath product of  $\mathfrak{S}_n$  and  $\mathfrak{S}_m$ , denoted  $\mathfrak{S}_n \wr \mathfrak{S}_m$  or  $\mathfrak{S}_m$ . However, we will not discuss the general theory of wreath products here.)

**6.7 Example.** Suppose m = 4 and n = 5, with the boxes of X labelled as follows.

| 1  | 2  | 3  | 4  | 5  |
|----|----|----|----|----|
| 6  | 7  | 8  | 9  | 10 |
| 11 | 12 | 13 | 14 | 15 |
| 16 | 17 | 18 | 19 | 20 |

Then a typical permutation  $\pi$  in G(4,5) looks like

| 16 | 20 | 17 | 19 | 18 |
|----|----|----|----|----|
| 4  | 1  | 5  | 2  | 3  |
| 12 | 13 | 15 | 14 | 11 |
| 7  | 9  | 6  | 10 | 8  |

i.e.,  $\pi(16) = 1$ ,  $\pi(20) = 2$ , etc.

We have just defined a group  $G_{mn}$  of permutations of the set  $R_{mn}$  of squares of an  $m \times n$  rectangle. Hence  $G_{mn}$  acts on the boolean algebra  $B_R$  of all subsets of the set R. The next lemma describes the orbits of this action.

**6.8 Lemma.** Every orbit  $\mathcal{O}$  of the action of  $G_{mn}$  on  $B_R$  contains exactly one Young diagram D (i.e., exactly one subset  $D \subseteq R$  such that D is left-justified, and if  $\lambda_i$  is the number of elements of D in row i of R, then  $\lambda_1 \geq \lambda_2 \geq \cdots \geq \lambda_m$ ).

**Proof.** Let S be a subset of R, and suppose that S has  $\alpha_i$  elements in row i. If  $\pi \in G_{mn}$  and  $\pi \cdot S$  has  $\beta_i$  elements in row i, then  $\beta_1, \ldots, \beta_m$  is just some permutation of  $\alpha_1, \ldots, \alpha_m$  [why?]. There is a unique permutation  $\lambda_1, \ldots, \lambda_m$  of  $\alpha_1, \ldots, \alpha_m$  satisfying  $\lambda_1 \geq \cdots \geq \lambda_m$ , so the only possible Young diagram D in the orbit  $\pi \cdot S$  is the one of shape  $\lambda = (\lambda_1, \ldots, \lambda_m)$ . It's easy to see that the Young diagram  $D_{\lambda}$  of shape  $\lambda$  is indeed in the orbit  $\pi \cdot S$ . For by permuting the elements in the rows of R we can left-justify the rows of S, and then by permuting the rows of R themselves we can arrange the row sizes of S to be in weakly decreasing order. Thus we obtain the Young diagram  $D_{\lambda}$  as claimed.  $\square$ 

We are now ready for the main result of this section.

**6.9 Theorem.** The quotient poset  $B_{R_{mn}}/G_{mn}$  is isomorphic to L(m,n).

**Proof.** Each element of  $B_R/G_{mn}$  contains a unique Young diagram  $D_{\lambda}$  by Lemma 6.8. Moreover, two different orbits cannot contain the same Young diagram D since orbits are disjoint. Thus the map  $\varphi: B_R/G_{mn} \to L(m,n)$ 

defined by  $\varphi(\mathcal{O}_{\lambda}) = \lambda$  is a bijection (one-to-one and onto), where  $\mathcal{O}_{\lambda}$  is the orbit containing  $D_{\lambda}$ . We claim that in fact  $\varphi$  is an isomorphism of partially ordered sets. We need to show the following: Let  $\mathcal{O}$  and  $\mathcal{O}^*$  be orbits of  $G_{mn}$  (i.e., elements of  $B_R/G_{mn}$ ). Let  $D_{\lambda}$  and  $D_{\lambda^*}$  be the unique Young diagrams in  $\mathcal{O}$  and  $\mathcal{O}^*$ , respectively. Then there exist  $D \in \mathcal{O}$  and  $D^* \in \mathcal{O}^*$  satisfying  $D \subseteq D^*$  if and only if  $\lambda \leq \lambda^*$  in L(m, n).

The "if" part of the previous sentence is clear, for if  $\lambda \leq \lambda^*$  then  $D_{\lambda} \subseteq D_{\lambda^*}$ . So assume there exist  $D \in \mathcal{O}$  and  $D^* \in \mathcal{O}^*$  satisfying  $D \subseteq D^*$ . The lengths of the rows of D, written in decreasing order, are  $\lambda_1, \ldots, \lambda_m$ , and similarly for  $D^*$ . Since each row of D is contained in a row of  $D^*$ , it follows that for each  $1 \leq j \leq m$ ,  $D^*$  has at least j rows of size at least  $\lambda_j$ . Thus the length  $\lambda_j^*$  of the jth largest row of  $D^*$  is at least as large as  $\lambda_j$ . In other words,  $\lambda_j \leq \lambda_j^*$ , as was to be proved.  $\square$ 

Combining the previous theorem with Theorem 5.9 yields:

**6.10 Corollary.** The posets L(m, n) are rank-symmetric, rank-unimodal, and Sperner.

Note that the rank-symmetry and rank-unimodality of L(m,n) can be rephrased as follows: The q-binomial coefficient  $\begin{bmatrix} m+n \\ m \end{bmatrix}$  has symmetric and unimodal coefficients. While rank-symmetry is easy to prove (see Proposition 6.2), the unimodality of the coefficients of  $\begin{bmatrix} m+n \\ m \end{bmatrix}$  is by no means apparent. It was first proved by J. Sylvester in 1878 by a proof similar to the one above, though stated in the language of the invariant theory of binary forms. For a long time it was an open problem to find a combinatorial proof that the coefficients of  $\begin{bmatrix} m+n \\ m \end{bmatrix}$  are unimodal. Such a proof would give an explicit injection (one-to-one function)  $\mu: L(m,n)_i \to L(m,n)_{i+1}$  for  $i < \frac{1}{2}mn$ . (One difficulty in finding such maps  $\mu$  is to make use of the hypothesis that  $i < \frac{1}{2}mn$ .) Finally around 1989 such a proof was found by Kathy O'Hara. However, O'Hara's proof has the defect that the maps  $\mu$  are not order-matchings. Thus her proof does not prove that L(m,n) is Sperner, but only that it's rank-unimodal. It is an outstanding open problem in algebraic combinatorics to find an explicit order-matching  $\mu: L(m,n)_i \to L(m,n)_{i+1}$ for  $i < \frac{1}{2}mn$ .

Note that the Sperner property of L(m,n) (together with the fact that the

largest level is in the middle) can be stated in the following simple terms: The largest possible collection  $\mathcal{C}$  of Young diagrams fitting in an  $m \times n$  rectangle such that no diagram in  $\mathcal{C}$  is contained in another diagram in  $\mathcal{C}$  is obtained by taking all the diagrams of size  $\frac{1}{2}mn$ . Although the statement of this fact requires almost no mathematics to understand, there is no known proof that doesn't use algebraic machinery. (The several known algebraic proofs are all closely related, and the one we have given is the simplest.) Corollary 6.10 is a good example of the efficacy of algebraic combinatorics.

An application to number theory. There is an interesting application of Corollary 6.10 to a number-theoretic problem. Fix a positive integer k. For a finite subset S of  $\mathbb{R}^+ = \{\alpha \in \mathbb{R} : \alpha > 0\}$ , and for a real number  $\alpha > 0$ , define

$$f_k(S, \alpha) = \# \left\{ T \in {S \choose k} : \sum_{t \in T} t = \alpha \right\}$$

In other words,  $f_k(S, \alpha)$  is the number of k-element subsets of S whose elements sum to  $\alpha$ . For instance,  $f_3(\{1, 3, 4, 6, 7\}, 11) = 2$ , since 1 + 3 + 7 = 1 + 4 + 6 = 11.

Given positive integers k < n, our object is to maximize  $f_k(S, \alpha)$  subject to the condition that #S = n. We are free to choose both S and  $\alpha$ , but k and n are fixed. Call this maximum value  $h_k(n)$ . Thus

$$h_k(n) = \max_{\substack{\alpha \in \mathbb{R}^+ \\ S \subset \mathbb{R}^+ \\ \#S = n}} f_k(S, \alpha).$$

What sort of behavior can we expect of the maximizing set S? If the elements of S are "spread out," say  $S = \{1, 2, 4, 8, \dots, 2^{n-1}\}$ , then all the subset sums of S are distinct. Hence for any  $\alpha \in \mathbb{R}^+$  we have  $f_k(S, \alpha) = 0$  or 1. Similarly, if the elements of S are "unrelated" (e.g., linearly independent over the rationals, such as  $S = \{1, \sqrt{2}, \sqrt{3}, e, \pi\}$ ), then again all subset sums are distinct and  $f_k(S, \alpha) = 0$  or 1. These considerations make it plausible that we should take  $S = [n] = \{1, 2, \dots, n\}$  and then choose  $\alpha$  appropriately. In other words, we are led to the conjecture that for any  $S \in \binom{\mathbb{R}^+}{n}$  and  $\alpha \in \mathbb{R}^+$ , we have

$$f_k(S, \alpha) \le f_k([n], \beta),$$
 (31)

for some  $\beta \in \mathbb{R}^+$  to be determined.

First let us evaluate  $f_k([n], \alpha)$  for any  $\alpha$ . This will enable us to determine the value of  $\beta$  in (31). Let  $S = \{i_1, \ldots, i_k\} \subseteq [n]$  with

$$1 \le i_1 < i_2 < \dots < i_k \le n, \quad i_1 + \dots + i_k = \alpha.$$
 (32)

Let  $j_r = i_r - r$ . Then (since  $1 + 2 + \dots + k = \binom{k+1}{2}$ )

$$n-k \ge j_k \ge j_{k-1} \ge \dots \ge j_1 \ge 0, \quad j_1 + \dots + j_k = \alpha - \binom{k+1}{2}.$$
 (33)

Conversely, given  $j_1, \ldots, j_k$  satisfying (33) we can recover  $i_1, \ldots, i_k$  satisfying (32). Hence  $f_k([n], \alpha)$  is equal to the number of sequences  $j_1, \ldots, j_k$  satisfying (33). Now let

$$\lambda(S) = (j_k, j_{k-1}, \dots, j_1).$$

Note that  $\lambda(S)$  is a partition of the integer  $\alpha - \binom{k+1}{2}$  with at most k parts and with largest part at most n-k. Thus

$$f_k([n], \alpha) = p_{\alpha - \binom{k+1}{2}}(k, n-k),$$
 (34)

or equivalently,

$$\sum_{\alpha \ge \binom{k+1}{2}} f_k([n], \alpha) q^{\alpha - \binom{k+1}{2}} = {n \brack k}.$$

By the rank-unimodality (and rank-symmetry) of L(n-k,k) (Corollary 6.10), the largest coefficient of  $\begin{bmatrix} n \\ k \end{bmatrix}$  is the middle one, that is, the coefficient of  $\lfloor k(n-k)/2 \rfloor$ . It follows that for fixed k and n,  $f_k([n], \alpha)$  is maximized for  $\alpha = \lfloor k(n-k)/2 \rfloor + \binom{k+1}{2} = \lfloor k(n+1)/2 \rfloor$ . Hence the following result is plausible.

**6.11 Theorem.** Let 
$$S \in {\mathbb{R}^+ \choose n}$$
,  $\alpha \in \mathbb{R}^+$ , and  $k \in \mathbb{P}$ . Then  $f_k(S, \alpha) \leq f_k([n], \lfloor k(n+1)/2 \rfloor)$ .

**Proof.** Let  $S = \{a_1, \ldots, a_n\}$  with  $0 < a_1 < \cdots < a_n$ . Let T and U be distinct k-element subsets of S with the same element sums, say  $T = \{a_{i_1}, \ldots, a_{i_k}\}$  and  $U = \{a_{j_1}, \ldots, a_{j_k}\}$  with  $i_1 < i_2 < \cdots < i_k$  and  $j_1 < j_2 < \cdots < j_k$ . Define  $T^* = \{i_1, \ldots, i_k\}$  and  $U^* = \{j_1, \ldots, j_k\}$ , so  $T^*, U^* \in \binom{[n]}{k}$ . The crucial observation is the following:

**Claim.** The elements  $\lambda(T^*)$  and  $\lambda(U^*)$  are incomparable in L(k, n-k), i.e., neither  $\lambda(T^*) \leq \lambda(U^*)$  nor  $\lambda(U^*) \leq \lambda(T^*)$ .

**Proof of claim.** Suppose not, say  $\lambda(T^*) \leq \lambda(U)^*$  to be definite. Thus by definition of L(k, n-k) we have  $i_r - r \leq j_r - r$  for  $1 \leq r \leq k$ . Hence  $i_r \leq j_r$  for  $1 \leq r \leq k$ , so also  $a_{i_r} \leq a_{j_r}$  (since  $a_1 < \cdots < a_n$ ). But  $a_{i_1} + \cdots + a_{i_k} = a_{j_1} + \cdots + a_{j_k}$  by assumption, so  $a_{i_r} = a_{j_r}$  for all r. This contradicts the assumption that T and U are distinct and proves the claim.

It is now easy to complete the proof of Theorem 6.11. Suppose that  $S_1, \ldots, S_r$  are distinct k-element subsets of S with the same element sums. By the claim,  $\{\lambda(S_1^*), \ldots, \lambda(S_r^*)\}$  is an antichain in L(k, n-k). Hence r cannot exceed the size of the largest antichain in L(k, n-k). By Theorem 6.6 and Corollary 6.10, the size of the largest antichain in L(k, n-k) is given by  $p_{\lfloor k(n-k)/2 \rfloor}(k, n-k)$ . By equation (34) this number is equal to  $f_k([n], \lfloor k(n+1)/2 \rfloor)$ . In other words,

$$r \le f_k([n], \lfloor k(n+1)/2 \rfloor),$$

which is what we wanted to prove.  $\Box$ 

Note that an equivalent statement of Theorem 6.11 is that  $h_k(n)$  is equal to the coefficient of  $\lfloor k(n-k)/2 \rfloor$  in  $\begin{bmatrix} n \\ k \end{bmatrix}$  [why?].
