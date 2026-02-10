# 18.408 Topics in Theoretical Computer Science Fall 2022 Lecture 1

## Dor Minzer

# 1 Introduction

The main topic of this course is Probabilistically Checkable Proofs (PCP), an active area of TCS which emerged in the early 90's and has had a tremendous impact on many other areas in TCS. One of the most prominent applications of PCPs is to hardness of approximation, wherein the theory of NP-hardness is extended to approximation problems. In an undergraduate complexity course, one often sees NP-hardness results from the 70's asserting that many famous combinatorial optimization problems (3SAT, Clique, Set-Cover, etc.) are NP-hard. It turns out that even approximating the optimal solution to these problems is still NP-hard, but to prove such results one needs an analog of the Cook-Levin theorem for approximation problems. This result is called the PCP theorem, and the first half of the course will be focused on the proof of this result. Aside from that, one then needs to develop Karp-type reductions that respect the notion of approximation to leverage the PCP theorem to prove NP-hardness results for other optimization problems (similar to the classical theory of NP-completeness). The second half of the course will focus on that.

So, what is a PCP? To begin this discussion, let us first view the standard NP-hardness of the 3-SAT problem in several equivalent ways. Recall that a 3-CNF formula is a formula of the form  $\phi(x_1,\ldots,x_n)=C_1\wedge C_2\wedge\ldots C_m$ , where each  $C_i$  is a clause of the form  $(\alpha\vee\beta\vee\gamma)$  where each one of  $\alpha,\beta,\gamma$  is a literal (i.e. one of the input variables  $x_i$  or its negation). The computational problem 3-SAT is the problem in which one is given, as an input, a 3-CNF formula  $\phi(x_1,\ldots,x_n)$ , and the goal is to decide if it is satisfiable or not. Namely, to decide if there is an assignment  $A\colon\{x_1,\ldots,x_n\}\to\{0,1\}$  that satisfies each one of the clauses of  $\phi$ . Thus, in terms of languages, we write

$$3\text{-SAT} = \{ \phi \mid \phi \text{ is a satisfiable } 3\text{-CNF formula} \}.$$

The Cook-Levin theorem is one of the most basic results in complexity theory, asserting that 3-SAT is NP-hard. That is, if 3-SAT can be solved in polynomial time, then P = NP. Another formulation of this theorem (which is a bit stronger), is that given any language  $L \in NP$ , checking membership in L can be efficiently reduced to checking membership in 3-SAT. Namely, there exists a reduction map  $f : \{0,1\}^* \to \{0,1\}^*$  such that: if  $z \in L$ , then  $f(z) = \phi_z \in 3$ -SAT, and if  $z \notin L$ , then  $f(z) = \phi_z \notin 3$ -SAT. In other words, an instance z to problem L can be encoded as a Boolean formula  $\phi_z = f(z)$  so that "witnesses" to satisfiability of  $\phi_z$  encode witnesses to the instance z being in L.

What is so special about 3-SAT, and what makes this useful? To illustrate that and draw our attention to several parameters of interest, we consider an NP-verifier for the 3-SAT language. Recall that an NP-verifier is a polynomial time Turing Machine that gets as input a formula  $\phi$ , and a witness w. We say the verifier accepts  $\phi$  if there is some witness w that makes it accept, and we say the verifier rejects if it rejects no matter what witness w the verifier is given. In the case of 3-SAT, the verifier is quite simple; the witness w is simply a supposed satisfying assignment for  $\phi$ , and the verifier checks that it indeed satisfies the formula  $\phi$ .

#### 1.1 Probabilistic verifiers

So far, there is nothing probabilistic about this, so we adopt a somewhat different view of this classical verifier. The witness w is still a supposed satisfying assignment, but now the verifier picks a random clause  $C_i$  from  $\phi$  and checks whether it is satisfied or not. Below we consider a few notions that will be important for us throughout this course, and explain them through this example.

- 1. **Completeness:** the completeness parameter measures what is the probability the verifier accepts provided the input  $\phi$  is in the language, and the verifier is given a correct witness. Throughout most of this course, we will be discussing perfect completeness, i.e. the case this probability is 1; this is indeed the case for the verifier above.
- 2. **Soundness:** the soundness parameter measures the probability the verifier accepts provided the input  $\phi$  is not the language, and the verifier is given any witness (typically thought of the witness that "fools" the verifier the most). In the above example, we know that if  $\phi$  is not satisfiable, then the assignment that w encodes cannot possibly satisfy all of the clauses of  $\phi$ , hence there is some clause  $C_i$  that is not satisfied by it. The probability that the verifier picked that clause is  $\frac{1}{m}$ , and therefore the probability the verifier accepts is at most  $1 \frac{1}{m}$
- 3. Locality/number of queries: this refers to the number of entries of the witness w the verifier makes access to. In this case, the verifier looks at a clause  $C_i$  containing 3 literals, hence has to read 3 locations from the witness w. Hence, we say that the number of queries of the verifier is 3.
- 4. **Alphabet size:** the alphabet size is the size of each one of the queries the verifier makes. In this case, the verifier just reads off 3 bits from w, hence its alphabet size is 2.

In light of this, we can say that the main features of the Cook-Levin theorem that make it so useful is that it shows that any language in NP admits a probabilistic verifier which is very local, making only 3 queries to the witness whose alphabet is of size 2. Indeed, given any language  $L \in \text{NP}$ , the verifier would use the reduction f above to reduce an instance z of L to a formula  $\phi_z = f(z)$ , and think of its witness as an assignment to the formula  $\phi_z$ . The main weakness of this theorem, in this language, is that the soundness guarantee is rather poor — the probability the verifier accepts an input not in the language is still close to 1.

One formulation of the PCP theorem in this language is the following counter-intuitive looking statement. There exists an absolute constant  $\varepsilon > 0$ , such that any language  $L \in \text{NP}$  admits a probabilistic verifier V that has completeness 1, soundness at most  $1 - \varepsilon$  that makes O(1) queries and has alphabet size O(1). Namely there is a verifier just like before that is able to "catch" cheating witnesses with much higher probability than before! Looking at the previous verifier, it is completely unclear how to do something like that (or if it is even possible), but as we will see in this course, it is possible (though it will take us time).

## 1.2 A combinatorial point of view of PCP

Next, we present an equivalent combinatorial view of PCP, which is somewhat easier to think about in the context of hardness of approximation. For parameters  $0 \le s < c \le 1$ , the computational problem gap-3-SAT[c,s] is the promise problem wherein one is given, as an input, a 3-CNF formula  $\phi$ ; it is promised that either there exists an assignment to  $\phi$  satisfying at least c fraction of the clauses in it, or that any assignment to  $\phi$  satisfies at most s fraction of the clauses of  $\phi$ . The goal in the problem gap-3-SAT[c,s] is to distinguish between these two cases. That is, to solve gap-3-SAT[c,s] one has to design a Turing Machine that accepts the former type of instances, and rejects the latter type of instances.

In this formulation, the Cook-Levin theorem asserts that gap-3-SAT  $\left[1, 1 - \frac{1}{m}\right]$  is NP-hard, and the PCP theorem is equivalent to the following assertion:

**Theorem 1.1.** There exists  $\varepsilon > 0$  such that gap-3-SAT[1, 1 -  $\varepsilon$ ] is NP-hard.

Hence, one sees that in gap-3-SAT[c, s], the parameters s and c correspond to the soundness and completeness of the verifier; the alphabet size and the number of queries are already apparent from the form of the definition of 3-SAT.

As we will see in the second half of this course, the above combinatorial view of PCP is useful when doing Karp-style reductions with the goal of showing hardness of approximation results. Indeed, you can prove (try this!) that if gap-3-SAT[c,s] is NP-hard, then it is NP-hard to approximate the maximum number of clauses that can be satisfied in a formula  $\phi$  within factor  $\frac{s}{c}$ . Hence, to get the best hardness of approximation results one wants to optimize the ratio between the soundness and the completeness parameter. The notion of gap problem carries with it more information though, regarding the "location" of the hardness.

Hence, the PCP theorem implies in particular that there is  $\varepsilon>0$  such that approximating the number of clauses that can be satisfied in a given 3-CNF formula within factor  $1-\varepsilon$  is NP-hard, and a natural question is what is the "right"  $\varepsilon$  in this result? Is there some  $s\in(0,1)$  such that approximating within factor  $s+\delta$  is NP-hard but approximating within factor  $s-\delta$  can be done in polynomial time?

## 1.3 PCP as a 2-Prover, 1-Round game

PCP can also be used as an interrogation technique. Consider the setting in which we have a computationally weak verifier V, and 2 very powerful provers. The provers try to convince the verifier V that some 3-CNF formula  $\phi$  is satisfiable, but they physically sit in two different rooms with no ability of communicating with each other. Is there some scheme that allows the provers convince the verifier that  $\phi$  is satisfiable if this is indeed the case? Can the provers convince the verifier that  $\phi$  is satisfiable when in actuality it isn't? Of course, V can simply ask one of the provers for a whole assignment to the formula  $\phi$ , and check all clauses are satisfied; V doesn't have time for that though. Another thing V can do is choose a clause  $C_i$  randomly, send it to one of the provers, and ask for an assignment to it. This though, fails miserably, as the prover can just cheat and just assign some value to the variables in  $C_i$  that satisfies this clause. What should V do then?

Well, V can sample a clause  $C_i$  and choose randomly one of the variables in it, say  $x_j$ . The verifier V can then send all of the variables of  $C_i$  to the first prover, and only the variable  $x_j$  to the second prover. The verifier expects to get, as answers from each one of the provers, assignments to the variables they received. Upon getting these answers, V checks that the given assignment satisfies  $C_i$ , and that the two provers assigned the same value to  $x_j$  (that is, that they are consistent).

The model of 2-prover-1-round protocols can be thought of more generally in the context of language L, not only for 3-SAT. In this formulation, the PCP theorem tells us that any language  $L \in NP$  has a 2-prover-1-round protocol that has:

- 1. Completeness: that is, there are prover strategies that manage to convince V of "true statements" namely if the protocol is ran on a common input z that is in L, then V always accept.
- 2. Soundness: that is, if the common input z is not in L, any prover strategy (even a malicious one) makes V accept with probability at most 1/3.
- 3. Efficient: the verifier V is very efficient, using  $O(\log n)$  randomness and reading only O(1) bits from the answer of each prover.

#### 1.4 Course overview

Since this is the first time this course is ran, the exact material we cover is yet to be determined; below is a tentative plan.

- Error-Correcting Codes: We will begin the course by describing a much simpler, completely combinatorial analog of PCPs, which are also an important building block in PCP constructions. In particular, we will define linear error correcting codes and their various parameters, give examples (Reed-Solomon, Reed-Muller, Hadamard) and describe concatenation of error correcting codes. We will also discuss local testing and local correction of codes.
- 2. The algebraic proof of the PCP theorem. This part of the course will consist of several weeks, and in it we will prove the basic PCP theorem. The way the proof works is by first doing a reduction that gets a large gap between the completeness and soundness parameters, but as a result significantly increases the number of queries and the alphabet size. This will be relatively easy, and the bulk of the work then will be to reduce the number of queries and the alphabet size back to be O(1). For that, we will present the sum-check protocol, proof composition, low-degree testing, aggregation of queries and the local-to-global phenomenon.
- 3. Hardness Amplification and the Long-Code Framework. Next, we will present the tools that are used in conjunction with the PCP theorem in order to establish hardness of approximation results. In particular, we will discuss the parallel repetition technique (an operation that improves the soundness of a PCP while keeping the number of queries the same) and the Long-Code framework. We will see several example of results that can be established this way. In particular, we will prove hardness of approximation results to popular combinatorial optimization problems such as Clique, Vertex-Cover and Linear-Equations over finite fields.
- 4. **Extreme Forms of the PCP theorem.** Next, we will discuss several improved forms of the PCP theorem that are conjectured to be true (yet are all open). By that, we often refer to pushing some feature of the PCP theorem to "the limit", and asking if there is a PCP construction that achieves that. These include size efficient PCPs, time efficient PCPs, the Sliding Scale Conjecture and the Unique-Games Conjecture.
- 5. Advanced Topics. Towards the end of the course we will discuss more advanced topics. These include the Unique-Games Conjecture (what it implies and the current state of affairs), sub constant soundness PCPs, optimal hardness of Clique and Vertex-Cover.

## 1.5 Applications of PCPs

PCPs have a wide array of applications throughout TCS (hardness of approximation, cryptography, interactive protocols and more), as well as some practical ones (most prominently in blockchains), and exploring such applications could be a good direction for a final project in the course. For most of the course though, we will focus on the applications of PCPs to hardness of approximation, and below we give a few examples of results we may see.

**Linear equations over finite fields.** An instance of the Max-3-Lin<sub>2</sub> problem consists of a set of variables  $X = \{x_1, \ldots, x_n\}$  and a set of equations  $E = \{e_1, \ldots, e_m\}$ , wherein each equation  $e \in E$  is of the form  $x_i + x_j + x_k = b_{i,j,k}$  where  $b_{i,j,k} \in \mathbb{F}_2$  is a constant; addition is performed over  $(\mathbb{F}_2, + \pmod{2})$ . Given

an instance (X, E), the goal is to find an assignment to the variables  $A: X \to \mathbb{F}_2$  that satisfies as many of the equations as possible. What is the complexity of Max-3-Lin<sub>2</sub>?

Well, if we are given (X, E) that is promised to be fully satisfiable (i.e. that there is an assignment satisfying all of its equations), then we can find a satisfying assignment efficiently by using Gaussian Elimination. In gap notations, this means that gap-Max-3-Lin<sub>2</sub>[1, 1] can be solved in polynomial time. What if we relax the promise, and only say that (X, E) is  $(1 - \varepsilon)$ -satisfiable, i.e. that there is an assignment satisfying  $1 - \varepsilon$  fraction of the equations? Note that one can always satisfy at least half of the equations by trying the "all 0" assignment and the "all 1 assignment". It turns out that beating this trivial algorithm is NP-hard:

**Theorem 1.2** (Hastad). For all  $\varepsilon > 0$ , gap-Max-3-Lin<sub>2</sub> $[1 - \varepsilon, 1/2 + \varepsilon]$  is NP-hard.

Minimum Vertex-Cover. A vertex cover in a graph G=(V,E) is a set of vertices  $C\subseteq V$  that contains at least one endpoint of each edge. The goal in the Vertex-Cover problem is to find, given a graph G=(V,E), the smallest vertex cover in it; denote the fractional size of it by VC(G). As we will see, there is an easy 2-approximation algorithm, i.e. an algorithm that given G efficiently finds a set  $C\subseteq V$  that is a vertex cover of G and has  $|C|\leqslant 2VC(G)\,|V|$ . It is suspected, with strong evidence, that this is essentially the best one can do (and this is related to the Unique-Games Conjecture and all), but this result is not known. The best known result to date is:

**Theorem 1.3.** For all  $\varepsilon > 0$ , approximating the minimum vertex-cover in a graph within factor  $\sqrt{2} - \varepsilon$  is NP-hard. Moreover, the promise problem gap-Vertex-Cover $[1 - \varepsilon, 1/\sqrt{2} + \varepsilon]$  is NP-hard.

In words, the "moreover" part of the theorem states it is NP-hard to distinguish between the case that almost all of the vertices of the graph are needed to cover all edges, and the case in which at most  $1/\sqrt{2}+o(1)$  fraction of them suffice.

Independent sets in graphs. An instance of the Independent-Set problem consists of a graph G=(V,E), and the goal is to find the largest set of vertices  $I\subset V$  that contains no edge from E; such sets are called independent sets. Suppose we are given a graph G=(V,E) which is promised to contain an independent set of fractional size  $\frac{1}{2}+\varepsilon$ ; what is the largest independent set we may find? Well, it turns out that the Vertex-Cover and the Independent-Set problems are very much related, and one can show that in this case, one can use the 2-approximation algorithm from above to find an independent set of fractional size  $2\varepsilon$  in G. It is again suspected that this is essentially the best one can do (again related to the Unique-Games Conjecture), but the best known result to date is the following:

**Theorem 1.4.** For all  $\varepsilon > 0$ , gap-Independent-Set $[1 - 1/\sqrt{2} - \varepsilon, \varepsilon]$  is NP-hard.

In words, given a graph, it is NP-hard to distinguish between the cases it contains an independent set of fractional size  $1 - 1/\sqrt{2} - \varepsilon$ , and the case it doesn't even contain an independent set of fractional size  $\varepsilon$ .

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lectures 2 and 3

#### Dor Minzer

The topic for today is error correcting codes, which can be thought of as combinatorial analogs of PCPs. We will give some basic definitions and examples of error correcting codes, as well as discuss notions such as local testability and concatenation/ composition of error correcting codes. In particular, we will show how to construct an explicit error correcting code with constant rate, relative distance and binary alphabet. This process is analogous to the process we will take in future lectures in the proof of the PCP theorem (but simpler). In particular, PCP considerations will motivate us to discuss the notions of locally testable codes, locally decodeable codes and random self-correction.

## 1 Error Correcting Codes

Let  $\Sigma$  be a finite alphabet, and let  $n \in \mathbb{N}$  be thought of as very large. An error correcting code is a collection of vectors  $C \subseteq \Sigma^n$ . The rate of an error correcting code measures how dense C is in  $\Sigma^n$  in logarithmic scale, i.e.  $R = \frac{\log(|C|)}{\log(|\Sigma^n|)}$ , and the distance of the code C is defined to be

$$d(C) = \min_{x,y \in C, x \neq y} \Delta(x,y), \qquad \text{where} \quad \Delta(x,y) = \# \left\{ i \in [n] \mid x_i \neq y_i \right\}.$$

Thus, the relative distance of C is defined as  $d_{\text{relative}}(C) = \frac{d(C)}{n}$ . Often times, the length of a codeword, n, is referred to as the block length. With these parameters in mind, we often refer to C as an  $(n, d_{\text{relative}}(C), R(C), q)$ -code.

Intuitively, it is clear that there is tension between the relative distance of a code and the rate of the code. The denser the code is, the less "space" there can be between distinct codewords. Indeed, many results in coding theory are concerned with exactly nailing down the tradeoff between parameters error correcting codes can achieve. For example, one of the most basic results of this form is the *Hamming bound*. Define  $B_x = \left\{z \in \Sigma^n \mid \Delta(x,z) \leqslant \frac{1}{2}d(C)n-1\right\}$  for each  $x \in C$ , namely the ball around x of radius  $\frac{1}{2}d(C)n-1$ . Note that by the definition of relative distance, the balls  $B_x$  and  $B_y$  are disjoint for any two distinct points  $x,y \in C$ , and so

$$|\Sigma^n| \geqslant |\bigcup_{x \in C} B_x| = \sum_{x \in C} |B_x| \geqslant |C| \binom{n}{\frac{1}{2} d(C) n - 1} |\Sigma|^{\frac{1}{2} d(C) n - 1}.$$

Simplifying, one sees that  $R + \frac{d(C)}{2} + o(1) \le 1$ . Thus, it is already clear that a code cannot have both relative distance and rate being close to 1.

Our interest in error correcting codes in this course is somewhat different, and we will not care so much about obtaining tight tradeoffs between parameters. For us, it will often be good enough that a code has constant relative distance, and not-too-terrible rate.

One particularly important class of codes is the class of linear error correcting codes. In this context, the alphabet  $\Sigma$  is equipped with an algebraic structure, and more precisely a field, say  $\Sigma = \mathbb{F}_q$ , where q is a power of a prime number.

**Definition 1.1.** A linear error correcting code is a subset  $C \subseteq \mathbb{F}_q^n$  which is a subspace of  $\mathbb{F}_q^n$  over  $\mathbb{F}_q$ .

The distance of a linear error correcting code. Let  $C \subseteq \mathbb{F}_q^n$  be a linear error correcting code. Note that since C is a subspace we have  $0 \in C$ , so the distance of the code always satisfies

$$d(C) = \min_{x \neq y \in C} \Delta(x,y) \geqslant \min_{x \in C, x \neq 0} \Delta(x,0) = \min_{x \in C \setminus \{0\}} \left| \operatorname{supp}(x) \right|.$$

In fact, this can be observed to be an equality. For any x,y we have that  $\Delta(x,y)=\Delta(x-y,0)$ , and as C is a subspace, if  $x,y\in C$  are distinct then  $x-y\in C\setminus\{0\}$ . Thus we get that:

**Claim 1.2.** For a linear error correcting code  $C \subseteq \mathbb{F}_q^n$  we have that  $d(C) = \min_{x \in C \setminus \{0\}} |\text{supp}(x)|$ .

In words, the distance of a linear error correcting code is the minimum Hamming weight of a non-zero codeword from it.

The rate as dimension. The rate of a linear error correcting code C also takes a special meaning. Let  $k = \dim(C)$ ; observe that  $|C| = q^k$ , so  $R(C) = \frac{\log |C|}{\log q^n} = \frac{k}{n}$ . Hence the rate of C is the dimension of C as a subspace divided by the dimension of the ambient vector space. We will often times denote  $k = \dim(C)$ , and refer to k as the dimension of the code.

**Generating matrices.** Since any linear correcting code C is a subspace, we can view it as the image of some linear transformation; more precisely, there is a matrix  $M: \mathbb{F}_q^k \to \mathbb{F}_q^n$  so that  $\mathsf{Image}(M) = C$ . Indeed, one way to construct M is by picking a basis  $v_1, \ldots, v_k$  of C and defining  $Me_i = v_i$ . Such matrix M is called a *generating matrix* of C. Written otherwise, we say  $M \in \mathbb{F}_q^{n \times k}$  is a generating matrix of C if

$$C = \left\{ Mz \mid z \in \mathbb{F}_q^k \right\}.$$

Generating matrices are quite useful, as they succinctly represent a code (which consists of many codewords). Also, one can view them as "encoding algorithms"; namely, if we have some message  $z \in \mathbb{F}_q^k$  that we wish to send over a noisy channel and we want to make it more robust against the noise, we can compute x = Mz and send it instead.

One of the primary goals of coding theory is to construct codes with "as good parameters as possible", and we have already seen that it is impossible to have both the relative distance and rate to be simultaneously close to 1. Is it at least possible to get them both to be bounded away from 0, though? It turns out that if one is willing to compromise on the alphabet size to be large, it is possible (and in fact not hard).

#### 1.1 The Reed-Solomon Code

Let  $d \in \mathbb{N}$  be a parameter, take  $q \geqslant n$ , and take distinct points  $a_1, \ldots, a_n \in \mathbb{F}_q$ . The Reed-Solomon code of degree d over points  $a_1, \ldots, a_n$  is defined as

$$\mathsf{RS}_{d,a_1,\dots,a_n,q} = \left\{ \left. (f(a_1),\dots,f(a_n)) \mid f \colon \mathbb{F}_q \to \mathbb{F}_q \text{ is a polynomial of degree at most } d \right\}.$$

In other words, for each function  $f \colon \mathbb{F}_q \to \mathbb{F}_q$  of the form  $f(x) = \sum_{i=0}^d \alpha_i x^i$  we have a word in  $\mathsf{RS}_{d,a_1,\dots,a_n,q}$ , which is the vector of evaluations of it on the points  $a_1,\dots,a_n$ . Often times, we will have q=n in which case  $\mathbb{F}_q = \{a_1,\dots,a_n\}$ .

Next, we calculate the parameters of  $\mathsf{RS}_{d,a_1,\dots,a_n,q}$ . Clearly, the block length of the code is n, and the alphabet size is q. As for the rate, we have that the number of polynomials of degree at most d is  $q^{d+1}$  since we have q options to choose each one of the coefficients, hence the rate of the code is  $R(\mathsf{RS}_{d,a_1,\dots,a_n,q}) = \frac{\log(q^{d+1})}{\log(q^n)} = \frac{d+1}{n}$ . Therefore, if we want the rate to be constant, we need to take d to be linear in n. Finally, for the distance of the code, by Claim 1.2 it suffices to bound the number of roots a non identity

Finally, for the distance of the code, by Claim 1.2 it suffices to bound the number of roots a non identically 0, univariate polynomial of degree at most d has. The fundamental theorem of algebra tells us that this is at most d, so  $d(\mathsf{RS}_{d,a_1,\dots,a_n,q}) = n - d$  and so  $d_{\mathsf{relative}}(\mathsf{RS}_{d,a_1,\dots,a_n,q}) = \frac{n-d}{n} = 1 - \frac{d}{n}$ . Hence, the code  $\mathsf{RS}_{d,a_1,\dots,a_n,q}$  is an  $(n,1-\frac{d}{n},\frac{d+1}{n},q)$  code, for  $q\geqslant n$ . We see that taking d=n/2 for example, we get that both the rate and the relative distance are constant,

We see that taking d=n/2 for example, we get that both the rate and the relative distance are constant, which is great! However, as we are forced to have at least n points in our field, the alphabet size we get is quite large. Can we shrink the alphabet size somehow, and (ideally) construct an error correcting code over bits  $\{0,1\}$  with constant relative distance and rate?

Later on in the course we will see an analogous situation, wherein without too much work we will able to construct PCPs for which the gap between the completeness and soundness is large (analogously to the distance of the code above), but the alphabet size grows as a result of this operation. We will want to shrink the alphabet size. It is worth noting that in PCPs, the rate parameter is analogous to the size of the PCPs, and there it will be less important for us that it is constant (this would correspond to linear size PCPs, and we will only aim at polynomial size PCPs).

### 1.2 Composition of Codes

To answer this question, in this section we present the technique of code concatenation/ composition. In the coding theory literature, this operation is known as concatenation, but we think that the word composition makes more sense and will henceforth use this terminology.

Suppose we have two codes  $C_1, C_2$  which are  $(n_1, d_1, r_1, q_1)$  and  $(n_2, d_2, r_2, q_2)$  codes. Further suppose that the number of codewords in  $C_2$  is at least the alphabet size of  $C_1$ , i.e.  $|C_2| \geqslant q_1$ . In this situation, we can construct a composed code  $C_1 \circ C_2$ , as follows. Fix some injective map  $M : \mathbb{F}_{q_1} \to C_2$ ; that is, for each alphabet symbol  $\sigma$  of  $C_1$  choose some distinct codeword  $c_2 \in C_2$ , and map  $M\sigma = c_2$ . The idea in the composed code  $C_1 \circ C_2$  then is to take each codeword in  $C_1$  and replace each symbol in it with its corresponding codeword in  $C_2$ . Namely, the composed code is

$$C_1 \circ C_2 = \{ (M(x_1), \dots, M(x_{n_1})) \mid (x_1, \dots, x_n) \in C_1 \}.$$

Next, we calculate the parameters of this code. Note that the block length is  $n_1 \cdot n_2$ , the alphabet is  $\mathbb{F}_{q_2}$ , and number of codewords in  $C_1 \circ C_2$  is the same as the number of codewords in  $C_1$  so

$$R(C_1 \circ C_2) = \frac{\log(|C_1|)}{\log(q_2^{n_1 n_2})} = \frac{\log(q_1^{n_1})R(C_1)}{\log(q_2^{n_1 n_2})} = R(C_1)\frac{\log(q_1)}{\log(q_2^{n_2})} = R(C_1)R(C_2),$$

where the last transition holds if  $q_1 = |C_2|$ .

As for the distance, if we take distinct  $(x_1, \ldots, x_n) \in C_1$  and  $(y_1, \ldots, y_n) \in C_1$ , then there are at least  $d(C_1)$  indices i such that  $x_i \neq y_i$ , and then  $M(x_i)$  and  $M(y_i)$  will be different in at least  $d(C_2)$  locations. Thus,  $d(C) \geqslant d(C_1)d(C_2)$ , and so  $d_{\text{relative}}(C) \geqslant d_{\text{relative}}(C_1)d_{\text{relative}}(C_2)$ .

Summarizing, the code  $C_1 \circ C_2$  is an  $(n_1n_2, d_1d_2, r_1r_2, q_2)$  code. This means that if the relative distances and rates of both  $C_1$  and  $C_2$  are constant, then the same holds for the composed code (albeit with a somewhat worse constant); furthermore the alphabet of  $C_1 \circ C_2$  is inherited from the code  $C_2$ , which is potentially much smaller than that of  $C_1$ .

We also remark that if the map M is itself a linear map, then  $C_1 \circ C_2$  is also a linear code, hence the composition operation works well with respect to linearity of codes. Composition also enjoys other properties that we will explore later on in the course.

**Example.** While simple, this operation is very powerful, and we will next see how to use the Reed-Solomon code with itself to get codes with constant rate and distance and smaller alphabet size. Indeed, take  $C_1 = \mathsf{RS}_{d,a_1,\dots,a_n,q}$  for q = n and d = n/2 which is a (n,1/2,1/2,n) code, and  $C_2 = \mathsf{RS}_{d',a'_1,\dots,a'_{n'},q'}$  for  $n' = q' = \log n$ , d' = q'/2 which is a  $(\log n,1/2,1/2,\log n)$  code that has at least  $(q')^{d'} > n$  codewords. Hence, we may compose these codes and get an  $(n\log n,\frac{1}{4},\frac{1}{4},\log n)$  code. We can in fact repeat this idea a few more items; for example, doing it once more yields an  $(n\log n\log\log n,\frac{1}{8},\frac{1}{8},\log\log n)$  code, so we can shrink the alphabet to be very small.

This idea alone would never really bring us down to a constant size alphabet. However, once the alphabet size is small enough  $(q = \log \log n \text{ will do})$ , one can just find a binary code with constant rate and relative distance by brute force. Indeed, if we take  $n' = K \log q$  for a large absolute constant K, we can construct a code  $C \subseteq \mathbb{F}_2^{n'}$  by going over all vectors  $x \in \mathbb{F}_2^{n'}$  and at each time, adding x to C if doing so would not decrease the relative distance of C below 0.01. The running time of this is  $2^{O(n')} < \text{poly}(n)$ , and clearly when the process terminates we get a code C with relative distance at least 0.01. Next, we argue that C also has a constant rate. Indeed, when the process ends, for each  $x \in \mathbb{F}_2^{n'}$ , the ball  $B_x = \left\{z \in \mathbb{F}_2^{n'} \,\middle|\, \Delta(x,z) \leqslant 0.01n'\right\}$  contains some point from C (otherwise we could add x to C). Thus, letting B be any one of these balls, we have

$$|C| \geqslant \frac{2^{n'}}{|B|} \geqslant \frac{2^{n'}}{\binom{n}{0.01n'}} \geqslant (3/2)^{n'},$$

so 
$$R(C) \geqslant \frac{n' \log(3/2)}{n' \log 2} \geqslant \Omega(1)$$
.

Thus, we can take C to be this code achieving parameters  $(100 \log \log \log n, \Omega(1), \Omega(1), 2)$ , and C' to be the composed Reed-Solomon code achieving parameters  $(n \log n \log \log n, \Omega(1), \Omega(1), \log \log n)$ , and compose them to get an  $(n \log n \log \log n \log \log n, \Omega(1), \Omega(1), 2)$  code. Thus, we indeed get a code achieving Boolean alphabet while simultaneously having constant rate and relative distance!

So, can we just construct PCPs using these codes and be done? Well, it turns out that for the purpose of PCPs, one needs more than just constant size alphabet, constant relative distance and good rate. Indeed, in PCPs, the "proof" or "witness" that the verifier looks at will hopefully be a codeword of some code. By hopefully, we mean that this is the legitimate form of witness that we will have in mind while constructing the PCP. As is always the case though, we will need to consider any other, potentially malicious witnesses, be able to detect that they are not of the "legitimate form", and thus reject them. On top of that, our PCP verifier can only look at a few locations in the witness altogether. Thus, our code C must have the functionality that membership of a given word w in it can be tested by looking only at a few coordinates of w. This motivates the notion of local testability of codes, that we define next.

## 1.3 Locally Testable Codes

Informally, a locally testable code  $C \subseteq \mathbb{F}_q^n$  is a code that is accompanied with a randomized tester T, which is supposed to check whether a given word  $w \in \mathbb{F}_q^n$  is in C or not. Additionally, we want the tester T to be local, in the sense that it only looks at a few locations of w in order to determine if  $w \in C$  or not.

Clearly, trying to distinguish between the case that  $w \in C$  and  $w \notin C$  using only a local tester is impossible. Indeed, if  $w \notin C$  but w agrees with some codeword  $c \in C$  on all but a single coordinate, the tester T would have hard time distinguishing between w and c. Thus, we relax the requirement from the tester T, and only ask it to distinguish between the case that  $w \in C$ , and the case that w is far from all codewords in C.

**Definition 1.3.** For an error correcting code  $C \subseteq \mathbb{F}_q^n$  and  $h \in \mathbb{N}$ ,  $\varepsilon, \delta > 0$  (which may be a function of the parameters of the code), an  $(h, \varepsilon, \delta)$ -local tester for T is a randomized algorithm that is given an oracle access to an input  $w \in \mathbb{F}_q^n$  and has the following properties:

- 1. T makes at most h oracle accesses to w.
- 2. If  $w \in C$ , then T accepts with probability 1.
- 3. If  $\Delta(w,C) := \min_{c \in C} \Delta(w,c) \geqslant \varepsilon n$ , then T rejects with probability at least  $\delta$ .

Definition 1.3 is indeed a very natural notion to consider and a lot of effort in coding theory has gone into investigating locally testable codes. For now though, it is not even clear if locally testable codes exist, and in the rest of this lecture we will see a few examples of algebraic codes that are locally testable.

## 1.4 Local Testability of the Reed-Solomon Code

We begin by examining the Reed-Solomon codes that we already defined, and show a "local" tester for them. To motivate this tester, we begin with the following observation.

**Claim 1.4.** Let  $d, q \in \mathbb{N}$ . For all distinct  $a_0, \ldots, a_{d+1} \in \mathbb{F}_q$  there are  $\alpha_0, \ldots, \alpha_{d+1} \neq 0$ , such that

1. If 
$$f: \mathbb{F}_q \to \mathbb{F}_q$$
 has degree at most  $d$ , then  $\sum_{i=0}^{d+1} \alpha_i f(a_i) = 0$ .

2. If 
$$f: \mathbb{F}_q \to \mathbb{F}_q$$
 is not of degree  $d$ , then for some  $a_1, \ldots, a_{d+1}$  we have  $\sum_{i=0}^{d+1} \alpha_i f(a_i) \neq 0$ .

*Proof.* To get a feel for what the claim, note that if we look at  $f(a_0), \ldots, f(a_d)$ , then there is a unique degree d polynomial g such that  $g(a_i) = f(a_i)$  (interpolation), hence if f is a degree d polynomial the value of it in  $a_{d+1}$  must be equal to  $g(a_{d+1})$ . In other words, d values of f determine the last one. The additional information given to us by the claim is that this deduction can be in fact be phrased as a linear equation in  $f(a_0), \ldots, f(a_{d+1})$ .

To establish the first item, consider the matrix  $M \in \mathbb{F}_q^{(d+1)\times(d+2)}$  whose i,j entry is  $a_j^i$ . Then M has rank d+1, so the system of equations  $M(\alpha_0,\ldots,\alpha_{d+1})=0$  has a non-trivial solution, and it is easily seen that these  $\alpha$ 's satisfy the first item of the claim.

<sup>&</sup>lt;sup>1</sup>The reason we have put the word "local" in quotation marks is that while this local tester achieves a non-trivial testing result, it will not be useful for us in the context of PCPs.

For the second item, we prove the counter-positive. Namely, we assume that f satisfies the equality for all  $a_0, \ldots, a_{d+1}$ , and prove that f is a polynomial of degree at most d. Take any  $a_0, \ldots, a_d$ , and define a polynomial h of degree d such that  $h(a_i) = f(a_i)$ . We claim that  $h \equiv f$ . Indeed, taking any other  $a_{d+1}$  we find that

$$\sum_{i=0}^{d+1} \alpha_i f(a_i) = 0 = \sum_{i=0}^{d+1} \alpha_i h(a_i),$$

where the first equality is by assumption and the second equality is by the first item. Thus, simplifying we get that  $h(a_{d+1}) = f(a_{d+1})$ , and we are done.

A slightly annoying feature of this claim is that the coefficients  $\alpha$  depend on points we chose  $a_0, \ldots, a_{d+1}$ , and circumvent that we consider a special type of (d+2)-tuples of points for which this is not the case, which are tuples that form an arithmetic progression.

**Claim 1.5.** Let  $d, q \in \mathbb{N}$ . For  $x, h \in \mathbb{F}_q$  we have that for  $\alpha_i = \binom{d+1}{i}(-1)^i$ ,

1. If 
$$f: \mathbb{F}_q \to \mathbb{F}_q$$
 has degree at most  $d$ , then  $\sum_{i=0}^{d+1} \alpha_i f(x+ih) = 0$ .

2. If 
$$f: \mathbb{F}_q \to \mathbb{F}_q$$
 is not of degree  $d$ , then for some  $x, h$  we have that  $\sum_{i=0}^{d+1} \alpha_i f(x+ih) \neq 0$ .

*Proof.* Essentially the same proof as in the previous section, where one checks that the solution to the linear system of equations is  $\alpha_i = \binom{d+1}{i}(-1)^i$  for  $i = 0, 1, \dots, d+1$ .

Given oracle accept to some  $f: \mathbb{F}_q \to \mathbb{F}_q$  and some parameter  $d \in \mathbb{N}$ , Claim 1.5 suggests a local tester T: choose  $x, h \in \mathbb{F}_q$  uniformly and independently, and check that  $\sum_{i=0}^{d+1} \alpha_i f(x+ih) = 0$ .

**Theorem 1.6.** The local tester T is an  $(d+2,2\delta,\delta)$  tester for  $RS_{d,n,q}$  for all  $\delta < \frac{1}{4(d+1)^2}$ .

The rest of this section is devoted to the proof of Theorem 1.6. First, it is clear that if f is a degree d polynomial, then the tester always accepts. As for the soundness of the test, we prove it counter-positively: assuming that the tester T accepts with probability at least  $1-\delta$ , we show that f is close to a degree d polynomial. For this, for each  $x \in \mathbb{F}_q$  consider a random choice of  $h \in \mathbb{F}_q$ , and then executing the test on  $x, x + h, \ldots, x + (d+1)h$ . Then we know that with probability  $\geq 1 - \delta$ , we have that

$$\sum_{i=1}^{d+1} \alpha_i f(x+ih) + \alpha_0 f(x) = 0,$$

so  $f(x) = -\sum_{i=1}^{d+1} \frac{\alpha_i}{\alpha_0} f(x+ih)$ . This tells us that the value of  $-\sum_{i=1}^{d+1} \frac{\alpha_i}{\alpha_0} f(x+ih)$  doesn't really depend on the choice of h but rather only on x (at least with high probability), and thus one is motivated to define

$$g(x) = \mathsf{plurality}_{h \in \mathbb{F}_q} \left( -\sum_{i=1}^{d+1} \frac{\alpha_i}{\alpha_0} f(x+ih) \right).$$

First, we show that  $\Delta(f,g) \leqslant 2\delta n$ . Indeed,  $f(x) = -\sum_{i=1}^d \frac{\alpha_i}{\alpha_0} f(x+ih)$  with probability at least  $1-\delta$ , hence with probability at least  $1-2\delta$  over x, we have that if we fix x, then over the choice of h we have  $f(x) = -\sum_{i=1}^{d+1} \frac{\alpha_i}{\alpha_0} f(x+ih)$  with probability at least  $\frac{1}{2}$ , in which case f(x) = g(x).

Second, we show that g is a degree d polynomial. For that, we show that for each x, the plurality in the definition of x is actually achieved overwhelmingly, and more precisely that:

**Claim 1.7.** For all  $x \in \mathbb{F}_q$  we have

$$\Pr_{h_1, h_2 \in \mathbb{F}_q} \left[ \sum_{i=1}^{d+1} \frac{\alpha_i}{\alpha_0} f(x+ih_1) = \sum_{i=1}^{d+1} \frac{\alpha_i}{\alpha_0} f(x+ih_2) \right] \geqslant 1 - 2(d+1)\delta.$$

*Proof.* Choose  $h_1$  and  $h_2$  randomly, and note that for each  $j \neq 0$ , with probability at least  $1 - \delta$  we have

$$\sum_{i=0}^{d+1} \alpha_i f(x + jh_2 + ih_1) = 0.$$

Multiplying by  $\alpha_j$  and summing up all of these equations for  $j=1,\ldots,d+1$ , we get from the Union Bound that with probability at least  $1-(d+1)\delta$ 

$$\sum_{i=0}^{d+1} \alpha_i \sum_{j=1}^{d+1} \alpha_j f(x+jh_2+ih_1) = 0.$$
 (1)

Similarly, for all  $i \neq 0$  we have that

$$\sum_{j=0}^{d+1} \alpha_j f(x + ih_1 + jh_2) = 0,$$

implying that  $\sum_{j=1}^{d+1} \alpha_j f(x+ih_1+jh_2) = -\alpha_0 f(x+ih_1)$  with probability at least  $1-\delta$ . Therefore by the Union we get that with probability at least  $1-2(d+1)\delta$  we may plug this into (1) and get that

$$0 = \sum_{i=0}^{d+1} \alpha_i \sum_{j=1}^{d+1} \alpha_j f(x+jh_2+ih_1) = \alpha_0 \sum_{j=1}^{d+1} \alpha_j f(x+jh_2+0 \cdot h_1) + \sum_{i=1}^{d+1} \alpha_i \cdot (-\alpha_0 f(x+0 \cdot h_2+ih_1)),$$

so 
$$\sum_{j=1}^{d+1} \alpha_j f(x+jh_2) = \sum_{i=1}^{d+1} \alpha_i f(x+ih_1)$$
, finishing the proof.

We can now show that g has degree at most d. The idea is to show that g passes all of the tests, and thereby conclude it is degree d by the second item of Claim 1.5. Take any  $x,h \in \mathbb{F}_q$ ; we want to show that  $\sum_{i=0}^{d+1} \alpha_i g(x+ih) = 0$ , and to show that we will introduce two random variables  $h_1, h_2$  that will be used to randomize the starting point of the test x and the direction of the test h. Using them, we will reduce  $\sum_{i=0}^{d+1} \alpha_i g(x+ih) = 0$  to showing that a collection of  $O(d^2)$  random tests of f pass.

**Claim 1.8.** If  $\delta < \frac{1}{4(d+1)^2}$ , then g has degree at most d.

*Proof.* In more detail, fix x, h and take  $h_1, h_2 \in \mathbb{F}_q$  randomly; then by Claim 1.7 for each  $i = 0, \dots, d$  we have that

$$g(x+ih) = -\sum_{i_1=1}^{d+1} \frac{\alpha_{i_1}}{\alpha_0} f(x+ih+i_1h_1)$$
 (2)

with probability at least  $1 - 2(d+1)\delta$ . Also, for all  $i_1 \neq 0$  and  $i \neq 0$  we have that  $\sum_{i_2=0}^{d+1} \alpha_{i_2} f(x+ih+i_1h_1+i_2ih_2) = 0$ , with probability at least  $1-\delta$ , hence by the Union Bound we get that with probability at least  $1-3(d+1)\delta$  we have

$$g(x+ih) = \sum_{i_1=1}^{d+1} \sum_{i_2=1}^{d+1} \frac{\alpha_{i_1}\alpha_{i_2}}{\alpha_0^2} f(x+i(h+i_2h_2)+i_1h_1)$$
(3)

for all  $i \neq 0$ . For i = 0, the right hand side is

$$\sum_{i_1=1}^{d+1} \sum_{i_2=1}^{d+1} \frac{\alpha_{i_1} \alpha_{i_2}}{\alpha_0^2} f(x+i_1 h_1) = -\sum_{i_2=1}^{d+1} \frac{\alpha_{i_2}}{\alpha_0} g(x) = g(x)$$

where in the first equality we used (2), and in the second one we used  $\sum_{i_2=0}^{d+1} \frac{\alpha_{i_2}}{\alpha_0} = 0$  (which holds by choice of  $\alpha$  by choosing the constant 1 function). Thus, for each i, (3) holds with probability at least  $1 - 3(d+1)\delta$ .

We expressed g(x+ih) for fixed x, h as a linear combination of the values of f at points of the form y+h' where y and h' are jointly uniform over  $\mathbb{F}_q$ . This will allow us to use the fact that the tester passes with high probability in order to analyze the sum of g(x+ih) over i.

To be more specific, using the Union bound, the probability (3) holds for all  $i=0,\ldots,d+1$  is at least  $1-3(d+1)^2\delta$ , and multiplying by  $\alpha_i$  and summing gives that

$$\sum_{i=0}^{d+1} \alpha_i g(x+ih) = \sum_{i_1=1}^{d+1} \sum_{i_2=1}^{d+1} \frac{\alpha_{i_1} \alpha_{i_2}}{\alpha_0^2} \sum_{i=0}^{d+1} \alpha_i f(x+i(h+i_2h_2)+i_1h_1) = 0,$$

where the last equality holds with probability  $1-(d+1)^2\delta$ , since it can be viewed as the test applied on  $x'=x+i_1h_1$  on  $h'=h+i_2h_2$ , which are distributed independently in  $\mathbb{F}_q$ . For each  $i_1,i_2\neq 0$ , the points  $x+i_1h_1$  and  $h+i_2h_2$  are jointly uniform from  $\mathbb{F}_q$ , hence  $\sum\limits_{i=0}^{d+1}\alpha_if(x+i(h+i_2h_2)+i_1h_1)=0$  with probability at least  $1-\delta$ . We get by the Union Bound that  $\sum\limits_{i=0}^{d+1}\alpha_ig(x+ih)=0$  with probability at least  $1-4(d+1)^2\delta>0$ , and since this an event that does not depend on  $h_1,h_2$ , we get that  $\sum\limits_{i=0}^{d+1}\alpha_ig(x+ih)=0$ .

#### 1.5 The Reed-Muller and Hadamard Codes

Returning to the discussion in the end of Section 1.2, we argued there that for the PCP application we must be using codes which are locally testable. In the previous section, we saw that Reed-Solomon codes are somewhat locally testable; here, we say "somewhat" because the locality of the tester is  $\approx d$ , whereas for

the code to be useful at all for us, we need to take fairly large d (say  $d = \Omega(n)$ ), which makes the local testability result we proved not very useful.

Secondly, in the end of the argument once the alphabet size of the composed code is small enough, we used a code found by a brute-force argument with constant rate, relative distance and Boolean alphabet; in the PCP application we will need to replace that code with a code that has local testability.

To resolve these issues, we will introduce two more basic families of codes: the Reed-Muller codes and the Hadamard Codes.

#### 1.6 The Reed-Muller Codes

The Reed-Muller codes are the multi-variate analogs of the Reed-Solomon codes. Here, we again have a field  $\mathbb{F}_q$ , a degree parameter  $d \in \mathbb{N}$ , and a parameter  $m \in \mathbb{N}$  which is the number of variables our polynomials have. In these notations, the Reed-Muller code is

$$\mathsf{RM}_{m,d,q} = \left\{ \, (f(v))_{v \in \mathbb{F}_q^m} \, \left| \, f \colon \mathbb{F}_q^m \to \mathbb{F}_q \text{ has total degree at most } d \right. \right\}.$$

Here, the total degree of a monomial  $x_1^{i_1}\cdots x_m^{i_m}$  is  $i_1+\ldots+i_m$ , and the total degree of a polynomial f is the maximum of the total degree over all monomials that appear in f. Thus, for every function  $f:\mathbb{F}_q^m\to\mathbb{F}_q$  of the form

$$f(x_1, ..., x_m) = \sum_{\vec{i}: i_1 + ... + i_m \leq d} c_{\vec{i}} x_1^{i_1} \cdots x_m^{i_m},$$

we have a corresponding codeword  $(f(v))_{v\in\mathbb{F}_q^m}$  in  $\mathsf{RM}_{m,d,q}.$ 

It is easy to show that the Reed-Muller code is a linear error correcting code, and one can analyze the parameters of it. For example, if  $q \geqslant d$ , then the rate of  $\mathsf{RM}_{m,d,q}$  is  $\frac{\binom{m+d}{m}}{q^m}$ , and the relative distance is at least  $1 - \frac{d}{q}$ . You will establish some of its properties in the problem set.

So far, it appears that Reed-Muller codes are worse than Reed-Solomon codes, at least with respect to the rate that they offer (they do have a decent distance though if q is much larger than d). However, Reed-Muller codes have far better local testability properties compared to Reed-Solomon codes. In Reed-Solomon, to perform local testing we had to essentially read a constant fraction of the given function. In Reed-Muller, we can do much better; this will be the focus of discussion at a later point in the course, and for now we briefly explain the extra versatility afforded to us by using Reed-Muller codes.

One idea that becomes available to us when looking at multivariate polynomials, is restrictions. Indeed, suppose we have a polynomial  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  of total degree at most d, and consider a line, namely a function  $\ell \colon \mathbb{F}_q \to \mathbb{F}_q^m$  of the form  $\ell(t) = a + tb$  for some  $a, b \in \mathbb{F}_q^m$ . Then we can consider the restriction of f to the line, i.e. the function  $f|_{\ell}(t) = f(\ell(t))$ , and note that this function is a univariate polynomial in t of degree at most d. Thus, we can use local testing ideas from the Reed-Solomon code in order to perform local testing on g, and that will cost us O(d) queries. Thus, it stands to reason that if we want to test if f is degree d or far from it, we could try to pick a random line  $\ell$ , and perform the local tester of Reed-Solomon on  $f|_{\ell}$ . Indeed, there are ideas in this spirit that work (though are more difficult to prove), and we will see it in the future.

So what did we gain from this? Well, in the basic set-up of Reed-Solomon, the amount of information that a polynomial of degree d encodes is d+1 symbols from  $\mathbb{F}_q$  (that is, its coefficients), and we needed to invest d+2 queries to locally test. In the Reed-Muller code, we could have stored much more information – roughly  $\binom{m+d}{m}$  many symbols from  $\mathbb{F}_q$ , and the locality of the local tester does not change much. This is one of the main features that makes Reed-Muller so useful in the context of PCP.

#### 1.7 The Hadamard Codes

The final family of codes we present is the family of Hadamard codes. This family is specified by a parameter  $n \in \mathbb{N}$ . For a vector  $v \in \mathbb{F}_2^n$ , we define  $\chi_v \colon \mathbb{F}_2^n \to \mathbb{F}_2$  as  $\chi_v(x) = \langle x, v \rangle$ , and then define the Hadamard as

$$H_n = \left\{ (\chi_v(x))_{x \in \mathbb{F}_2^n} \mid v \in \mathbb{F}_2^n \right\}.$$

As you will see in the problem set,  $H_n$  has relative distance 1/2 (which is good), relative rate  $\frac{n}{2^n}$  (which is not very good; we will only use it when n is already small) and alphabet size 2. One additional important feature of  $H_n$  is that it is locally testable:

**Theorem 1.9.**  $H_n$  is  $(3, 2\varepsilon, \varepsilon)$  locally testable for  $\varepsilon < \frac{1}{8}$ .

*Proof.* Consider the following tester T: given oracle access to a function  $f: \mathbb{F}_2^n \to \mathbb{F}_2$ , choose  $x, y \in \mathbb{F}_2^n$  uniformly and independently, query f(x), f(y) and f(x+y) and check that f(x+y) = f(x) + f(y); here,  $(x+y)_i = x_i + y_i$ . Then it is clear that the locality of the tester is 3, and that if  $f = \chi_v$  for some  $v \in \mathbb{F}_2^n$ , then the tester succeeds with probability 1 as

$$\chi_v(x+y) = \langle x+y, v \rangle = \langle x, v \rangle + \langle y, v \rangle = \chi_v(x) + \chi_v(y).$$

Next, we prove that if f is  $2\varepsilon$  far from  $H_n$ , then T rejects with probability at least  $\varepsilon$ . We prove that counter-positively; namely, assuming that T rejects with probability less than  $\varepsilon$ , we show that f is close to some  $\chi_v$ . Indeed, define  $g: \mathbb{F}_2^n \to \mathbb{F}_2$  by

$$g(x) = \mathsf{majority}_{y \in \mathbb{F}_2^n} \left( f(x+y) - f(y) \right).$$

We first claim that  $\Delta(f,g) \leq 2\varepsilon 2^n$ . Indeed, since f(x) + f(y) = f(x+y) with probability at least  $1 - \varepsilon$ , we have that for all but  $1 - 2\varepsilon$  of the x's, it holds that  $\Pr_y[f(x) = f(x+y) - f(y)] \geq \frac{1}{2}$ , in which case f(x) = g(x).

Second, we claim that  $g = \chi_v$  for some  $v \in \mathbb{F}_2^n$ , and for that we show that g(x) + g(z) = g(x+z) for all  $x, z \in \mathbb{F}_2^n$ . Towards this end, we argue that for all x, the majority in the definition of g(x) is attained:

**Claim 1.10.** For all 
$$x \in \mathbb{F}_2^n$$
 we have  $\Pr_{y_1,y_2 \in \mathbb{F}_2^n} [f(x+y_1) - f(y_1) = f(x+y_2) - f(y_2)] \geqslant 1 - 2\varepsilon$ .

*Proof.* With probability  $1-\varepsilon$  we have that  $f(y_1)+f(y_2)=f(y_1+y_2)$ , and with probability  $1-\varepsilon$  we have that  $f(x+y_1)+f(x+y_2)=f(x+y_1+x+y_2)=f(y_1+y_2)$ , hence with probability  $1-2\varepsilon$  we have that  $f(x+y_1)+f(x+y_2)=f(y_1)+f(y_2)$ . Since  $f(y_1)+f(y_2)=f(y_1)-f(y_2)$  and  $f(x+y_1)+f(x+y_2)=f(x+y_1)-f(x+y_2)$ , the result follows.

The proof now quickly follows. Fix  $x, z \in \mathbb{F}_2^n$  and take  $y_1, y_2 \in \mathbb{F}_2^n$  randomly; then by Claim 1.10 with probability at least  $1 - 6\varepsilon$  we have

$$g(x) = f(x+y_1) - f(y_1),$$
  $g(z) = f(z+y_2) - f(y_2),$   $g(x+z) = f(x+z+y_1+y_2) - f(y_1+y_2),$ 

$$g(x) + g(z) - g(x+z) = (f(x+y_1) + f(z+y_2) - f(x+z+y_1+y_2)) - (f(y_1) + f(y_2) - f(y_1+y_2)).$$

With probability at least  $1-2\varepsilon$  we have  $f(x+y_1)+f(z+y_2)-f(x+z+y_1+y_2)=0$  and  $f(y_1)+f(y_2)-f(y_1+y_2)=0$ , hence with probability at least  $1-8\varepsilon>0$  we have that g(x)+g(z)-g(x+z); as the last statement does not have any of the y's in it, it follows that g(x)+g(z)-g(x+z)=0 for all x and z.

Taking  $v \in \mathbb{F}_2^n$  by setting  $v_i = g(e_i)$  where  $e_i \in \mathbb{F}_2^n$  is the *i*th elementary basis vector, one can show that  $g(x) = \chi_v(x)$ , and we are done.

## 1.8 Composing Locally Testable Codes?

Having introduced error correcting codes, the composition technique and realizing that we need to use local testing towards PCP, we come to the question of whether our new realization combines well with the composition technique that was so crucial in construction good error correcting codes (and will be just as crucial when proving the PCP theorem).

Thinking about it schematically, suppose that we have  $C_1$  which is an  $(n_1, d_1, r_1, q_1)$  code, and  $C_2$  which is an  $(n_2, d_2, r_2, q_2)$  code, and  $C_1$ ,  $C_2$  are locally testable by the testers  $T_1$  and  $T_2$  that have locality  $t_1$  and  $t_2$  respectively. Is the composed code  $C_1 \circ C_2$  locally testable?

Let  $w \in \mathbb{F}_{q_2}^{n_1 \cdot n_2}$  be a word; how shall we go about testing it locally? A natural idea proceeds as follows: we imagine a "virtual codeword"  $c_1 \in C$  from which w is derived, and then simulate the tester  $T_1$  on it. More precisely:

- 1. Run the tester  $T_1$  in order to choose locations  $i_1, \ldots, i_{t_1} \in [n_1]$  to be read from the "virtual codeword".
- 2. Read off the blocks corresponding to these locations in w, i.e. the blocks that are supposed to have replaced the symbols in locations  $i_1, \ldots, i_t$  in  $c_1$  with codewords from  $C_2$ .
- 3. Decipher from the blocks the corresponding symbol in the original word from  $C_1$  in these locations, and perform the local test  $T_1$  on these values.

There are numerous issues with this scheme. First off, it may be the case that the blocks that we read corresponding to  $i_1, \ldots, i_t$  were erroneous (after all, we care to reject words that are far from the code), in which case the deciphering in the third step would be incorrect and may even fail. In such case, the simulation of  $T_1$  we are trying to perform on a virtual word from  $C_1$  is incorrect.

This motivates the notion of *local decodeability*, a notion that strengthens local testing by requiring us not only to be able to locally test whether a given word is a codeword or far from the code. Instead, if w is close to a codeword c, we are required also to be able to recover any coordinate of c by performing only a few oracle access calls to w.

Another (related) issue that we point out now (but will only appear later on) is that sometimes, we will really be interested in some special coordinates i of c which are not "random looking", while only having access to a word w which is only guaranteed to be close to c. In particular, it may be the case that for this specific type of i's we always have that  $w_i \neq c_i$ . This motivates the idea of random self-reducibility that we have actually already seen a few times). This idea says that given a coordinate i, we can choose a few coordinates  $j_1, \ldots, j_\ell$  so that marginally each one of them is distributed uniformly over [n], and yet they are correlated in a way that if we know  $c_{j_1}, \ldots, c_{j_\ell}$  we can also recover  $c_i$ . For example, in the Hadamard code, if we had some f that is close to  $\chi_v$ , and a special point  $x^* \in \mathbb{F}_2^n$  that we really cared about and wanted to know  $\chi_v(x^*)$ , we could proceed as follows. Sample  $y \in \mathbb{F}_2^n$  uniformly, ask for f(y) and  $f(y+x^*)$  (where we note that marginally each one of y and  $y+x^*$  is distributed uniformly over  $\mathbb{F}_2^n$ ), and output  $f(y+x^*)-f(y)$ . It is easily seen that if f and  $\chi_v$  are close, then the output is  $\chi_v(x^*)$  with high probability.

## 2 Upcoming Lectures

Starting from the next lecture, we will see analogous ideas to the ones presented herein and are used in the algebraic proof of the PCP theorem. There are several ingredients that need to be combined well together to make the proof go through, and each one of the steps requires more time and attention.

We will first show a PCP construction achieving great completeness and soundness, albeit with a large alphabet size (analogous to the Reed-Solomon code). Following that, we will spend a few lectures on the sum-check protocol and the low-degree test (local testing for Reed-Muller), which together realize the idea of composition introduced in this lecture, and achieve an alphabet size reduction. We will need to apply this step twice, and for that we will spend a few more lectures introducing a few more ideas, most notably the block property and aggregation of queries. Finally, we will be in a position to apply the Hadamard-based PCP to finish off the proof.

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lectures 4,5,6

#### Dor Minzer

In this lecture we make the first step in the proof of the PCP theorem, and establish seemingly strong inapproximability result for solving quadratic equations. This construction though will not be local at all (each one will involve all of the variables), and we will turn our attention into improving upon the locality of the construction. Towards this end, we will present the sum-check protocol and low-degree extensions.

### 1 Quadratic Solvability

**Definition 1.1** (Quadratic-Solvability over  $\mathbb{F}_q$  with locality r). For a field  $\mathbb{F}_q$  and  $r \in \mathbb{N}$ , an instance of  $QS_{q,r}$  consists of a set of variables  $X = \{x_1, \ldots, x_n\}$  and a set of equations  $E = \{e_1, \ldots, e_m\}$ , where each equation  $e \in E$  is a quadratic equation in the X's involving at most r of the variables.

Given an instance of  $QS_{q,r}$ , the goal is to find an assignment to the variables, namely  $A \colon X \to \mathbb{F}_q$ , that satisfies as many of the equations as possible.

For example, the following (X, E) is an instance of  $QS_{q,r}$ : take  $X = \{x_1, \dots, x_n\}$  and the equations  $x_1x_2 + x_3 = 0, x_1^2 - 7x_4x_5 + x_2x_3 = 2.$ 

Abusing notations we denote by  $QS_{q,r}$  the language consisting of all satisfiable instances, namely

$$QS_{q,r} = \{ (X, E) \mid \exists A \colon X \to \mathbb{F}_q \text{ that satisfies all of the equations in } E \}.$$

We also consider the corresponding gap problem,  $QS_{q,r}[c,s]$  for  $0 < s \le c \le 1$ , in which one is given an instance promised to be at least c satisfiable or at most s satisfiable, and the goal is to distinguish between these two cases.

We show that the Quadratic Solvability problem is NP-hard using the classical theory of NP-hardness. Then, we will use ideas from previous lectures, we show that the gap version of Quadratic Solvability is also NP-hard.

#### 1.1 NP-hardness of Quadratic Solvability

First, we show that for some  $r \in \mathbb{N}$  (r = 5 will be enough), the problem  $QS_{q,r}$  is NP-hard for all q. The idea is to start with the NP-hard 3-SAT problem, and arithmetize the clauses as equations.

**Theorem 1.2.** For r = 6 and any field  $\mathbb{F}_q$ , the problem  $QS_{q,r}$  is NP-hard.

*Proof.* We reduce from 3-SAT. Given a 3-CNF formula  $\phi = C_1 \wedge C_2 \wedge \ldots \wedge C_m$ , we construct an instance (X', E') of quadratic solvability as follows. First, for every variable  $x_i$  in  $\phi$  we construct a variable  $x_i'$  in X'. Second, for every pair of variables  $x_i, x_j$  we construct a variable  $x_{i,j}'$  in X'.

We will want the variables  $x'_i$  to be Boolean valued (representing the value of  $x_i$ ), and want the value of  $x'_{i,j}$  to be equal to the value of  $x_ix_j$ . To implement these we add the equations  $x'_i = x'_i^2$  for all i and  $x'_{i,j} = x'_i x'_j$  for all i, j.

Finally, we want to write down an equation that checks whether each clause in  $\phi$  holds. Thus, fix C to be a clause in  $\phi$ , and assume without loss of generality that  $C=(x_1\vee x_2\vee x_3)$ . Note that this can be equivalently written as an equation as  $(1-x_1)(1-x_2)(1-x_3)=0$ , however this would be an equation of degree 3. Instead, we expand the left hand side, and use our  $x'_{i,j}$  variables to express it as a quadratic equation:  $1-x'_1-x'_2-x'_3+x'_{1,2}+x'_{2,3}+x'_{1,3}-x'_{1,2}x'_3=0$ , and we add this equation to E'. We remark that if C has a negation in it, say  $C=(\bar{x}_1\vee x_2\vee x_3)$ , then the same idea works replacing  $x_1$  with  $1-x_1$  (starting with the equation  $x_1(1-x_2)(1-x_3)=0$ ).

**Completeness.** We show that if  $\phi$  is satisfiable, then (X', E') is satisfiable. Indeed, if  $A: \{x_1, \ldots, x_n\} \to \{0, 1\}$  satisfies all clauses in  $\phi$ , then we can define  $B: X' \to \{0, 1\}$  by setting  $B(x_i') = A(x_i)$  and  $B(x_{i,j}') = A(x_i)A(x_j)$ , and observe that then B satisfies all of the equations in (X', E').

**Soundness.** We have to show that if  $\phi$  is unsatisfiable, then (X', E') is unsatisfiable. Equivalently, we show instead that if (X', E') is satisfiable, then  $\phi$  is satisfiable. Towards this end, suppose that  $B: X' \to \mathbb{F}_q$  satisfies all equations. Then in particular it satisfies that  $B(x_i')^2 = B(x_i')$  for all i, hence  $B(x_i') \in \{0, 1\}$ , and as  $B(x_{i,j}') = B(x_i')B(x_j')$  we get that  $B(x_{i,j}') \in \{0, 1\}$  also, hence  $B: X' \to \{0, 1\}$ . We may therefore define  $A: \{x_1, \ldots, x_n\} \to \{0, 1\}$  by  $A(x_i) = B(x_i')$ , and note that since B is Boolean and satisfies the equation associated with each clause of  $\phi$ , it follows that A satisfies all of the clauses of  $\phi$ .

#### 1.2 NP-hardness of Gap Quadratic Solvability

Next, we show that how to use Theorem 1.2 to prove that the gap version of quadratic solvability is also NP-hard. Towards this end we need the following lemma.

**Lemma 1.3.** Let  $m, n \in \mathbb{N}$  and let  $q \ge 4\log(mn)^2$ , s = mnq. One can construct, in polynomial time, a matrix  $M \in \mathbb{F}_q^{s \times m}$  such that the code generated by M has relative distance at least  $1 - \frac{1}{\sqrt{q}}$ .

Proof. Consider the Reed-Solomon codes  $C_1 = \mathrm{RS}_{d=m,q=mn}$  and  $C_2 = \mathrm{RS}_{d=\log(mn),q}$ , and note that the number of codewords in  $C_2$  is at least  $(\log(mn))^{\log(mn)^2} > mn$ , hence we may consider the composed code  $C = C_1 \circ C_2$  which has blocklength s; we do so using an appropriate linear function mapping symbols of  $C_1$  to codewords of  $C_2$ , so that C is a linear code. Take a matrix  $M \in \mathbb{F}_q^{s \times m}$  to be a generating matrix of C. We note that the relative distance of  $C_1$  is 1 - 1/n, and the relative distance of  $C_2$  is  $1 - \log(mn)/q$ , hence the relative distance of C is at least

$$\left(1 - \frac{1}{n}\right) \left(1 - \frac{\log mn}{q}\right) \geqslant 1 - \frac{1}{\sqrt{q}}.$$

With this lemma in hand, we can now deduce from Theorem 1.2 that the gap version of the Quadratic Solvability problem is also NP-hard, albeit with very poor locality parameter. The idea is that, given a system of equations as in Theorem 1.2, one can construct a new system of equations in which each equation is a linear combination of equations from the original system. One can show, for instance, that if we take sufficiently many independently chosen random linear combinations of equations, then a satisfiable system would be mapped to a satisfiable instance, and an unsatisfiable instance would be mapped to a highly unsatisfiable instance. We will see that a pre-determined set of linear combinations that are dictated by the rows of the matrix M constructed in Lemma 1.3 also does the job.

**Theorem 1.4.** For  $q \ge 4\log(mn)^2$ , the problem gap- $QS_{q,n}[1,\frac{1}{\sqrt{q}}]$  is NP-hard. Here, n stands for the number of variables in the system and m stands for the number of equations in the system.

*Proof.* We show a polynomial time reduction from  $QS_{q,6}$  to gap- $QS_{q,r=n}[1,\frac{1}{\sqrt{q}}]$ , which by Theorem 1.2 implies that gap- $QS_{q,n}[1,\frac{1}{\sqrt{q}}]$  is NP-hard. Given an instance (X,E) of  $QS_{q,5}$ , we construct in polynomial time an instance (X',E') of quadratic solvability such that

- 1. If (X, E) is satisfiable, then (X', E') is satisfiable.
- 2. If (X, E) is unsatisfiable, the (X', E') is at most  $\frac{1}{\sqrt{q}}$ -satisfiable.

Towards this end, construct a matrix  $M \in \mathbb{F}_q^{s \times m}$  as in Lemma 1.3 where s = mnq. We define (X', E') by taking X' = X, and associating with each row of M an equation. In words, we think of (X, E) as a system of equations and then take linear combinations of them as indicated by the matrix M. More precisely, writing  $E = \{e_1, \ldots, e_m\}$  and thinking of the equation  $e_j$  as  $f_j(x) = b_j$ , the ith equation in (X', E'), denoted by  $e'_i$ , is given by

$$\sum_{j=1}^{m} M_{i,j} f_j(x) = \sum_{j} M_{i,j} b_j.$$

**Completeness.** Suppose that (X, E) is satisfiable, and let  $A: X \to \mathbb{F}_q$  be a satisfying assignment. Then A satisfies any equation which is the result of linear combination of equations in (X, E), and hence satisfies (X', E').

**Soundness.** Suppose (X, E) is unsatisfiable, and let  $A \colon X' \to \mathbb{F}_q$  be some assignment. Then A does not satisfy all of the equations in (X, E), hence defining the vector  $v \in \mathbb{F}_q^m$  by  $v_j = f_j(A) - b_j$  gives us that v is not the all 0 vector. Hence, Mv is a codeword in the code generated by M which is not identically 0, so by the distance of the code generated by M it follows that  $(Mv)_i \neq 0$  on all but  $\frac{1}{\sqrt{g}}$  fraction of  $i = 1, \dots, s$ .

In other words, for all but  $\frac{1}{\sqrt{q}}$  of i's we have that  $\sum_{j=1}^{m} M_{i,j}(f_j(x) - b_j) \neq 0$ , implying that A satisfies at most  $\frac{1}{\sqrt{q}}$  of the equations in (X', E').

In the proof of Theorem 1.4 we managed to get a gap between the completeness and the soundness case (and quite a large one), however as is clear from the proof, both the alphabet size (the field size) and the number of queries (i.e. the number of variables each equation depends on) are large, and we will want to reduce them.

It is possible to reduce both the locality and the alphabet size to be O(1) straightaway from Theorem 1.4, however this will result in a non polynomial size PCP (in fact exponential), and we will discuss this point later on in the course. Our proof of the PCP theorem will eventually use this idea, however in order to keep the reduction to be poly-time, it is important to first sufficiently reduce the number of queries and alphabet (just as we did in error correcting codes), say to be poly( $\log \log n$ ), and only then use such ideas.

## 2 Query Reduction via the Sum-check Protocol and Low-degree Extensions

We now turn our attention into developing the sum-check protocol, which is the key primitive that facilitates query reduction in algebraic PCP constructions.

Let  $q = \mathsf{poly}(\log(mn))$ , and consider the natural verifier in the setting of  $\mathsf{gap}\text{-}\mathsf{QS}_{q,n}[1,1/\sqrt{q}]$ . Therein, the verifier has oracle access to an assignment  $A \colon \{x_1,\ldots,x_n\} \to \mathbb{F}_q$ , and his task is to verify that many of the equations in the given instance (X,E) are satisfied. For that, the verifier can pick an equation  $e \in E$ 

randomly and check whether A satisfies it or not. The issue with this approach is that the verifier has to read the entire table of values of A to execute this plan, since each equation  $e \in E$  depends on all of the variables of the system. The question is, therefore, how can the verifier check whether an equation of the form

$$\sum_{i=1, j=1}^{n} a_{i,j} x_i x_j + \sum_{i=1}^{n} b_i x_i = c$$

holds, while making less queries to A? This is clearly impossible if the verifier is only given access to A, but it turns out to be possible if the verifier is supplied with additional information!

#### 2.1 The Low-degree Extension

Towards this end, let  $\mathbb{H} \subseteq \mathbb{F}_q$  be a set whose size is to be determined shortly, and let  $m \in \mathbb{N}$  be an integer so that  $|\mathbb{H}|^m = n$ . For this, it suffices to take  $d = |\mathbb{H}| = \log(n)$  and  $m = \frac{\log n}{\log \log n}$ . Thus, we can identify the set of variables [n] with the cube  $\mathbb{H}^m$ , and re-indexing them accordingly the above equation becomes

$$\sum_{\vec{i},\vec{j}\in\mathbb{H}^m} a_{\vec{i},\vec{j}} x_{\vec{i}} \cdot x_{\vec{j}} + \sum_{\vec{i}\in\mathbb{H}^m} b_{\vec{i}} x_{\vec{i}} = c. \tag{1}$$

Thinking of the assignment A now in these notations, we have that  $A : \mathbb{H}^m \to \mathbb{F}_q$ . It is clear that A may be extended to the entire domain  $\mathbb{F}_q^m$  in many ways, however there is one extension, the so-called low-degree extension, which will be of utmost important to us. Roughly speaking, this is the extension of A that as a polynomial has as small as possible individual degrees. To present and prove some of its basic properties, we first introduce two basic facts about low degree polynomials that will be used many times in this course.

We begin with the classical Schwarz-Zippel lemma.

**Lemma 2.1.** Suppose that  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  is a non-identically 0 polynomial of total degree d, and let  $S \subseteq \mathbb{F}_q$ . Then

$$\Pr_{x \in S^m} \left[ f(x) = 0 \right] \leqslant \frac{d}{|S|}.$$

*Proof.* See problem set 1.

We will also need a version of this lemma for individual degrees, as follows.

**Lemma 2.2.** Suppose that  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  is a non-identically 0 polynomial of individual degrees at most r and  $|\mathbb{H}| \geqslant r+1$ . Then there is  $x \in \mathbb{H}^m$  such that  $f(x) \neq 0$ .

*Proof.* The proof is by induction on m. For m=1, this follows from the fundamental theorem of algebra. Assume m>1, and write

$$f(z_1, \dots, z_m) = \sum_{j=0}^r z_m^j f_j(z_1, \dots, z_{m-1}),$$

where for each  $j=0,\ldots,r$ , the function  $f_j\to\mathbb{F}_q^{m-1}\to\mathbb{F}_q$  is a polynomial of individual degrees at most r. Since f is not-identically 0, there is j such that  $f_j\not\equiv 0$ , and by the induction hypothesis we may find a setting  $(x_1,\ldots,x_{m-1})\in\mathbb{H}^{m-1}$  such that  $f_j(x_1,\ldots,x_{m-1})\not\equiv 0$ . Thus, fixing these values the polynomial  $f(x_1,\ldots,x_{m-1},z_m)$  is a univariate polynomial of degree at most r in  $z_m$ , hence by the base case we may find a setting  $z_m=x_m\in\mathbb{H}$  on which it doesn't vanish, and the proof is concluded.

We can now prove the existence and uniqueness of the low degree extension of an assignment.

**Claim 2.3.** For any  $A : \mathbb{H}^m \to \mathbb{F}_q$ , there is a unique  $A_{\text{extension}} : \mathbb{F}_q^m \to \mathbb{F}_q$  such that

- 1.  $A(z) = A_{\mathsf{extension}}(z)$  for all  $z \in \mathbb{H}^m$ .
- 2.  $A_{\text{extension}}$  is a polynomial whose individual degrees are all at most  $|\mathbb{H}| 1$ .

*Proof.* The construction of  $A_{\text{extension}}$  is by interpolation. For each  $z \in \mathbb{H}^m$ , we can define a function  $\ell_z \colon \mathbb{F}_q^m \to \mathbb{F}_q$  of individual degrees at most  $|\mathbb{H}| - 1$  such that  $\text{supp}(\ell_z) \cap \mathbb{H}^m = \{z\}$ . Indeed, one just takes

$$\ell_z(x) = \prod_{i=1}^m \prod_{a \in \mathbb{H} \setminus \{z_i\}} \frac{x_i - a}{z_i - a},$$

and note that  $supp(\ell_z) \cap \mathbb{H}^m = \{z\}$ , that  $\ell_z(z) = 1$  and that the individual degrees of  $\ell_z$  are all  $|\mathbb{H}| - 1$ . We can thus define

$$A_{\rm extension}(x) = \sum_{z \in \mathbb{H}^m} A(z) \ell_z(x),$$

and note that  $A_{\text{extension}}$  has individual degrees at most  $|\mathbb{H}| - 1$  and  $A_{\text{extension}}(z) = A(z)\ell_z(z) = A(z)$  for  $z \in \mathbb{H}^m$ . This proves the existence part of the claim.

For the uniqueness, suppose A' and A'' are two distinct functions satisfying the claim, and consider B = A' - A''. Then B has individual degrees at most  $|\mathbb{H}| - 1$ , and B vanishes on  $\mathbb{H}^m$ , and by Lemma 2.2 it follows that  $B \equiv 0$ .

The function  $A_{\rm extension}$  is often referred to as the low-degree extension of A and it plays a crucial role in the sum-check protocol. Instead of giving the verifier only access to the assignment A, we shall give him access to  $A_{\rm extension}$  in the hope that this will help us in cutting down on the number of queries. Let us remark first that, formally speaking, the verifier is only given oracle access to some assignment  $B \colon \mathbb{F}_q^m \to \mathbb{F}_q$  which is supposed to be the low-degree extension of A. Thus, the verifier will also need to make sure, somehow, that B is indeed a low-degree function; this is where the low-degree testing problem enters the picture. We ignore this issue for now, assuming the verifier is able to ensure that B is a low-degree function, and show how the protocol proceeds then. In upcoming lectures, after developing the low-degree testing machinery, we will remove this assumption.

#### 2.2 The Sum-Check Protocol

We are now going to make use of our low-degree extension  $A_{\text{extension}}$  to verify that the equation

$$\sum_{\vec{i},\vec{j}\in\mathbb{H}^m} a_{i,j} x_{\vec{i}} \cdot x_{\vec{j}} + \sum_{\vec{i}\in\mathbb{H}^m} b_i x_{\vec{i}} = c \tag{2}$$

holds using much fewer queries than n. Towards this end, define the intermediate functions  $f_s \colon \mathbb{H}^{2s} \to \mathbb{F}_q$  for  $s = 0, 1, \ldots, m$  by 1

$$f_{s}(i_{1},\ldots,i_{s},j_{1},\ldots,j_{s}) = \sum_{\substack{\vec{\alpha}\in\mathbb{H}^{m},\alpha_{\ell}=i_{\ell},\\\vec{\beta}\in\mathbb{H}^{m},\beta_{\ell}=j_{\ell}\\\text{for }\ell=1,\ldots,s}} a_{\vec{\alpha},\vec{\beta}}A(\vec{\alpha})\cdot A(\vec{\beta}) + \frac{1}{|\mathbb{H}|^{s}} \sum_{\vec{\alpha}\in\mathbb{H}^{m},\alpha_{\ell}=i_{\ell}\text{ for }\ell=1,\ldots,s} b_{\vec{\alpha}}A(\vec{\alpha}).$$
(3)

<sup>&</sup>lt;sup>1</sup>By  $\frac{1}{\|\mathbb{H}\|^s}$ , we mean the inverse of  $|\mathbb{H}|^s \in \mathbb{F}_q$ .

In words, the function  $f_s$  represents partial sums similar to the ones in (2) in which a prefix of the indices  $\vec{i}$  and  $\vec{j}$  has been fixed to be according to the input of  $f_s$ .

Note that in this language, the equation that we want to verify is that  $f_0 = c$ . Additionally, note that we have, for all s, that

$$f_s(i_1,\ldots,i_s,j_1,\ldots,j_s) = \sum_{i_{s+1},j_{s+1}\in\mathbb{H}} f_{s+1}(i_1,\ldots,i_s,i_{s+1},j_1,\ldots,j_s,j_{s+1}),\tag{4}$$

and that

$$f_m(i_1,\ldots,i_m,j_1,\ldots,j_m) = a_{i_1,\ldots,i_m,j_1,\ldots,j_m} A(i_1,\ldots,i_m) \cdot A(j_1,\ldots,j_m) + b_{i_1,\ldots,i_m} A(i_1,\ldots,i_m).$$
 (5)

Finally, note that the function  $f_m$  is composed only of O(1) entries of A (to be exact, 2).

This suggests a recursive approach: to verify that  $f_0 = c$ , reduce that to verifying  $f_1(i_1, j_1) = c_{i_1, j_1}$  for some  $i_1, j_1$ , further reduce that to  $f_2(i_1, i_2, j_1, j_2) = c_{i_1, i_2, j_1, j_2}$  for some  $i_1, i_2, j_1, j_2$ , and continue until we need to verify some value of  $f_m$ , which can be done by appealing to the table of values A. To carry out this recursion though we need some redundancies, hence we consider the low-degree extensions of each  $f_s$ . Abusing notations, we will refer to the low-degree extension of  $f_s$  by the same notation,  $f_s \colon \mathbb{F}_q^{2s} \to \mathbb{F}_q$ , and we can now present the sum-check protocol.

The inputs to the sum-check protocol are the assignment  $A_0 \colon \mathbb{F}_q^m \to \mathbb{F}_q$  which has individual degrees at most  $|\mathbb{H}|-1$ , as well as functions  $g_{s,\vec{i}',\vec{j}'} \colon \mathbb{F}_q^2 \to \mathbb{F}_q$  for each  $s=1\dots,m$  and  $\vec{i}',\vec{j}' \in \mathbb{F}_q^{s-1}$  of individual degrees at most  $|\mathbb{H}|-1$ . The goal is to verify that  $A_0$  satisfies (1), and the intention is that  $g_{s,\vec{i}',\vec{j}'}$  is the restriction of function  $f_s$  where the first s-1 coordinates of i and of j are set according to  $\vec{i}'$  and  $\vec{j}'$ . We proceed as follows:

- 1. Verify that  $q_0 = c$ , else reject.
- 2. Verify that  $\sum_{h,h'\in\mathbb{H}} g_1(h,h') = g_0$ , else reject.
- 3. Set s = 1.
- 4. While  $s \leq m$ :
  - (a) Choose  $i_s, j_s \in \mathbb{F}_q$  randomly, let  $\vec{i}_s' = (i_1, \dots, i_s)$  and  $\vec{j}_s' = (j_1, \dots, j_s)$ .
  - (b) Verify that  $\sum_{h,h' \in \mathbb{H}} g_{s+1,\vec{i}'_s,\vec{j}'_s}(h,h') = g_{s,\vec{i}'_{s-1},\vec{j}'_{s-1}}(i_s,j_s)$ , else reject.
  - (c) Increase s by 1.
- 5. Verify that<sup>2</sup>

$$g_{m,\vec{i}_{m-1},\vec{j}_{m-1}'}(i_m,j_m) = a_{i_1,\dots,i_m,j_1,\dots,j_m}A_0(i_1,\dots,i_m) \cdot A_0(j_1,\dots,j_m) + b_{i_1,\dots,i_m}A_0(i_1,\dots,i_m),$$

else reject.

Below we prove the correctness of the Sum-check Protocol.

<sup>&</sup>lt;sup>2</sup>We remark that here, the coefficients  $a_{i_1,\ldots,i_m,j_1,\ldots,j_m}$  are the low-degree extension of the original coefficients  $a_{i_1,\ldots,i_m,j_1,\ldots,j_m}$  for  $i_1,\ldots,i_m,j_1,\ldots,j_m\in\mathbb{H}$ . In contrast to the functions  $f_s$  and  $A_{\text{extension}}$ , the verifier is aware of all of the values of these coefficients, hence he can compute the low degree extension.

**Lemma 2.4.** Suppose that  $A_0: \mathbb{F}_q^m \to \mathbb{F}_q$  is a function with individual degrees at most  $|\mathbb{H}| - 1$ , and  $g_{s,\vec{i}',\vec{j}'}: \mathbb{F}_q^2 \to \mathbb{F}_q$  for  $s = 0, \ldots, m, \ \vec{i}', \vec{j}' \in \mathbb{F}_q^{s-1}$  are functions of individual degrees at most  $|\mathbb{H}| - 1$ .

- 1. Completeness: If  $A_0$  is the low degree extension of an assignment satisfying (1), and the functions  $g_{s,\vec{i}',\vec{j}'}$  are equal to the appropriate restrictions of the functions  $f_s$  defined above for  $A_0$ , then the sum-check protocol accepts with probability 1.
- 2. **Soundness:** if  $A_0$  doesn't satisfy (1), then the sum-check protocol accepts with probability at most  $\frac{2dm}{a}$ .

*Proof.* We begin by proving the completeness of the protocol.

**Completeness.** It is clear that the protocol passes the first checks, and we analyze the checks in the fourth and fifth steps. We focus on the fourth item as the arguments are the same. For notational simplicity, we do the proof for s = 1; the argument is identical for s > 1. By (4), we have that

$$f_1(i,j) = \sum_{h,h' \in \mathbb{H}} f_2(i,h,j,h')$$

for all  $i, j \in \mathbb{H}$ . From the uniqueness of the low-degree extension of both sides, as function of i, j, it follows that the low degree extension of the left hand side is equal to the low degree extension of the right hand side. However, since taking low-degree extension is a linear operator (i.e., the low degree extension of f + f' is the sum of the low degree extension of f and the low degree extension of f'), it follows that

$$g_1(i,j) = f_1(i,j) = \sum_{h,h' \in \mathbb{H}} f_2(i,h,j,h') = \sum_{h,h' \in \mathbb{H}} g_{2,i,j}(h,h')$$

for all  $i, j \in \mathbb{F}_q$ .

**Soundness.** For  $A_0$ , we denote by  $f_s$  the functions as defined by (3) for  $A_0$ , and abusing notation we also denote their low degree extension by  $f_s$ . We begin with an informal explanation of the argument. If the sum check protocol accepts, then the check that  $g_0 = c$  passes, but as  $A_0$  does not solve (1) it follows that  $f_0 \neq c$ , hence  $g_0 \neq f_0$ . Then, the protocol checks that the sum of values of  $g_1$  is  $g_0$ , and by definition the sum of values of  $f_1$  is  $f_0$ ; thus, as  $g_0 \neq f_0$ , it follows that  $g_1 \neq f_1$ , and hence choosing random  $i, j \in \mathbb{F}_q$  gives with high probability that  $g_1(i,j) \neq f_1(i,j)$ . Repeating this argument, we get that with high probability the value of  $g_m$  we look at does not coincide with the value of  $f_m$ , however the last check in the process verifies exactly that, hence the protocol would reject.

Formally, let  $E_s$  be the event that

$$g_{s,\vec{i}'_{s-1},\vec{j}'_{s-1}}(i_s,j_s) = f_s(\vec{i}'_{s-1},i_s,\vec{j}'_{s-1},j_s),$$

and let E be the event that the sum-check protocol accepts. First, note that  $E \subseteq E_m$ ; indeed, if the sum-check protocol accepts, the last check passing is equivalent to the fact that  $E_m$  holds. It follows that

$$\Pr\left[E\right] = \Pr\left[\bigcup_{s=1}^{m} E_s \cap E\right] \leqslant \sum_{s=1}^{m} \Pr\left[\bar{E}_{s-1} \cap E_s \cap E\right] \leqslant \sum_{s=1}^{m} \Pr\left[E_s \cap E \mid \bar{E}_{s-1}\right].$$

If  $E_{s-1}$  fails, then  $g_{s-1,\vec{i}'_{s-2},\vec{j}'_{s-2}}(i_{s-1},j_{s-1}) \neq f_{s-1}(\vec{i}'_{s-2},i_{s-1},\vec{j}'_{s-2},j_{s-1})$ , so for the check of the sum-check protocol to pass in iteration s, it must be that the functions  $g_{s,\vec{i}'_{s-1},\vec{j}'_{s-1}}(\star,\star)$  and  $f_s(\vec{i}'_{s-1},\star,\vec{j}'_{s-1},\star)$  are different (else, the sum of  $g_{s,\vec{i}'_{s-1},\vec{j}'_{s-1}}(h,h')$  over  $h,h'\in\mathbb{H}$  would be  $f_{s-1}(\vec{i}'_{s-2},i_{s-1},\vec{j}'_{s-2},j_{s-1})$  as opposed to  $g_{s-1,\vec{i}'_{s-2},\vec{j}'_{s-2}}(i_{s-1},j_{s-1})$ ). Thus, these are distinct univariate polynomials of degree at most  $2(|\mathbb{H}|-1)$ , and the probability of  $E_s$  is the same as the probability that these two functions agree on randomly chosen  $i_s,j_s\in\mathbb{F}_q$ , which is at most  $\frac{2(|\mathbb{H}|-1)}{q}$ . We conclude that

$$\Pr\left[E\right] \leqslant \sum_{s=1}^{m} \Pr\left[E_s \cap E \mid \bar{E}_{s-1}\right] \leqslant \sum_{s=1}^{m} \frac{2\left|\mathbb{H}\right|}{q} = \frac{2m\left|\mathbb{H}\right|}{q} \leqslant \frac{2dm}{q}.$$

So how can we use Lemma 2.4 towards improving upon the locality of the equations that we check? Note that overall, the protocol makes  $(|\mathbb{H}|+1)m$  calls to functions for the g-functions, and 2 queries to the assignment  $A_0$ . Thus, overall the protocol makes  $O(\log(mn)^2)$  queries to the input tables; this is much better than the  $\Theta(n)$  we started with!

The most pressing issue is that for Lemma 2.4 to be useful, we must guarantee that the assignment  $A_0$  and the tables  $g_{s,\vec{t}',\vec{j}'}$  are all polynomials of individual degrees at most  $|\mathbb{H}|-1$ . How do we do that? Well, for the tables  $g_{s,\vec{t}',\vec{j}'}$  this is quite easy in fact; we can represent the function  $g_{s,\vec{t}',\vec{j}'}$  simply by its coefficients. Each one of the functions  $g_{s,\vec{t}',\vec{j}'}$  is only a bi-variate function, so we can represent it by its  $|\mathbb{H}|^2$  coefficients, which is still a poly-logarithmic number of symbols. Hence we can force it to be low-degree just by design. The same cannot be said about  $A_0$ ; if we simply represented it by its list of coefficients we would be back to square one since there are  $|\mathbb{H}|^m$  of them, which is polynomially large. We therefore need to find some other way of representing a low-degree, multi-variate polynomial in a way that enables us to check that it is indeed a low-degree polynomial while reading much less information. This will be the topic of the next lecture.

#### 2.3 Linearizing the Sum-check Protocol

To finish the discussion about the sum check protocol, it will be convenient for us to transform the check made by the sum-check protocol into a single quadratic equation (as opposed to as it currently is as an AND of several equations), and to do so we proceed as follows.

Fix the equation e that we run the sum-check protocol, and let  $G_e$  be the table of coefficients for all the g-functions encountered throughout the protocol. We note that the randomness of the sum-check protocol is  $\vec{i}=(i_1,\ldots,i_m)\in\mathbb{F}_q^m$  and  $\vec{j}=(j_1,\ldots,j_m)\in\mathbb{F}_q^m$ , and fixing the randomness of it, the protocol checks an AND of m linear equations over  $G_e$ , as well as a quadratic equation involving several entries from  $G_e$  and two entries from  $A_0$ . We denote as  $e_{\vec{i},\vec{j},1},\ldots,e_{\vec{i},\vec{j},m+1}$ , and we think of them as  $h_{\vec{i},\vec{j},\ell}(G_e,A_0(\vec{i}),A_0(\vec{j}))=0$  for  $\ell=1,\ldots,m+1$ . We know that each equation  $e_{\vec{i},\vec{j},m+1}$  involves at most poly(log n) entries from  $G_e$ , and  $e_{\vec{i},\vec{j},m+1}$  at most poly(log n) entries from  $G_e$  and 2 entries of  $A_0$ .

In this language, we have proved that assuming  $A_0$  is a low-degree function that satisfies e, with probability 1 all of the equations  $e_{\vec{i},\vec{j},\ell}$  are satisfied; else with probability at most  $\frac{md}{q}$  all of the equations are satisfied. Instead of checking if all of the equations  $e_{\vec{i},\vec{j},\ell}$ , we can take a random linear combination of them

and check it. Namely, for each 
$$\vec{v} \in \mathbb{F}_q^{m+1}$$
, we consider  $h_{\vec{i},\vec{j},\vec{v}} = \sum_{\ell=1}^{m+1} v_\ell h_{\vec{i},\vec{j},\ell}$ , and note that:

1. If  $G_e, A_0$  are such that all of  $e_{\vec{i},\vec{j},\ell}$  are satisfied, then  $h_{\vec{i},\vec{j},\vec{v}}(G_e,A_0(\vec{i}),A_0(\vec{j}))=0$ .

2. Else, at least one of  $e_{\vec{i},\vec{j},\ell}$  is not 0. In that case, the vector  $\vec{h}=(h_{\vec{i},\vec{j},\ell}(G_e,A_0(\vec{i}),A_0(\vec{j})))_{\ell=1,\dots,m+1}$  is not the all 0 vector, and hence  $h_{\vec{i},\vec{j},\vec{v}}(G_e,A_0(\vec{i}),A_0(\vec{j}))=\left\langle \vec{h},\vec{v}\right\rangle \neq 0$  with probability  $1-\frac{1}{q}$ .

We thus present the linearized sum-check protocol. Given an equation e and inputs  $A_0$ ,  $G_e$  as to the sum-check protocol, run the sum-check protocol to generate  $h_{\vec{i},\vec{j},\ell}$  as above, sample  $\vec{v} \in \mathbb{F}_q^m$  uniformly, and check that  $\left\langle \vec{v}, \vec{h} \right\rangle = 0$  for  $\vec{h} = h_{\vec{i},\vec{j},\ell}(G_e, A_0(\vec{i}), A_0(\vec{j}))$ .

Note that the number of v's is  $q^m = poly(n, m)$ , hence for each equation e in the original system this protocol generates polynomially many equations, so overall the number of equations in the new system is polynomial in n and m. Also, we have the following properties:

**Lemma 2.5.** Suppose that  $A_0 \colon \mathbb{F}_q^m \to \mathbb{F}_q$  is a function with individual degrees at most d-1, and  $g_{s,\vec{i}',\vec{j}'} \colon \mathbb{F}_q^2 \to \mathbb{F}_q$  for  $s=0,\ldots,m,\ \vec{i}',\vec{j}' \in \mathbb{F}_q^{s-1}$  are functions of individual degrees at most  $|\mathbb{H}|-1$ . Then

- 1. Completeness: If  $A_0$  is the low degree extension of an assignment satisfying (1), and the functions  $g_{s,\vec{i}',\vec{j}'}$  are equal to the appropriate restrictions of the functions  $f_s$  defined above for  $A_0$ , then the linearized sum-check protocol accepts with probability 1.
- 2. **Soundness:** if  $A_0$  doesn't satisfy (1), then the linearized sum-check protocol accepts with probability at most  $\frac{2dm+1}{q}$ .

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lectures 7,8

#### Dor Minzer

Last time we presented the sum-check protocol which enabled us to test whether a given assignment  $A_0: \mathbb{F}_q^m \to \mathbb{F}_q$  that is promised to be a low degree polynomial satisfies a given equation or not, using only poly(log n) many queries. Today, we will introduce representations of low degree polynomials that enable one to test that a given table of values  $A_0$  indeed represents a low degree polynomial using only constantly many queries. In subsequent lectures we combine this with the sum check protocol and construct a PCP with poly(log n) many queries.

# 1 Low Degree Testing

Throughout this lecture, we are working over the field  $\mathbb{F}_q$  and with the parameters  $m, d \in \mathbb{N}$ , where d is the total degree and m is the number of variables.

#### 1.1 The Line versus Point Scheme

Suppose  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  is a polynomial of total degree at most d. The most natural encoding of f is its table of values; this encoding however, is not good enough for our purposes since it doesn't admit a tester with constantly many queries. A natural idea thus is to consider the table of restriction to "higher dimensional" objects than points. For example, one may consider the table of restrictions of f to lines.

**Definition 1.1.** We define  $S_1(\mathbb{F}_q^m)$  to be the set of all lines in  $\mathbb{F}_q^m$ . That is,  $S_1(\mathbb{F}_q^m)$  is the collection of sets of the form  $L_{a,b} = \{at + b \mid t \in \mathbb{F}_q\}$ , for  $a, b \in \mathbb{F}_q^m$ .

Note that if  $L \in S_1(\mathbb{F}_q^m)$ , then the restriction  $f|_L$  is a univariate polynomial of degree at most d. Indeed, if the line L is parameterized as  $L = \{at+b \mid t \in \mathbb{F}_q\}$ , the restriction can be thought of as the univariate function  $f|_L(t) = f(a+tb)$ , which has degree at most d. Thus, to encode f we can specify its table of values as well as the table of restrictions of f to all lines. Namely, we can encode a polynomial f by  $B_0 \colon \mathbb{F}_q^m \to \mathbb{F}_q$  defined as  $B_0(x) = f(x)$ , as well as  $B_1 \colon \mathsf{Lines}(\mathbb{F}_q^m) \to \{\mathsf{degree}\ d\ \mathsf{univariate}\ \mathsf{polynomials}\}$  defined as  $B_1[L] = f|_L$ .

First, we consider the size of the encoding. Letting  $N=q^m$ , the number of points in  $\mathbb{F}_q^m$  is N, and the number of lines in  $\mathbb{F}_q^m$  is about  $N^2$  (since a line is specified by two points), hence the size of the encoding is about  $N^2+N$ , which is polynomial in the size of the original object; this is good enough for us.

Second, we discuss the local test corresponding to this encoding. The most natural test associated with this scheme is the line versus point test. In this context, our input consists of two tables  $B_0$  and  $B_1$  (which are supposed encodings of a low-degree polynomial f), where  $B_0$  assigns an  $\mathbb{F}_q$ -value to each point x, and  $B_1$  assigns a univariate polynomial over  $\mathbb{F}_q$  of degree at most d to each line in  $S_1(\mathbb{F}_q^m)$ . The test is:

1. Sample a point  $x \in \mathbb{F}_q^m$  randomly and take a random line  $L \in S_1(\mathbb{F}_q^m)$  containing x.

- 2. Query  $B_0(x)$  and  $B_1[L]$ .
- 3. Check that  $B_1[L](x) = B_0(x)$ .

The completeness of this test is clear. That is, if  $B_0, B_1$  are the tables of some polynomial  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  of degree at most d, then the test passes with probability 1. What about the soundness?

**Theorem 1.2.** Suppose that  $B_0, B_1$  are tables that pass the line versus point test with probability at least  $1 - \varepsilon$ . Then there exists a polynomial  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  of total degree d, such that

$$\Pr_{x \in \mathbb{F}_q^m} \left[ f(x) = B_0(x) \right] \geqslant 1 - O(\varepsilon), \qquad \Pr_{L \in S_1(\mathbb{F}_q^m)} \left[ f|_L \equiv B_1[L] \right] \geqslant 1 - O(\varepsilon).$$

In words, if the test passes with probability close to 1, then the tables  $B_0$  and  $B_1$  are close to the tables of some low-degree polynomial f. This regime of parameters is often called the "99% regime", since it makes a structural assertion on the assignment in the case that the test passes with probability close to 1. Such results are typically easier to prove, and they have been indeed utilized in early PCP constructions. However, such results cannot directly be used towards constructing PCPs with small error (i.e. large gap between the completeness and the soundness), and for that one needs to address the so-called "1%" regime. Here, one assumes that the test passes with probability at least  $\varepsilon$  (which is small but bounded away from 0), and wants to conclude that the assignments  $B_0$ ,  $B_1$  still must have a global structure. In this regime, we have the following theorem:

**Theorem 1.3.** There are absolute constants C>0 and c>0 such that the following holds. Suppose that  $B_0, B_1$  are tables that pass the line versus point test with probability at least  $\varepsilon$ , where  $\varepsilon\geqslant \frac{d^Cm^C}{q^c}$ . Then there exists a polynomial  $f:\mathbb{F}_q^m\to\mathbb{F}_q$  of total degree d, such that

$$\Pr_{x \in \mathbb{F}_q^m} \left[ f(x) = B_0(x) \right] \geqslant \Omega(\varepsilon), \qquad \Pr_{L \in \mathit{Lines}(\mathbb{F}_q^m)} \left[ f|_L \equiv B_1[L] \right] \geqslant \Omega(\varepsilon).$$

The known proofs of Theorem 1.3 are quite complicated, and we will not present them here. Part of the issue is that the structure offered to us by lines, and in particular the bipartite graph between lines and points associated with the test, lacks enough "combinatorial structure" and "expansion". Indeed, the proof of Theorem 1.3 is heavily algebraic. To circumvent this, we will consider a different (but similar in spirit) encoding schemes of low degree polynomials that are easier to analyze.

### 1.2 The Plane versus Line and Plane versus Point Schemes

A natural idea of the previous scheme is to consider, instead of lines, higher dimensional affine subspaces.

**Definition 1.4.** We denote by  $S_r(\mathbb{F}_q^m)$  the collection of all affine subspaces of  $\mathbb{F}_q^m$  of dimension r. Whenever q and m are clear from context, we will drop them from the notation and simply write  $S_r$ .

Note that letting  $N=q^m$ , we have that  $|S_r|\approx N^r$ , thus as long as r is constant, we can afford ourselves to use tables for  $S_r$  in our encodings. In this way, given a degree d polynomial  $f\colon \mathbb{F}_q^m\to \mathbb{F}_q$ , we can define  $B_r\colon S_r\to \{\text{total degree }d\text{ polynomial over }r\text{ variables}\}$  as  $B_r[P]=f|_P$  for each  $P\in S_r$ . We will refer to this as the r-dimensional encoding of f.

For concreteness, we shall focus on the case that r=2, in which case  $S_2(\mathbb{F}_q^m)$  consists of all of the affine planes in  $\mathbb{F}_q^m$ . This will be good enough for our purposes, but we remark that there is some merit in

considering higher r. First, we will have to do so in the analysis of the test for r=2, and second, better analysis is known for larger r. Still, our focus shall be on r=2.

So, if we have our (supposed) assignments  $B_0$ ,  $B_1$  to points and lines and  $B_2$  to planes. How shall we go about testing them? The first option is the plane versus point test:

- 1. Sample a point  $x \in \mathbb{F}_q^m$  randomly and take a plane  $P \in S_2(\mathbb{F}_q^m)$  that contains x.
- 2. Query  $B_0(x)$  and  $B_2[P]$ .
- 3. Check that  $B_2[P](x) = B_0(x)$ .

The second option is the plane versus line test:

- 1. Sample a line  $L\in S_1(\mathbb{F}_q^m)$  randomly and take a plane  $P\in S_2(\mathbb{F}_q^m)$  that contains L.
- 2. Query  $B_1[L]$  and  $B_2[P]$ .
- 3. Check that  $B_2[P]|_L \equiv B_1[L]$ .

And yet, there are third and fourth options. Both go under the name "the plane versus plane test", but they vary in the dimension of space these planes intersect in. The first variant is the Plane versus Plane test on planes that intersect on a line:

- 1. Sample a line  $L \in S_1(\mathbb{F}_q^m)$  randomly and take two plane  $P, P' \in S_2(\mathbb{F}_q^m)$  that contain L.
- 2. Query  $B_2[P]$  and  $B_2[P']$ .
- 3. Check that  $B_2[P]|_L \equiv B_2[P']|_L$ .

The second variant is the Plane versus Plane test on planes that intersect on a point:

- 1. Sample a point  $x \in S_0(\mathbb{F}_q^m)$  randomly and take two plane  $P, P' \in S_2(\mathbb{F}_q^m)$  that contain x.
- 2. Query  $B_2[P]$  and  $B_2[P']$ .
- 3. Check that  $B_2[P](x) = B_2[P'](x)$ .

It turns out that all of these tests work, roughly equally well, in the sense that a result analogous to Theorem 1.3 holds for each one of the, albeit with somewhat different parameters. In fact, one can reduce the analysis of any one of them to any other; we will see some of these connections here, and some of them in the problem set. For the purposes of our future PCP application, we will have to analyze the plane versus point and plane versus plane tests; in particular, we will prove the following statement:

**Theorem 1.5.** Suppose that  $B_0, B_2$  are tables for the plane versus point test with probability at least  $\varepsilon \geqslant \frac{d^2}{a^{1/10}}$ . Then there exists a polynomial  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  of total degree d, such that

$$\Pr_{x \in \mathbb{F}_q^m} \left[ B_0(x) = f(x) \right] \geqslant \varepsilon - \frac{md}{q^{1/10}}.$$

In words, theorem 1.5 says that if the plane versus point passes with significant probability  $\varepsilon$ , then the points table  $B_0$  agrees with a function f of degree at most d on at least  $\varepsilon - o(1)$  of the points. This formulation will be quite important for us for the purpose of this lecture, since it admits a proof by induction on m (which is the route we are going to take). For future use, we need a corollary of it, which we state now and deduce from Theorem 1.5 later in Section 2.6.

**Theorem 1.6.** Suppose that  $B_0, B_2$  are tables for the plane versus point test with probability at least  $\varepsilon \geqslant \frac{d^2}{q^{1/10}}$ . Then for all  $\delta > \frac{d^2}{q^{1/10}}$  there is  $k \leqslant \frac{2}{\delta^2}$  and a list of polynomials  $f_1, \ldots, f_k \colon \mathbb{F}_q^m \to \mathbb{F}_q$  of total degree d, such that

$$\Pr_{x \in P \in S_2(\mathbb{F}_q^m)} \left[ B_0(x) = B_2[P](x) \wedge B_2[P] \neq f_j|_P \ \forall j \right] \leqslant 3\delta.$$

In words, we can find a short list of low-degree polynomials  $f_1, \ldots, f_k$  such that except for small probability, if the test passes, then it is because the plane table is consistent with one of the polynomials in the list.

# 2 Analysis of the Plane versus Plane Test

En route to proving Theorem 1.5, we need to consider the related Plane versus Plane test on planes that intersect on lines as described earlier. This is the content of this section and where most the "action" takes place.

Let m=3, and suppose  $B_2\colon S_2(\mathbb{F}_q^3)\to \{\text{total degree }d\text{ polynomials in 2-variables}\}$  passes the plane versus plane test with probability at least  $\varepsilon$ . Then, in light of the formulation of Theorem 1.3, one expects to prove that there is a polynomial  $f\colon \mathbb{F}_q^3\to \mathbb{F}_q$  of total degree at most d that agrees with  $B_2$  on  $\Omega(\varepsilon)$  of the planes. This is true and will come as a byproduct of the argument we present, however for the purpose of Theorem 1.5, we need the following list-decoding statement.

**Theorem 2.1.** Suppose that  $B_2$  is a table that pass the plane versus plane test with probability at least  $\varepsilon$ , and let  $\delta \geqslant \frac{2(d+1)}{q}$ . Then there is  $k \leqslant \frac{1}{\delta}$  and k polynomials  $f_1, \ldots, f_k \colon \mathbb{F}_q^3 \to \mathbb{F}_q$  of total degree d, such that

$$\Pr_{\substack{P,P'\in S_2(\mathbb{F}_q^3)\\as \text{ in the test}}}\left[B_2[P]_{P\cap P'}\equiv B_2[P']_{P\cap P'}\wedge \ \forall j(B_2[P]\not\equiv f_j\vee B_2[P']\not\equiv f_j)\right]\leqslant \delta+2\sqrt{\frac{d+1}{q}}.$$

In words, Theorem 2.1 provides a short list of polynomials  $f_1, \ldots, f_k$  such that all of the success of the test can be explained by it. Namely, for all but small fraction of the tests (P, P'), if the test passes on planes P and P', then there is some  $f_j$  in the list such that  $f_j$  is consistent with both  $B_2[P]$  and  $B_2[P']$ .

The main feature which of the fact that m=3, is that two randomly chosen planes intersect on a line, proved in the following fact. <sup>1</sup>

Fact 2.2. 
$$\Pr_{P,P'\in S_2(\mathbb{F}_q^3)}\left[\dim(P\cap P')\neq 1\right]\leqslant \frac{1}{q^2}$$
.

*Proof.* The number of planes in  $\mathbb{F}_q^3$  is exactly  $\frac{q^3(q^3-1)(q^3-q)}{q^2(q^2-1)(q^2-q)}$ ; here, the numerator counts the number of ways to choose 3 points that span an affine plane, and the denominator counts the number of times a given plane P is counted. Simplifying, this is  $N=q\frac{q^3-1}{q-1}=q(q^2+q+1)$ . Thus, the number of pairs of planes is  $N^2$ . If two planes do not intersect on a line, then they either are identical – there are N such pairs, or

If two planes do not intersect on a line, then they either are identical – there are N such pairs, or are parallel – there are  $N \cdot (q-1)$  such pairs. Indeed, they cannot intersect at a point, since if P, P' intersect on a point x, we can write them as P = x + L, P' = x + L' for two subspaces L, L', and as  $\dim(L \cap L') = \dim(L) + \dim(L') - \dim(L \oplus L') \geqslant 4 - 3 = 1$  it follows that P and P' intersect on a line.

It follows that

$$\Pr_{P,P'\in S_2(\mathbb{F}_q^3)}\left[\dim(P\cap P')\neq 1\right]=\frac{N+N(q-1)}{N^2}=\frac{1}{N}\leqslant \frac{1}{q^2}. \hspace{1cm} \Box$$

<sup>&</sup>lt;sup>1</sup>We remark that importantly, the analogous statement for m=r+1 is true for r-dimensional affine subspaces of  $\mathbb{F}_q^m$ . Namely, two random r-dimensional affine subspaces of  $\mathbb{F}_q^{r+1}$  intersect on an r-1-dimensional affine subspace except with small probability. Thus, the proof we presents works in this more general setting, and we will in fact use it later on in this generality.

### 2.1 The Assignment Graph

Consider the graph G=(V,E) whose vertex set is  $S_2(\mathbb{F}_q^3)$ , and two vertices  $P,P'\in V$  are adjacent if  $B_2[P]_{P\cap P'}\equiv B_2[P']_{P\cap P'}$ . Note that  $|E|\geqslant \varepsilon\left(1-\frac{1}{q^2}\right)|V|^2$ , so thinking of  $\varepsilon$  as bounded away from 0, the graph G is dense. We will want to study the combinatorial structure of G, and in particular show that it is roughly a union of cliques. We will then consider the cliques that are sizable, which are collections of planes that are all around consistent, and for each one of them we will construct a degree d function f that is consistent it. This will be our list.

# 2.2 Making G Transitive

The heart of the analysis of the Plane versus Plane test is the fact that the graph G is close to being a *transitive* graph.

**Definition 2.3.** A graph H = (V, E) is called transitive if there are no triple of vertices  $u, v, w \in V$  such that  $(u, v) \in E$ ,  $(v, w) \in E$  but  $(u, w) \notin E$ .

We show that G is nearly transitive, in the sense that we can remove a few edges from it and make it transitive. To do so, define the parameter  $\beta(H)$  which captures the distance of H from being transitive.

**Definition 2.4.** Let H = (V, E) be a graph. For each non-edge  $(u, w) \notin E$ , define

$$\beta(u,w) = \Pr_{v \in V} \left[ (u,v) \in E, (v,w) \in E \right], \qquad \text{and subsequently } \beta(H) = \max_{(u,w) \notin E} \beta(u,w).$$

We prove the following two lemmas with respect to the parameter  $\beta(H)$ . The first lemma asserts that if  $\beta(H)$  is small, then one can remove a few edges from H and make it transitive. The second lemma asserts that  $\beta(G)$  is small.

**Lemma 2.5.** Given a graph H=(V,E), one can remove from it at most  $2\sqrt{\beta(H)}|V|^2$  edges to get a graph H'=(V,E') which is transitive.

*Proof.* The proof is by a iterative process. Denote  $\beta = \beta(H)$ , and perform the following iterations as long as they change the graph H:

- 1. If there is v such that  $d(v) \leq \sqrt{\beta} |V|$ , remove all edges adjacent to v.
- 2. Else, take some  $v \in V$  and remove all edges between neighbours of v and non-neighbours of v.

It is clear that when the process terminates, the graph is transitive, and the main task is to upper bound the total number of edges removed by the process. Clearly, the first operation can remove at most  $\sqrt{\beta} |V|^2$  edges in total. For the second operation, consider an invocation of it and denote by N(v) the set of neighbours of v, and by C(v) the connected component of v. The second operation removes edges between N(v) and  $C(V) \setminus (N(v) \cup \{v\})$ . Prior to the removal, define

$$\begin{split} E_{\mathsf{non}} &= \left\{ (u,w) \mid w \in C(V) \setminus (N(v) \cup \{v\}), u \in N(v) \right\}, \\ E_{\mathsf{remove}} &= \left\{ (u,w) \in E \mid w \in C(V) \setminus (N(v) \cup \{v\}), u \in N(v) \right\}. \end{split}$$

By definition of  $\beta(H)$ , for each w such that  $(v,w) \notin E$ , there are at most  $\beta|V|$  such  $u \in N(v)$  that  $(u,w) \in E$ . Thus,

$$|E_{\mathsf{remove}}| \leq |C(V) \setminus (N(v) \cup \{v\})| \cdot \beta |V|$$
.

On the other hand, the total number of pairs u, w such that  $u \in N(v)$  and  $w \notin N(v)$  is at least  $d(v) \cdot |C(V) \setminus (N(v) \cup \{v\})|$ , and since the first step of the process was not executed, we get

$$|E_{\mathsf{non}}| \geqslant \sqrt{\beta} |V| |C(V) \setminus (N(v) \cup \{v\})|.$$

It follows that  $|E_{\mathsf{remove}}| \leq \sqrt{\beta} \, |E_{\mathsf{non}}|$ . Thus, the total number of edges removed is at most  $\sqrt{\beta}$  times the total number of pairs that were in the sets  $E_{\mathsf{non}}$ , and to finish the argument we argue that each pair of vertices may appear in  $E_{\mathsf{non}}$  in at most a single iteration.

Indeed, if  $(u,w) \in E_{\mathsf{non}}$  when the iteration is invoked on v, then at that point of the process w and u are in the same connected component. However, after this point there are no edges between  $C(v) \setminus (N(v) \cup \{v\})$  and  $N(v) \cup \{v\}$ , which means that v and w are in different connected components, and as v and w are in the same connected component at that time, it follows that w and w are in different connected components. In other words, when the pair (u,w) appears in  $E_{\mathsf{non}}$  the vertices w and w are in the same connected component, and after that step they are not, hence each pair appears in  $E_{\mathsf{non}}$  at most once.

Thus, to prove that G is almost transitive, it suffices to prove an upper bound on  $\beta(G)$ , and this is the content of the following lemma.

**Lemma 2.6.** For our graph G = (V, E) above,  $\beta(G) \leqslant \frac{d+1}{q}$ .

*Proof.* Consider any non-edge  $(P_1, P_3)$  in G.

Sample  $P_2 \in V$ ; what is the probability that  $(P_1, P_2)$  and  $(P_2, P_3)$  are all edges? In that case, we get that either  $P_2$  is disjoint from the line  $P_1 \cap P_3$ , which happens with probability at most  $\frac{1}{q}$ , or else  $P_1 \cap P_2 \cap P_3$  is a point x. In that case, the point x is distributed uniformly in  $P_1 \cap P_3$ , and we have that  $B_2[P_1]$ ,  $B_2[P_2]$  agree on  $P_1 \cap P_2$  and  $B_2[P_2]$ ,  $B_2[P_3]$  agree on  $P_2 \cap P_3$ , so  $B_2[P_1](x) = B_2[P_3](x)$ . However, since  $(P_1, P_3)$  is a non edge,  $B_2[P_1]|_{P_1 \cap P_3}$  and  $B_2[P_3]|_{P_1 \cap P_3}$  are two distinct degree d univariate polynomials, and hence this is the probability that they agree on a randomly chosen point from  $P_1 \cap P_3$ , which is at most  $\frac{d}{q}$ .

Summarizing, applying Lemmas 2.5, 2.6 on G=(V,E) we may find G'=(V,E') with  $E'\subseteq E$  and  $|E'|\geqslant |E|-2\sqrt{(d+1)/q}N^2$  which is transitive. Note that a transitive graph is a union of cliques, so we may write  $V=C_1\cup\ldots\cup C_k$  where each  $C_i$  in V is a clique. Thus, the number of edges in G' is  $\sum_{i=1}^k {|C_i|\choose 2}=|E'|$ , and we show that almost all edges of G' are covered by large cliques. Let  $\delta>0$  to be chosen, and set  $I=\{i\mid |C_i|\geqslant \delta N\}$ . Then

$$\sum_{i \notin I} \binom{|C_i|}{2} \leqslant \frac{1}{2} \sum_{i \notin I} |C_i|^2 \leqslant \frac{\delta N}{2} \sum_{i \notin I} |C_i| \leqslant \delta N^2.$$

Thus, we find that

$$\sum_{i \in I} \binom{|C_i|}{2} \geqslant |E'| - \delta N^2 \geqslant \varepsilon N^2 - \left(2\sqrt{\frac{d+1}{q}} + \delta\right) N^2.$$

Also, clearly  $|I| \leq \frac{1}{\delta}$ . In the rest of the argument, we will find a list of polynomials  $(f_i)_{i \in I}$  which "explain" all of the edges inside the cliques  $(C_i)_{i \in I}$ , which finishes the proof of Theorem 2.1.

# 2.3 Interpolating a Low-degree Polynomial in Each $C_i$

Next, we show that for each  $C_i$ , we may find a polynomial  $f_i : \mathbb{F}_q^3 \to \mathbb{F}_q$  of total degree at most d that agrees with  $B_2[P]$  for all  $P \in C_i$ .

**Claim 2.7.** Suppose that  $\delta \geqslant \frac{2(d+1)}{q}$ , and let  $i \in I$ . Then there exists a polynomial  $f_i \colon \mathbb{F}_q^3 \to \mathbb{F}_q$  of total degree d such that  $f_i|_P \equiv B_2[P]$  for all  $P \in C_i$ .

*Proof.* Choose linearly independent vectors  $x, y \in \mathbb{F}_q^3$ , set  $T = \operatorname{Span}(x, y)$  and take  $a \in \mathbb{F}_q^3 \setminus T$  uniformly. Note that each  $\lambda \in \mathbb{F}_q$ , the distribution of  $\lambda a + T$  is uniform over  $S_2$ . Thus, it follows that

$$\mathbb{E}_{a,T} \left[ \sum_{\lambda \in \mathbb{F}_q} 1_{\lambda a + T \in C_i} \right] = q \frac{|C_i|}{|S_2|} \geqslant \delta q \geqslant 2(d+1),$$

hence there are a and T such that  $\sum_{\lambda \in \mathbb{F}_q} 1_{\lambda a + T \in C_i} \geqslant 2(d+1)$ , and we fix such a and T. Without loss

of generality, we assume that  $T=\operatorname{Span}(e_1,e_2)$  and  $a=e_3$ , otherwise we can apply an affine linear transformation. Let  $\Lambda=\{\lambda\in\mathbb{F}_q\mid \lambda a+T\in C_i\}$ , and take  $\Lambda'\subseteq\Lambda'$  of size 2(d+1). Note that the probability that a randomly chosen plane is parallel to a+T is  $\frac{1}{(q^3-1)(q^3-q)/(q^2-1)(q^2-q)}\leqslant\frac{1}{q^2}$ , so it follows that the probability that a randomly chosen plane is in C and not parallel to a+T is at least  $\delta-\frac{1}{q^2}$ , and using the same technique as above we may find T' that intersects T on a line, such that has at least d+1 of the affine shifts of T' in C. That is, there are  $b\in\mathbb{F}_q^3$  and T' such that  $b\not\in T'$ ,  $\dim(T\cap T')=1$  and  $\Gamma\subseteq\mathbb{F}_q$  of size d+1 such that  $\{\gamma b+T'\}_{\gamma\in\Gamma}\subseteq C_i$ . By applying linear transformations again we may assume  $b=e_2$  and  $T'=\operatorname{Span}(e_1,e_3)$ .

We will show, using interpolation, that there is  $f_i \colon \mathbb{F}_q^3 \to \mathbb{F}_q$  of total degree at most 2d that agrees with  $B_2[\gamma b + T']$  for all  $\gamma \in \Gamma$ , we will then argue that  $f_i$  must agree with  $B_2[\lambda a + T]$  for all  $\lambda \in \Lambda'$ , and then that  $f_i$  must agree with B[P] for all  $P \in C_i$ . Finally, we will show that the degree of  $f_i$  must be in fact at most d.

Let 
$$\ell_{\gamma}(y) = \prod_{\gamma' \in \Gamma \setminus \{\gamma\}} \frac{y - \gamma'}{\gamma - \gamma'}$$
, and define

$$f_i(x, y, z) = \sum_{\gamma \in \Gamma'} \ell_{\lambda}(y) B_2[\gamma a + T](x, z).$$

Clearly,  $f_i$  has degree at most  $|\Gamma| + d - 1 \le 2d$  and  $f_i|_{\gamma b + T'} = f(x, \gamma, z) = B_2[\gamma b + T'](x, z)$  for  $\gamma \in \Gamma'$ . Thus,  $f_i$  agrees with all  $\{\gamma b + T'\}_{\gamma \in \Gamma}$ , and additionally the individual degree of y in  $f_i$  is at most d. Fix  $\lambda \in \Lambda'$  and consider the plane  $\lambda a + T$ . Within this plane, consider for each  $\alpha$  the line  $\ell_{\alpha,\lambda}$  defined by  $x = \alpha, z = \lambda$ . Note that the line  $\ell_{\alpha,\lambda}$  intersects each one of the planes  $\{\gamma b + T'\}$  at a point  $p = (\alpha, \gamma, \lambda)$  which is inside  $(\lambda a + T) \cap (\gamma b + T')$ , and hence

$$f_i(p) = B[\gamma b + T'](p) = B[\lambda a + T](p),$$

so we get that  $f_i|_{\ell_{\alpha,\lambda}}$  and  $B[\lambda a+T]|_{\ell_{\alpha,\lambda}}$  agree on all points  $(\alpha,\gamma,\lambda)$  for  $\gamma\in\Gamma$ , which constitute at d+1 points on  $\ell_{\alpha,\lambda}$ . Since these are two degree d polynomials, we conclude that they must be the same, hence  $f_i$  agrees with  $B[\lambda a+T]$  on all lines  $\ell_{\alpha,\lambda}$  and therefore  $f_i|_{\lambda a+T}\equiv B[\lambda a+T]$  for all  $\lambda\in\Lambda'$ .

Next, note that any plane P is either parallel to  $\lambda a + T$  or intersects it in a line. For  $P \in C_i$  that intersect it on a line, we get that  $B_2[P]$  and  $B_2[\lambda a + T]$  agree on the intersection line for all  $\lambda \in \Lambda'$ , and as  $f_i$  and

 $B_2[\lambda a + T]$  agree, we get that  $B_2[P]$  and  $f_i$  agree on  $\bigcup_{\lambda \in \Lambda'} (\lambda a + T) \cap P$ . As this set has size  $|\Lambda'| q$ , we conclude that  $f_i|_P$  and  $B_2[P]$  agree on at least 2(d+1)q points  $p \in P$ , hence

$$\Pr_{p \in P} [f_i|_P(p) = B_2[P](p)] \geqslant \frac{2(d+1)q}{q^2} = \frac{2(d+1)}{q},$$

and by the Schwarz-Zippel lemma, as the degrees of  $f_i|_P$ ,  $B_2[P]$  are both are most 2d, it follows that  $f_i|_P \equiv B_2[P]$ . Thus, we conclude that  $f_i|_P$  and  $B_2[P]$  agree on all planes that are not parallel to T.

For planes parallel to T, say  $P'=b+T\in C_i$ , sampling  $P=w+T'\in S_2$  we get that with probability  $\geqslant 1-1/q$  it intersects P' in a line; conditioned on that and looking at the shifts  $\lambda w+T'$  we get as before that in expectation, at least  $\left(\delta-\frac{1}{q}\right)q\geqslant 2d+1$  of them are in  $C_i$ . Thus, we can find w,T' such that at least 2d+1 of  $\lambda\in\mathbb{F}_q$ , we have  $\lambda w+T'\in C_i$ . Then get that  $B_2[P']$  and  $B_2[\lambda w+T']$  agree on  $P'\cap(\lambda w+T')$  for these  $\lambda$ 's, hence we get that  $f_i|_{P'}$  and  $B_2[P']$  agree on at least (2d+1)q points, and again by Schwarz-Zippel  $B_2[P']\equiv f_i|_{P'}$ .

Finally, we argue that  $f_i$  has degree at most d. Suppose this is not the case, and consider monomial  $x^{m_1}y^{m_2}z^{m_3}$  of maximal degree, and furthermore take  $x^{m_1}y^{m_2}z^{m_3}$  of that degree that maximizes  $m_2$ . Choosing a random plane amounts to looking at all points (x,y,z) such that ax+by+cz=e for randomly chosen  $(a,b,c)\neq 0$  and uniformly chosen  $e\in \mathbb{F}_q$ . With probability  $g\in \mathbb{F}_q$  we have  $g\in \mathbb{F}_q$  and uniformly chosen  $g\in \mathbb{F}_q$ . With probability over  $g\in \mathbb{F}_q$  we have that this plane is in  $g\in \mathbb{F}_q$  with probability at least  $g\in \mathbb{F}_q$ . Then we can write this as  $g\in \mathbb{F}_q$  and the monomial we are inspecting yields

$$(-1)^{m_2} \frac{a^{m_2}}{b^{m_2}} x^{m_1+m_2} z^{m_3} + \text{other monomials.}$$

We look at the function  $f_i(x, -\frac{a}{b}x - \frac{c}{b}y + \frac{d}{b}, z)$ , and in particular at the coefficient of  $x^{m_1+m_2}z^{m_3}$  as a function of a, c, e. Then  $x^{m_1}y^{m_2}z^{m_3}$  gives us  $(-1)^{m_2}\frac{a^{m_2}}{b^{m_2}}$ , and no other monomial can give this power of a (indeed, this could only come from a monomial  $x^{m'_1}y^{m'_2}z^{m'_3}$  such that  $m'_1+m'_2+m'_3=m_1+m_2+m_3$  and  $m'_1=m_1, m'_2\geqslant m_2$ , but we chose the monomial to maximize  $m_2$  so that then  $m'_2=m_2, m'_1=m_1$  and  $m'_3=m_3$ ), so the coefficient of  $x^{m_1+m_2}z^{m_3}$  is a polynomial in a, c, e of degree at most 2d, hence choosing the values of a, c, e randomly, it is non-zero with probability at least  $1-\frac{2d}{q}$ . With probability at least  $\delta-\frac{1}{q}\geqslant \frac{2d+1}{q}$  the chosen plane is in  $C_i$ , and as the sum of these two probabilities exceeds 1, it means that there is a plane P specified by the equation ax+by+cz=e in  $C_i$  such that the monomial  $x^{m_1+m_2}z^{m_3}$  appears in  $f_i|_P$ , but then  $B_2[P]=f_i|_P$  has degree larger than d, and contradiction.

# **2.4** Proof of Theorem 1.5 for m=3

Having established Theorem 2.1, we can now prove Theorem 1.5 for m=3. The proof uses the connection between the plane versus plane and the plane versus point test we earlier eluded to.

**Theorem 2.8.** Suppose that  $B_0, B_2$  are tables that pass the plane versus point test with probability at least  $\varepsilon \geqslant \frac{d^2}{q^{1/10}}$ . Then there exists a polynomial  $f: \mathbb{F}_q^3 \to \mathbb{F}_q$  of total degree d, such that

$$\Pr_{x} \left[ f(x) = B_0(x) \right] \geqslant \varepsilon - \frac{d}{q^{1/10}}.$$

*Proof.* We first observe a connection between the plane versus plane test and the plane versus point test. Namely, we argue that if  $B_2$  and  $B_0$  pass the plane versus point test with probability at least  $\varepsilon$ , then  $B_2$ 

passes the plane versus plane test with probability at least  $\varepsilon^2 - \frac{d+1}{q}$ . Indeed, sample  $x \in \mathbb{F}_q^3$  and two planes  $P_1, P_2$  independently that contain x. Then

$$\underset{x,P_1,P_2}{\mathbb{E}} \left[ 1_{B[P_1](x) = B_0(x)} 1_{B[P_2](x) = B_0(x)} \right] = \underset{x}{\mathbb{E}} \left[ \underset{P \ni x}{\mathbb{E}} \left[ 1_{B[P](x) = B_0(x)} \right]^2 \right] \geqslant \underset{x}{\mathbb{E}} \left[ \underset{P \ni x}{\mathbb{E}} \left[ 1_{B[P](x) = B_0(x)} \right] \right]^2 \geqslant \varepsilon^2.$$

Thus, note that sampling  $P_1$ ,  $P_2$  that contain a common line means that  $P_1$ ,  $P_2$  intersect on a line  $\ell$ , and so we get that

$$\mathbb{E}_{\ell, P_1, P_2} \left[ \sum_{x \in \ell} 1_{B[P_1](x) = B_0(x)} 1_{B[P_2](x) = B_0(x)} \right] \geqslant q \varepsilon^2,$$

meaning that with probability at least  $\varepsilon^2 - \frac{d+1}{q}$ ,  $B[P_1]$  and  $B[P_2]$  agree on at least d+1 of the points in  $\ell$ , in which case they are identical by Schwarz-Zippel. Overall,  $B_2$  passes the plane versus plane test with probability at least  $\varepsilon^2 - \frac{d+1}{q}$ .

Take  $\delta = \frac{d^C}{q^c}$  for C, c > 0 to be determined, and take all polynomials  $f_1, \ldots, f_k \colon \mathbb{F}_q^3 \to \mathbb{F}_q$  that agree with  $B_2[P]$  for at least  $\delta$  fraction of planes; note that by Claim 2.12 we have  $k \leqslant \frac{1}{\delta^2 - d/q} \leqslant \frac{2}{\delta^2}$ . We now define

$$W_i = \{ P \mid f_i|_P \equiv B_2[P] \},$$

and argue that the probability the plane versus point test picks a plane outside  $W:=\bigcup_{i=1}^k W_i$  but passes is very small. To see that, define an assignment  $B_2'$  to the planes such that  $B_2'[P]=B_2[P]$  if  $P\not\in W$ , and for each  $P\in W$  we choose  $B_2'[P]$  to be a randomly chosen degree d polynomial over P. By standard probabilistic arguments, after this re-randomization no degree d polynomial agrees with  $B_2'$  on more than  $\delta+10\frac{d\log(q^{d^3})}{q}\leqslant 11\delta$  fraction of the planes P, and we fix such randomization. We claim that this randomization implies that the success probability of the test is at most  $10\sqrt{\delta}$ . Indeed, otherwise by the above connection we would be able to conclude that  $B_2'$  passes the plane versus plane test with probability at least  $99\delta$ , and by Theorem 2.1 we can find a function degree d function  $f: \mathbb{F}_q^3 \to \mathbb{F}_q$  that agrees with  $B_2'$  for at least  $50\delta$  of the planes, which contradicts the property of the randomization. This means that prior to the randomization,

$$\Pr_{x \in P \in S_2(\mathbb{F}_q^3)} \left[ f(x) = B_2[P](x) \land \forall j f_j |_P \not\equiv B_2[P] \right] \leqslant \Pr_{x \in P \in S_2(\mathbb{F}_q^3)} \left[ f(x) = B_2'[P](x) \right] \leqslant 10\sqrt{\delta}.$$

The following claim finishes the proof.

Claim 2.9. For 
$$\eta = \max\left(\left(\frac{100\varepsilon}{q^2\delta^2}\right)^{1/3}, \frac{100\sqrt{\delta}}{\varepsilon}\right)$$
, there is  $j$  such that  $\Pr_{x \in \mathbb{F}_q^3}\left[f_j(x) = B_0(x)\right] \geqslant \varepsilon - \eta$ .

Proof. Assume otherwise, so that the set  $X_j=\{x\mid f_j(x)=B_0(x)\}$  contains at most  $\varepsilon-\eta$  elements for each j. By the assumption on the test,  $\mathbb{E}_P\left[\sum_{x\in P}1_{B_0(x)=B_2[P](x)}\right]\geqslant \varepsilon q^2$ , so by Claim 2.10 with probability at least  $\eta$  over P,  $\sum_{x\in P}1_{B_0(x)=B_2[P](x)}\geqslant (\varepsilon-\eta)q^2$ . However, if we choose P at random, then by Claim 2.11 and the union bound we have  $|P\cap X_j|\leqslant (\varepsilon-50\eta)q^2$  for all j except with probability  $\frac{k\varepsilon}{q^2\eta^2}\leqslant \frac{2\varepsilon}{q^2\eta^2\delta^2}$ . Thus with probability at least  $\eta-\frac{2\varepsilon}{q^2\eta^2\delta^2}\geqslant \frac{\eta}{2}$  both events hold together. In this case we get that  $f_j|_P\not\equiv B_2[P]$  for all j, as otherwise we would have that  $|P\cap X_j|=\sum_{x\in P}1_{B_0(x)=B_2[P](x)}$ . In conclusion, we get that with probability at least  $\frac{\eta}{2}$  we have that  $\sum_{x\in P}1_{B_0(x)=B_2[P](x)}\geqslant (\varepsilon-\eta)q^2$  and  $f_j|_P\not\equiv B_2[P]$ , and so

$$\Pr_{x \in P \in S_2(\mathbb{F}_q^3)} \left[ B_0(x) = B_2[P](x), f_j|_P \not\equiv B_2[P] \,\forall j \right] \geqslant \frac{\eta}{2} \cdot (\varepsilon - \delta) > 10\sqrt{\delta},$$

and contradiction.  $\Box$ 

To finish the proof we choose 
$$\delta = \varepsilon^2 \frac{d}{a^{1/5}}$$
 and  $\eta = \frac{d}{a^{1/10}}$ .

#### 2.4.1 Auxiliary Claims

In this section we prove auxiliary claims that were used in the proof of Theorem 2.8. The first one is an averaging argument:

Claim 2.10. 
$$\Pr_P\left[\sum_{x\in P} 1_{B_0(x)=B_2[P](x)} \geqslant (\varepsilon - \delta)q^2\right] \geqslant \delta.$$

*Proof.* The expectation of  $\sum_{x\in P} 1_{B_0(x)=B_2[P](x)}$  is at least  $\varepsilon q^2$ , and it is never more than  $q^2$ , so letting z denote the probability in question, we get that  $zq^2+(1-z)(\varepsilon-\delta)q^2\geqslant \varepsilon q^2$ , hence  $zq^2\geqslant \delta q^2$ , and so  $z\geqslant \delta$ .  $\square$ 

The second is a sampling lemma, saying that a random plane P samples points well:

**Claim 2.11.** Let  $X \subseteq \mathbb{F}_q^3$  be a set, then

$$\Pr_{P} \left[ |P \cap X| \geqslant q^2 \frac{|X|}{|\mathbb{F}_q^3|} + q^2 \delta \right] \leqslant \frac{1}{q^2 \delta^2} \frac{|X|}{|\mathbb{F}_q^3|}$$

*Proof.* Write a randomly chosen plane as  $P=\{x_1,\ldots,x_{q^2}\}$ , denote  $Z_i=1_{x_i\in X}$ , and note that  $|P\cap X|=\sum_{i=1}^{q^2}Z_i$ . By linearity of expectation,  $\mathbb{E}_P\left[|P\cap X|\right]=q^2\frac{|X|}{|\mathbb{F}_q^3|}$ . Also, we note that for all  $i\neq j$ , the points  $x_i,x_j$  are distributed uniformly over tuples of distinct points in  $\mathbb{F}_q^3\times\mathbb{F}_q^3$ . Thus,

$$\mathbb{E}_{P}\left[|P \cap X|^{2}\right] = q^{2} \frac{|X|}{|\mathbb{F}_{q}^{3}|} + \sum_{i \neq j} \mathbb{E}_{P}\left[1_{x_{i}, x_{j} \in X}\right] \leqslant q^{2} \frac{|X|}{|\mathbb{F}_{q}^{3}|} + q^{2}(q^{2} - 1) \frac{|X|}{|\mathbb{F}_{q}^{3}|} \frac{|X| - 1}{|\mathbb{F}_{q}^{3}| - 1},$$

which yields  $\mathbb{E}_P\left[|P\cap X|^2\right]\leqslant q^2\frac{|X|}{|\mathbb{F}_q^3|}+\left(q^2\frac{|X|}{|\mathbb{F}_q^3|}\right)^2$ . Thus  $\mathrm{var}(|P\cap X|)\leqslant q^2\frac{|X|}{|\mathbb{F}_q^3|}$ , and by Chebyshev's inequality the left hand side of the claim is at most

$$\Pr_{P}\left[\left||P\cap X|-q^2\frac{|X|}{|\mathbb{F}_q^3|}\right|\geqslant q^2\delta\right]\leqslant \frac{q^2\frac{|X|}{|\mathbb{F}_q^3|}}{q^4\delta^2}\leqslant \frac{1}{q^2\delta^2}\frac{|X|}{|\mathbb{F}_q^3|}.$$

The third claim is a list decoding size bound, and we prove it in a rather general form. In our case, the code will be the planes code, in which a polynomial f is encoded by its table of restrictions; this code has relative distance at least  $\frac{d}{a}$ 

Claim 2.12. Suppose C is an error correcting code over  $\mathbb{F}_q^n$  with relative distance 1-s, and let  $\delta > \sqrt{s}$ . When for every  $w \in \mathbb{F}_q^n$ , the number of codewords  $c \in C$  such that w and c agree on at least  $\delta n$  coordinates, is at most  $\frac{1}{\delta^2 - s}$ .

*Proof.* Let  $c_1, \ldots, c_k \in C$  be all codewords that agree with w on at least  $\delta$  fraction of coordinates. Then we have that  $\mathbb{E}_{i \in [k]} \left[ \mathbb{E}_{x \in [n]} \left[ 1_{c_i(x) = w(x)} \right] \right] \geqslant \delta$ , so by Cauchy-Schwarz

$$\delta^{2} \leqslant \underset{x \in [n]}{\mathbb{E}} \left[ \underset{i \in [k]}{\mathbb{E}} \left[ 1_{c_{i}(x) = w(x)} \right] \right]^{2} \leqslant \underset{x \in [n]}{\mathbb{E}} \left[ \underset{i \in [k]}{\mathbb{E}} \left[ 1_{c_{i}(x) = w(x)} \right]^{2} \right]$$

$$= \underset{x \in [n]}{\mathbb{E}} \left[ \frac{1}{k^{2}} \sum_{i=1}^{k} 1_{c_{i}(x) = w(x)} + \frac{1}{k^{2}} \sum_{i \neq j} 1_{c_{i}(x) = w(x) = c_{j}(x)} \right].$$

Note that for  $i \neq j$ , we have that  $\mathbb{E}_{x \in [n]} \left[ 1_{c_i(x) = w(x) = c_j(x)} \right] \leqslant \eta$  since the relative distance of C is at least 1-s, and  $c_i, c_j$  are codewords. Plugging this above we get  $\delta^2 \leqslant \frac{1}{k} + s$ , hence  $k \leqslant \frac{1}{\delta^2 - s}$ .

## 2.5 The Inductive Argument

Finally, we explain how to get Theorem 1.5 by induction on m. For that, we need the following generalization of Theorem 2.8.

**Theorem 2.13.** Suppose that  $B_0, B_{m-1}$  are tables that pass the (m-1)-dimensional space versus point test with probability at least  $\varepsilon \geqslant \frac{d^2}{q^{1/10}}$ . Then there exists a polynomial  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  of total degree d, such that

$$\Pr_{x \in \mathbb{F}_q^m} [f(x) = B_0(x)] \geqslant \varepsilon - \frac{d^{10}}{q^{1/10}}.$$

*Proof.* The argument is similar to the argument in Theorem 2.8, and we do not give the details. We remark that following the strategy therein, the bulk of the proof boils down to proving an analog of Theorem 2.1 for the (m-1)-dimensional affine subspace vs (m-1)-dimensional affine subspace test in  $\mathbb{F}_q^m$ , and the same analysis that we showed works. Therein, the main fact we used m=3 for is that random two planes in  $\mathbb{F}_q^3$  intersect, with high probability, on a line. In the current setting it is true that two randomly chosen (m-1)-dimensional affine subspaces in  $\mathbb{F}_q^m$  intersect, with high probability, in an affine subspace of dimension m-2.

We can now prove Theorem 1.5 by induction on m, restated below.

**Theorem 1.5 (Restated).** Suppose that  $B_0$ ,  $B_2$  are tables that pass the plane versus point test with probability at least  $\varepsilon \geqslant \frac{d^2}{a^{1/10}}$ . Then there exists a polynomial  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  of total degree d, such that

$$\Pr_{x \in \mathbb{F}_q^m} \left[ f(x) = B_0(x) \right] \geqslant \varepsilon - m \frac{d^{10}}{q^{1/10}}.$$

*Proof.* We prove by induction on m. For m=3, the statement is true from Theorem 2.8. Assume the statement for  $m\geqslant 3$ , and prove for m+1. Then we are working over  $\mathbb{F}_q^{m+1}$ . For each  $W\subseteq \mathbb{F}_q^{m+1}$  of dimension m, we may consider the plane versus point test there; let  $\varepsilon_W$  be the acceptance probability of it there, and note that  $\mathbb{E}_W\left[\varepsilon_W\right]=\varepsilon$ . By induction hypothesis, we may find  $f_W\colon W\to \mathbb{F}_q$  of degree d such that

$$\Pr_{x \in W} [f_W(x) = B_0(x)] \geqslant \varepsilon_W - m \frac{d^{10}}{q^{1/10}},$$

so we may define an assignment  $B_m$  that assigns to each m dimensional subspace  $W \in B_m(\mathbb{F}_q^{m+1})$  the function  $f_W$ , and get that  $B_0, B_m$  pass the m-dimensional subspace versus point test with probability

$$\mathbb{E}\left[\Pr_{x\in P\in S_2(W)}\left[f_W(x)=B_0(x)\right]\right]\geqslant \mathbb{E}\left[\varepsilon_W-m\frac{d^{10}}{q^{1/10}}\right]=\varepsilon-m\frac{d^{10}}{q^{1/10}}.$$

Applying Theorem 2.13 we find a polynomial  $f: \mathbb{F}_q^{m+1} \to \mathbb{F}_q$  of degree at most d satisfying that

$$\Pr_{x \in W \in \mathcal{S}_m(\mathbb{F}_q^{m+1})} \left[ B_0(x) = f(x) \right] \geqslant \left( \varepsilon - m \frac{d^{10}}{q^{1/10}} \right) - \frac{d^{10}}{q^{1/10}} = \varepsilon - (m+1) \frac{d^{10}}{q^{1/10}}.$$

# 2.6 Proof of the List Decoding Statement, Theorem 1.6

Proof of Theorem 1.6. Let  $f_1, \ldots, f_k$  be all degree d functions that agree with  $B_0$  on at least  $\delta$  fraction of points; by Claim 2.12,  $k \leq \frac{2}{\delta^2}$ , and we next perform a randomization argument as before. Let  $W_i \subseteq \mathbb{F}_q^m$  be the set of points on which  $f_i$  and  $B_0$  agree, and  $W = W_1 \cup \ldots \cup W_k$ . We claim that if we randomize the values of  $B_0$  on all  $x \in W$ , then with high probability the acceptance probability of the plane versus point test is at most  $10\delta$ . Indeed, with high probability after the randomization no degree d function agrees with  $B_0$  on more than  $2\delta$  fraction of points, and hence by Theorem 2.13 the plane versus point test passes with probability at most  $2\delta$ . Thus, it follows that before the randomization, except with probability  $2\delta$ , whenever the test passes,  $B_0$  agrees with at least one of the functions  $f_i$ .

Sample P, and let E be the event that  $f_j|_P = B_2[P]$  for some j. If E fails, then  $f_j|_P$  and  $B_2[P]$  agree on at most  $\frac{d}{q}$  of the points of  $x \in P$ , and so  $B_2[P](x) = f_j(x)$  for some j for at most  $\frac{dk}{q}$  fraction of points  $x \in P$ . Thus,

$$\Pr_{x \in P \in S_2(\mathbb{F}_q^m)} \left[ B_0(x) = B_2[P](x) \wedge \bar{E} \wedge \exists j B_0(x) = f_j(x) \right]$$

$$\leqslant \Pr_{x \in P \in S_2(\mathbb{F}_q^m)} \left[ \exists j, B_0(x) = B_2[P](x) = f_j(x) \mid \bar{E} \right]$$

$$\leqslant \frac{dk}{q}.$$

Hence,

$$\Pr_{x \in P \in S_2(\mathbb{F}_q^m)} \left[ B_0(x) = B_2[P](x) \land \bar{E} \right] \leqslant \Pr_{x \in P \in S_2(\mathbb{F}_q^m)} \left[ B_0(x) = B_2[P](x) \land \forall j B_0(x) \neq f_j(x) \right] + \frac{dk}{q},$$

which is at most  $2\delta + \frac{dk}{q} \geqslant 2\delta + \frac{2d}{q\delta^2} \leqslant 3\delta$ .

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lecture 9

#### Dor Minzer

In the last few lectures, we have described the sum-check protocol and low-degree testing problem, as well as proved the correctness of the sum-check protocol (under the promise the assignment is a low-degree polynomial), and the low-degree testing result in the 1% regime. Today, we will combine these two results in order to prove a PCP theorem with poly-logarithmically many queries.

## 1 A PCP with poly(log n) Queries

To formalize PCPs is in a combinatorial language, we use the language of constraint satisfaction graphs.

**Definition 1.1.** A instance of constraint satisfaction graph (abbreviated CSG) consists of sets of nodes  $X = \{x_1, \ldots, x_n\}$ , an alphabet  $\Sigma_i$  for each node  $x_i$ , a collection hyperedges E and a constraint  $C_e$  for each edge  $e \in E$ . For each edge  $e \in E$ , writing  $e = (x_{i_1}, \ldots, x_{i_s})$ , the constraint  $C_e$  can be any subset of  $\Sigma_{i_1} \times \ldots \times \Sigma_{i_s}$ ; these tuples are thought of as satisfying the constraint.

The alphabet size of an instance is  $\max_i |\Sigma_i|$ , and the number of queries is the size of the largest hyperedge in the graph.

Given an instance of CSG,  $\Psi=(X,E,\Sigma,\{C_e\}_{e\in E})$ , the goal is to find an assignment to the nodes that satisfies as many of the constraints as possible. Namely, find a labeling A of X such that for as many hyperedges  $e=(x_{i_1},\ldots,x_{i_s})$  as possible we have that  $(A(x_{i_1}),\ldots,A(x_{i_s}))\in C_e$ . The value of an instance  $\Psi$ , denoted by  $\mathrm{val}(\Psi)$ , is the maximum fraction of constraints that can be satisfied by any assignment A. Thus, in the problem gap-CSG[c,s] we are given an instance  $\Psi$  of CSG promised to either have  $\mathrm{val}(\Psi)\geqslant c$  or  $\mathrm{val}(\Psi)< s$ , and the goal is to distinguish between these two cases.

We will often refer to hardness results for CSG as PCP constructions, and to measure the efficiency of the PCP construction we will focus on the size of the alphabet, number of queries, completeness and soundness parameters it achieves. In this language, we show:

**Theorem 1.2** (PCP with poly-logarithmic number of queries). There are absolute constants c, C > 0 such that  $gap\text{-}CSG[1, 1/\log(n)^c]$  is NP-hard on instances with alphabet size and number of queries at most  $\log(n)^C$ .

The proof of Theorem 1.2 proceeds by a reduction. The starting point of the reduction is the problem  $\operatorname{gap-QS}_{q=\log(n)^{100},r=n}[1,\frac{1}{\sqrt{q}}]$  (which we proved to be NP-hard), and we let (X,E) be an instance of quadratic equations over field of size  $q=\log(n)^{100}$  (where n is the number of variables). We produce an instance  $\Psi$  of CSG in polynomial time as follows.

We choose  $d=|\mathbb{H}|=\log(n)$  and  $m=\frac{\log(n)}{\log\log(n)}$  in the linearized sum-check protocol and write  $X=\mathbb{H}^m$ . For each  $e\in E$ , we run the linearized sum-check protocol. Namely we have  $A_0\colon \mathbb{F}_q^m\to \mathbb{F}_q$  which is assumed to be the low-degree extension of an assignment of (X,E), and for each e we have an auxiliary table  $G_e$  which consists of all of the partial sum function needed by the sum-check protocol. Then the linearized sum-check protocol describes a collection tests in  $G_e$  and  $A_0$  that satisfies:

- 1. Each constraint contains two entries from  $A_0$ , and at most (m+1)d entries from  $G_e$ .
- 2. If  $A_0$  satisfies e, then all of them are satisfied,
- 3. Else, if  $A_0$  doesn't satisfy e and is a function of total degree at most d, then at most  $\frac{2md+1}{q}$  of the constraints hold.

Thus, we will think of the entries of  $A_0$  and all of the tables  $G_e$  as nodes in our CSG instance  $\Psi$ , and of the checks generated by the sum-check protocol as defining hyperedges and constraints on them. We are not done with the description of  $\Psi$ , though; we must enforce that the table  $A_0$  is a function of total degree d for our analysis of the linearized sum-check protocol to be of use. Towards this end, we will use our low-degree testers.

In addition to the table  $A_0$ , we will also have a table  $A_2$  which is supposed to consist of the restriction of  $A_0$  to all planes in  $\mathbb{F}_q^m$ . Namely, for each  $P \in S_2(\mathbb{F}_q^m)$ , we include a new node,  $A_2[P]$ , in  $\Psi$ , and the alphabet of this node corresponds to functions of total degree at most d over P.

Thus, our PCP will proceed as follows: we sample a test T in the linearized sum-check protocol. Recall that to do so, we sample an equation  $e \in E$  and the randomness as in the linearized sum-check protocol, and eventually check some quadratic equation in  $G_e$ ,  $A_0(\vec{i})$ ,  $A_0(\vec{j})$ ; suppose it is given as  $h(G_e, A_0(\vec{i}), A_0(\vec{j})) = 0$ . Upon generating this equation, we sample a plane P containing  $\vec{i}$  and  $\vec{j}$ , query  $A_2[P]$  and check that  $A_2[P](\vec{i}) = A_0(\vec{i})$ . Thus, overall the constraint we generate in  $\Psi$  makes both of these checks: i.e. it reads  $G_e$ ,  $A_0(\vec{i})$ ,  $A_0(\vec{j})$  and  $A_2[P]$  and checks that  $h(G_e, A_0(\vec{i}), A_0(\vec{j})) = 0$  and  $A_2[P](\vec{i}) = A_0(\vec{i})$ .

We have the following lemma, which establishes that Theorem 1.2 holds:

#### **Lemma 1.3.** The above PCP has the following properties:

- 1. Completeness: If (X, E) is satisfiable, then  $val(\Psi) = 1$ . Namely, there are tables  $\{G_e\}_{e \in E}$ ,  $A_0$  and  $A_2$  that satisfy the above checks with probability 1.
- 2. **Soundness:** If (X, E) is at most  $\varepsilon$  satisfiable, then  $val(\Psi) \leqslant O\left((2md/q + \varepsilon)^{1/3}\right)$ . Namely, any  $\{G_e\}_{e \in E}$ ,  $A_0$  and  $A_2$  satisfy at most fraction  $O\left((2md/q + \varepsilon)^{1/3}\right)$  of the constraints of  $\Psi$ .

*Proof.* The completeness is clear, and we move to the soundness.

For the soundness, suppose that we have  $\{G_e\}_{e\in E}$ ,  $A_0$  and  $A_2$  that pass all of the checks with probability at least  $\delta$ ; denote by E the event that the above checks work. Note that by properties of the sum-check protocol, when we sample a check as above, the distribution of each one of  $\vec{i}$  and  $\vec{j}$  is uniform over  $\mathbb{F}_q^m$ . Let  $\eta>0$  to be determined, and let  $k=\frac{2}{\eta^2}$ . Then by the low-degree testing theorem, we may find  $f_1,\ldots,f_k\colon \mathbb{F}_q^m\to \mathbb{F}_q$  of total degree at most d such that

$$\Pr_{\vec{i} \in P \in S_2(\mathbb{F}_n^m)} \left[ A_0(\vec{i}) = A_2[P](\vec{i}), \ \forall \ell A_2|_P \neq f_\ell|_P \right] \leqslant \eta.$$

We denote by E' the event that  $A_2[P] = f_\ell|_P$  for some  $\ell$ . Then we get that  $\Pr\left[E \wedge \bar{E}'\right] \leqslant \eta$ , and so  $\Pr\left[E \wedge E'\right] \geqslant \delta - \eta$ . It follows that there is  $\ell$ , such that the probability that replacing  $A_0$  by  $f_\ell$ , we get that the above checks are all satisfied with probability at least  $\frac{1}{k} \left(\delta - \eta\right) \geqslant \frac{(\delta - \eta)\eta^2}{2}$ .

However, since  $f_\ell$  is of total degree at most d the analysis of the linearized sum-check protocol says that it passes it with probability at most  $\frac{2md+1}{q}$  on equations of (X,E) which it doesn't satisfy, and by assumption there are at most  $\varepsilon$  equation that it satisfies, so overall we must have that

$$\frac{(\delta - \eta)\eta^2}{2} \leqslant \frac{2md + 1}{q} + \varepsilon.$$

Taking  $\eta = \delta/2$ , we conclude the result.

### 2 Formalizations of PCPs

As discussed in the first lecture of this course, one can view a PCP from several different equivalent perspectives. While they are equivalent, sometimes, depending on the context and application, it is more natural to view PCP in one of the views rather than another. For the majority of the course, we will stick to the combinatorial view, as formalized by constraint satisfaction graphs as above. You are encouraged, however, to think above what we've seen in the course so far in the different views, and establish the equivalence between them.

The combinatorial, constraint satisfaction view. In this lecture, we have chosen the combinatorial view in which a PCP construction is thought as a hypergraph. The nodes of the graph represent variables and each one of its edges is associated with a constraint on its nodes. The goal is to assign labels to the nodes of the graph so as to satisfy as many of the constraints as possible. The parameters of most interest here are the completeness (the fraction of constraints that can be satisfied in the YES case), the soundness (the fraction of constraints that can be satisfied in the NO case), the alphabet size, the number of queries (the number of alphabet symbols that need to be read to check constraints), and the instance size. In this language, we achieved perfect completeness, i.e. 1, soundness  $(\log n)^{-\Omega(1)}$ , alphabet poly $(\log n)$ , queries poly $(\log n)$  and polynomial instance size, i.e.  $n^{O(1)}$ .

The verifier view. Another view is the verifier view, wherein we think of some NP statement, and the verifier is given a proof  $\pi$ . The verifier selects randomly (in a correlated manner) a few locations in  $\pi$ , checks that they satisfy some constraint, and if so the verifier accepts (and otherwise the verifier rejects). One can define the same parameters as before, wherein the amount of random bits the verifier uses becomes an important parameter; this parameter is analogous to the logarithm of the number of edges in the graph in the combinatorial view.

The k-prover, verifier view. Finally, a third view of PCPs is when we have a polynomial time verifier which wants to be convinced of some NP statement, and towards this end the verifier can ask questions to k all powerful provers that cannot communicate with each other. In this view, one should think of the verifier as generating locations in a supposed proof  $\pi$ , but since the verifier does not have a proof, he can send each chosen location to one of the provers, and expect in return the value that was supposed to be in that location in  $\pi$ . One can again discuss various analogous parameters to before, and in particular the number of provers is the analog of the number of queries in the previous views.

#### 3 What's Ahead?

Theorem 1.2 is already a very substantial result in complexity theory. In fact, with some additional work one can use it towards constructing a quasi-polynomial size PCP with constantly many queries and constant alphabet size which can serve as the basis for many hardness of approximation results. The catch is that these results would not be NP-hardness result, since the transformation from Theorem 1.2 to the constant queries, constant alphabet size PCP would require a quasi-polynomial time reduction (i.e. time  $n^{\text{poly}(\log n)}$ ), so to be meaningful one would need to assume that NP has no quasi-polynomial time algorithms.

There are several avenues one may continue in their path of study in PCP, and below we outline a few topics that will be discussed in the upcoming weeks.

- 1. **Recursion:** One can think of the sequence of reductions (sum-check, low-degree testing) we did as a method that took us from a PCP with n queries over alphabet of size q (the gap version of Quadratic equations from the second lecture), to a PCP with  $\operatorname{poly}(\log n)$ , while incurring only small loses in the soundness of the PCP and polynomial size blowup in the size of the instance. One may hope that there is a way to recursively apply such process to get a PCP with  $\operatorname{poly}(\log\log n)$  queries, then  $\operatorname{poly}(\log\log\log n)$  and so on. This turns out to indeed be possible, analogously to the composition step we saw in error correcting codes.
  - Doing so though, requires several more ideas as well as a great deal of care. We will present the main ideas needed to carry out this composition, and in particular a technique called "aggregation of queries".
- 2. Reducing the number of queries to O(1): Once the number of queries in the PCP is sufficiently small (poly( $\log \log n$ ) will do) one can use a code with much worse rate more specifically the Hadamard code in order to reduce the number of queries to be constant. We will see this step in the next few lectures.
- 3. Applications in hardness of approximation: Once we have establish a PCP with constantly many queries and constant alphabet size, we will discuss some of their applications in hardness of approximation. First we will see some of the more basic applications of it (such as hardness of Clique and APX hardness of various problems), which will motivate the question of optimal hardness of approximation results. This will lead us to discuss extreme forms of the PCP theorem, and in particular we will discuss the parallel repetition theorem, the long-code framework and the Unique-Games Conjecture.

As discussed above then, for the next installment in the course we shall assume the following improved version of Theorem 1.2.

**Theorem 3.1** (PCP with poly-loglog number of queries). There are absolute constants C, c > 0 such that  $gap\text{-}CSG[1, 1/\log(n)^c]$  is NP-hard on instances with alphabet size  $poly(\log n)$  and number of queries at most  $(\log \log(n))^C$ .

Our focus on the next few lectures will be to deduce the following result, which is often referred to as the basic form of the PCP theorem:

**Theorem 3.2** (PCP with constantly many queries and constant alphabet). There is an absolute constant  $\varepsilon > 0$  such that  $gap\text{-}CSG[1, 1 - \varepsilon]$  is NP-hard on instances with alphabet size and number of queries at most O(1).

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lectures 10,11

#### Dor Minzer

In previous lectures we have proved a PCP theorem with poly-logarithmic number of queries; namely that gap-CSG $[1,1/\log(n)^c]$  is NP-hard on instances with alphabet size and number of queries that are both poly $(\log n)$ , where n is the size of the instance. As hinted earlier, there is a way to "recurse" and by that to take the number of queries further down to be doubly logarithmic and even triply logarithmic. How does one eventually achieve a PCP with constant number of queries, though? Today, we will assume a stronger (but similar) version of the result we have already proved, and use it to construct a PCP with constantly many queries.

#### 1 Overview

Our starting point today will be the following PCP construction.

**Theorem 1.1** (PCP with poly-loglog number of queries). There are absolute constants  $\varepsilon, C > 0$  such that  $gap\text{-}QS[1, 1 - \varepsilon]$  is NP-hard on instances with alphabet size O(1) and number of queries at most  $(\log \log(n))^C$ .

This theorem differs from the result we proved over the last few lectures in several aspects. First, the alphabet size here is O(1) instead of poly-logarithmic; this is not a significant difference, since we can represent a single alphabet symbol by  $\operatorname{poly}(\log\log n)$  many bits, thus decrease the alphabet size at the expense of increasing the number of queries by that factor. Secondly, in the last lecture we only achieved poly-logarithmic number of queries, and here we are assuming  $\operatorname{poly}(\log\log n)$  number of queries; this difference is more significant, and we will discuss it at a later point. Third, the soundness of our PCP is  $1-\varepsilon$  (i.e. close to 1) as opposed to close to 0. In this aspect, the result we are using here is weaker than the one we have proved. We are doing it so as to simplify the presentation, as working in regime in which the soundness bounded away from 1 is easier than working in the regime the soundness is close to 0. It is possible though to modify the ideas presented herein and establish a result with soundness close to 0.

We will use Theorem 1.1 to prove:

**Theorem 1.2** (PCP with a constant number of queries). There is an absolute constant  $\varepsilon > 0$  such that  $gap\text{-}CSG[1, 1 - \varepsilon]$  is NP-hard on instances with alphabet size O(1) and number of queries O(1).

Towards this end, we will first introduce a construction that doesn't work but will be helpful for us in conveying some of the ideas that go into the proof. We will then identify an additional structural property that we could hope to get from the instances from Theorem 1.1, and then modify our construction so that it is indeed correct assuming this additional property. We will discuss this additional property and a transformation that allows us to guarantee it in subsequent lectures.

#### 2 Hadamard and Quadratic Hadamard Codes

Suppose we have an instance (X, E) of quadratic solvability as in Theorem 1.1; thus, we have variables  $x_1, \ldots, x_n$  that are to be assigned values from  $\mathbb{F}_q$ , and equations  $e_1, \ldots, e_m$  each containing at most  $s = \text{poly}(\log\log n)$  many variables. We know that in the YES case, there is an assignment  $A: X \to \mathbb{F}_q$  satisfying all equations, and in the NO case each assignment A satisfies at most  $\delta = 1/\log(n)^c$  of the equations. We want to encode the assignment A in a different way, so that by making O(1) queries into the encoding we can check whether the encoded A satisfies  $e_i$ , and for that we are going to use the *quadratic Hadamard code* that you have already seen in the problem set.

#### 2.1 The Hadamard Code

Recall that the Hadamard code over  $\mathbb{F}_q$  is defined as follows:

**Definition 2.1.** For  $v \in \mathbb{F}_q^s$ , we define the Hadamard Encoding of v as the truth table of the function  $h_v \colon \mathbb{F}_q^s \to \mathbb{F}_q$  defined by

$$h_v(y) = \langle v, y \rangle$$
.

In words, for each vector  $v \in \mathbb{F}_q^s$  we consider the linear function  $h_v(y) = \langle v, y \rangle$ , and the truth table of  $h_v$  is the Hadamard encoding of the vector v. It is easy to prove that the Hadamard code is a linear error correcting code and has relative distance 1 - 1/q. Note that if we wish to encode a vector of length s, then the length of the encoding of v is  $q^s$ , i.e. exponential in s. Thus, we can afford to use such encodings only if  $q^s$  is at most polynomially large in n, which is the reason we would like to apply the Hadamard code only to encode strings of length at most  $s = O(\log n)$ ; in our case, the strings will be of length  $s = \operatorname{poly}(\log \log n)$ .

The Hadamard code is locally testable. Indeed, note that if  $h_v$  is a legitimate Hadamard codeword, then  $h_v(x+y)=h_v(x)+h_v(y)$ , which suggests the following randomized local test for the Hadamard. Given a table of values  $f\colon \mathbb{F}_q^s\to \mathbb{F}_q$  which is supposed to be an Hadamard encoding of some vector v, perform the following test, which we call the linearity test:

- 1. Pick  $x, y \in \mathbb{F}_q^s$  uniformly.
- 2. Query f(x), f(y) and f(x+y).
- 3. Accept if f(x + y) = f(x) + f(y).

The following lemma asserts that correctness of the test:

**Lemma 2.2.** Suppose that  $f: \mathbb{F}_q^s \to \mathbb{F}_q$  passes the linearity test with probability at least  $1 - \varepsilon$  for  $\varepsilon < 1/8$ . Then, there exists  $v \in \mathbb{F}_q^s$ , such that

$$\Pr_{x \in \mathbb{F}_q^s} \left[ f(x) = h_v(x) \right] \geqslant 1 - 2\varepsilon.$$

*Proof.* The proof is identical to the proof shown earlier in the course for q=2. One defines

$$g(x) = \mathsf{majority}_{y \in \mathbb{F}_q^s} f(x+y) - f(y)$$

and shows that  $\Pr_{x \in \mathbb{F}_q^s}[f(x) = g(x)] \geqslant 1 - 2\varepsilon$ , and that provided that  $\varepsilon < 1/8$ , g passes the linearity test with probability 1, in which case g can easily be seen to be a Hadamard codeword.

The last important feature of the Hadamard code is that it enables us to verify linear constraints on the encoded vector v. Indeed, suppose we had some vector of coefficients  $\alpha_1, \ldots, \alpha_s$  and we want to test that  $\sum_{i=1}^s \alpha_i v_i = c$ . How can we do it using the Hadamard encoding of v?

Well, if we have the legitimate Hadamard encoding of v, namely  $h_v$ , the above constraint can simply be re-written as  $h_v(\vec{\alpha}) = c$  where  $\vec{\alpha} = (\alpha_1, \dots, \alpha_s)$ . In our situation though, we will have oracle access to a table  $f: \mathbb{F}_q^s \to \mathbb{F}_q$  that we can only guarantee to be close to a table of a legitimate Hadamard codeword  $h_v$ . Thus, it could be the case that the input  $\vec{\alpha}$  just happens to be one of the inputs in which f and  $h_v$  differ. Can we verify the linear constraint on v despite of that?

Instead of directly asking for the value of f at  $\vec{\alpha}$ , we can use self correction! Namely, we can sample  $x \in \mathbb{F}_q^s$  uniformly, and then observe that each one of the inputs x and  $x + \vec{\alpha}$  is distributed uniformly on  $\mathbb{F}_q^s$ , hence we expect f and  $h_v$  to agree on them. Then, we can read off f(x) and  $f(x + \vec{\alpha})$ , and check that  $f(x + \vec{\alpha}) - f(x) = c$ . The idea is that with high probability over x,  $f(x + \vec{\alpha}) - f(x) = h_v(x + \vec{\alpha}) - h_v(x) = h_v(\vec{\alpha})$ , hence this test will pass only if v satisfies the linear constraint.

Summarizing, we state the following tester for the Hadamard codeword which enables us to check whether a given table f is close to a Hadamard codeword, and if the nearby codeword satisfies a given linear constraint. The input to the test is an oracle access to  $f: \mathbb{F}_q^s \to \mathbb{F}_q$ , as well as a vector of coefficients  $\vec{\alpha} \in \mathbb{F}_q^s$  and  $c \in \mathbb{F}_q$ , and we want to test if f is close to some Hadamard codeword  $h_v$  that satisfies that  $\langle \vec{\alpha}, v \rangle = c$ .

- 1. Sample  $x, y \in \mathbb{F}_q^s$  uniformly and check that f(x+y) = f(x) + f(y).
- 2. Query  $f(x + \vec{\alpha})$  and check that  $f(x + \vec{\alpha}) f(x) = c$ .

We summarize the above discussion with the following lemma.

**Lemma 2.3.** Suppose  $f: \mathbb{F}_q^s \to \mathbb{F}_q$ ,  $\vec{\alpha}$  and c are such that the above test accepts with probability at least  $1 - \varepsilon$ , for  $\varepsilon < 1/8$ . Then there exists  $v \in \mathbb{F}_q^s$  such that

- 1. v satisfies the linear constraint:  $\langle \vec{\alpha}, v \rangle = c$ .
- 2. f is close to  $h_v$ :  $\Pr_{x \in \mathbb{F}_q^s} [f(x) = h_v(x)] \ge 1 2\varepsilon$ .

Proof. Left to the reader.

Thus, the Hadamard code only incurs an exponential blow-up in the size of the encoding, and it allows us to check linear constraints in the encoded values. This almost fits what we need in order to go from Theorem 1.1 to Theorem 1.2, except that there we need to be able to check quadratic constraints in the encoded values. In the next section we show a variant of the Hadamard code which enables us to do that.

#### Remark 2.4. A few remarks are in order.

- 1. Notice that while the linearity tester required only 3 queries, in order to check a linear constraint we required an additional query. There are ways to incorporate the linear constraint check into the linearity tester so that to keep the number of queries to be 3; this is not very important for us now as this difference will be minor, but there are some applications in which such ideas are crucial.
- 2. As discussed, there are analogs the above ideas and in particular of Lemma 2.2, in the low-soundness regime. Roughly speaking, such results are concerned with the case the field size q is though of as somewhat large, and consider the case that f passes the linearity test with probability at least  $1/q + \varepsilon$ . In such cases, one proves a list decoding statement, saying that there is a list  $v_1, \ldots, v_k$

where  $k = k(\varepsilon) \in \mathbb{N}$  that "explains" all of the success probability of the test. Namely, the probability that f(x+y) = f(x) + f(y) but f disagrees with each one of  $h_{v_i}$  on at least one of  $\{x, y, x+y\}$  is very small. Incorporating the linearity checks requires more effort.

#### 2.2 The Quadratic Hadamard Code

The quadratic Hadamard code is defined as:

**Definition 2.5.** For  $v \in \mathbb{F}_q^s$  we define the quadratic Hadamard encoding of v as the truth table of the function  $Qh_v \colon \mathbb{F}_q^{s^2} \to \mathbb{F}_q$  defined by

$$Qh_v(y) = h_{v \otimes v}(y) = \langle v \otimes v, y \rangle$$
,

where  $v \otimes v \in \mathbb{F}_q^{s^2}$  is the vector whose i, j entry is  $v_i v_j$ .

One way to think about the quadratic Hadamard code is that it is a subset of the Hadamard code of vectors of length  $s^2$ , corresponding only to vectors of the form  $v \otimes v$ . We will want to show that we can still locally test the quadratic Hadamard code, and that it enables us to verify quadratic constraints in v. We also remark that as the size of the encoding of a string of length s is  $q^{s^2}$ , we will want to use the Hadamard encoding only on strings whose length is at most  $O(\sqrt{\log n})$ , and for us it will be the case that  $s = \mathsf{poly}(\log\log n)$ .

Suppose we have oracle access to a functions  $f \colon \mathbb{F}_q^s \to \mathbb{F}_q$  and  $Qf \colon \mathbb{F}_q^{s^2} \to \mathbb{F}_q$  which are supposed to be the Hadamard and the quadratic Hadamard encoding of some  $v \in \mathbb{F}_q^s$ . Suppose, in addition, we have a quadratic constraint  $\sum_{i,j} \alpha_{i,j} v_i v_j = c$  on the v's. How can we test that f and Qf are indeed such functions, and that v satisfies the quadratic constraint?

By the previous discussion, we can already perform a test to guarantee that f and Qf are close to Hadamard codewords of some vectors. Indeed, our tester begins by:

- 1. Run the linearity tester on f: namely, sample  $x,y\in\mathbb{F}_q^s$  check that f(x+y)=f(x)+f(y), else reject.
- 2. Run the linearity tester on f: namely, sample  $x', y' \in \mathbb{F}_q^{s^2}$  check that Qf(x'+y') = Qf(x') + Qf(y'), else reject.

By Lemma 2.2, if f and Qf pass this test with probability at least  $1-\varepsilon$  where  $\varepsilon<1/8$ , then there are  $v\in\mathbb{F}_q^s$  and  $u\in\mathbb{F}_q^s$  such that f is  $2\varepsilon$ -close to  $h_v$  and qf is  $2\varepsilon$ -close to  $h_u$ . Next, we would like to test that  $u=v\otimes v$ , and for that we begin with the basic observation that

$$h_{v \otimes v}(x \otimes y) = \langle v \otimes v, x \otimes y \rangle = \langle v, x \rangle \langle v, y \rangle = h_v(x)h_v(y),$$

hence we get a potential connection that we should test. Namely, this suggests test to test that  $u = v \otimes v$ , we would like to check that  $h_u(x \otimes y) = h_v(x)h_v(y)$ , and we will indeed do that. There is one catch: the vector  $x \otimes y$  is not uniformly distributed over  $\mathbb{F}_q^{s^2}$ , so if we attempt to access the value of  $h_u$  on it by directly querying Qf on that point, it may be the case that this is a location in which  $h_u$  and Qf differ. To overcome this, we use local correction again, and get the tensor tester:

- 1. Sample  $x, y \in \mathbb{F}_q^s$  and  $z \in \mathbb{F}_q^{s^2}$  uniformly.
- 2. Check that  $Qf(z + x \otimes y) Qf(z) = f(x)f(y)$ , else reject.

We have the following lemma.

**Lemma 2.6.** Suppose that  $f: \mathbb{F}_q^s \to \mathbb{F}_q$  and  $Qf: \mathbb{F}_q^{s^2} \to \mathbb{F}_q$  are functions that succeed with probability at least  $1 - \varepsilon$  in the linearity tester and the tensor tester, and  $\varepsilon \leqslant \frac{1}{100}$ . Then there is  $v \in \mathbb{F}_q^s$  such that f is  $2\varepsilon$  close to  $h_v$ , and Qf is  $2\varepsilon$  close to  $h_{v \otimes v}$ .

*Proof.* From Lemma 2.2 there are  $v \in \mathbb{F}_q^s$  and  $u \in \mathbb{F}_q^{s^2}$  such that f is  $2\varepsilon$ -close to  $h_v$  and Qf is  $2\varepsilon$ -close to  $h_u$ . Note that with probability at least  $1-8\varepsilon$  it holds that  $Qf(z+x\otimes y)=h_u(z+x\otimes y), Qf(z)=h_u(z), f(x)=h_v(x), f(y)=h_v(y)$ , so

$$\Pr_{x,y\in\mathbb{F}_q^s}[h_v(x)h_v(y)=h_u(x\otimes y)]\geqslant 1-9\varepsilon.$$

However, note that if  $u \neq v \otimes v$ , then the functions  $P(x,y) = h_v(x)h_v(y)$  and  $Q(x,y) = h_u(x \otimes y)$  are distinct functions over  $\mathbb{F}_q^{2s}$  of individual degree 1 and total degree 2, hence by Schwarz-Zippel they disagree on randomly chosen x,y with probability at least  $(1-1/q)^2 > 9\varepsilon$ . It follows that we must have that  $u = v \otimes v$ .

Recall that in the last section, we saw that if we have oracle access to a table g that is close to a Hadamard function  $h_u$ , then we can check linear equations in u. In our situation, we have access to a table Qf that is close to a Hadamard function  $h_{v\otimes v}$ , hence we can check linear equations in  $v\otimes v$ , which are simply quadratic equations in v. Thus, we reach our final tester. The tester gets oracle access to tables  $f: \mathbb{F}_q^s \to \mathbb{F}_q$  and  $Qf: \mathbb{F}_q^{s^2}$  as well as a vector of coefficients  $\vec{\alpha} \in \mathbb{F}_q^{s^2}$  and  $c \in \mathbb{F}_q$ ; the tester needs to verify that for some  $v \in \mathbb{F}_q^s$ , f is close to  $h_v, Qf$  is close to  $h_{v\otimes v}$  and that  $\langle \vec{\alpha}, v \otimes v \rangle = c$ .

- 1. Run the linearity tester on f and Qf:
  - (a) Sample  $x, y \in \mathbb{F}_q^s$  and  $x', y' \in \mathbb{F}_q^{s^2}$  uniformly.
  - (b) Check that f(x+y) = f(x) + f(y) and Qf(x'+y') = Qf(x') + Qf(y'), else reject.
- 2. Run the tensor tester:
  - (a) Sample  $x, y \in \mathbb{F}_q^s$  and  $z \in \mathbb{F}_q^{s^2}$  uniformly.
  - (b) Check that  $Qf(z + x \otimes y) Qf(z) = f(x)f(y)$ , else reject.
- 3. Run the self-correction constraint tester:
  - (a) Sample  $x \in \mathbb{F}_a^{s^2}$  uniformly.
  - (b) Check that  $Qf(x + \vec{\alpha}) Qf(x) = c$ , else reject.

The following lemma summarizes the properties of the above tester.

**Lemma 2.7.** Suppose that  $f: \mathbb{F}_q^s \to \mathbb{F}_q$  and  $Qf: \mathbb{F}_q^{s^2} \to \mathbb{F}_q$  are functions that succeed with probability at least  $1 - \varepsilon$  in the linearity + tensor + constraint tester, and  $\varepsilon \leqslant \frac{1}{100}$ . Then there is  $v \in \mathbb{F}_q^s$  such that f is  $2\varepsilon$  close to  $h_v$ , and Qf is  $2\varepsilon$  close to  $h_{v \otimes v}$ , and  $\langle \vec{\alpha}, v \otimes v \rangle = c$ .

*Proof.* From Lemma 2.6 it follows that f and qf are  $2\varepsilon$ -close to  $h_v$  and  $h_{v\otimes v}$  for some  $v\in\mathbb{F}_q^s$ , hence with probability at least  $1-5\varepsilon>0$  over x,

$$c = Qf(x + \vec{\alpha}) - Qf(x) = h_{v \otimes v}(x + \vec{\alpha}) - h_{v \otimes v}(x) = \langle \vec{\alpha}, v \otimes v \rangle,$$

so v satisfies the quadratic constraint.

## 3 Going from Theorem 1.1 to Theorem 1.2 via the Quadratic Hadamard Code?

#### 3.1 Composing with the Hadamard Code

The ideas presented in the lecture so far suggest the following way of deducing Theorem 1.2 from Theorem 1.1. Start with an instance of quadratic equations (X, E) as in Theorem 1.1, let q = O(1) be the field size, and write  $X = \{x_1, \ldots, x_n\}$ ,  $E = \{e_1, \ldots, e_m\}$ . For each equation  $e_i$ , consider the set of variables  $X_i \subseteq X$  that appear in it, and use the Hadamard and quadratic Hadamard encodings to encode the (supposed) assignment  $A \colon X \to \mathbb{F}_q$  on these variables. For convenience, instead of thinking of the supposed A as an assignment, we think of it as a vector  $\vec{v} \in \mathbb{F}_q^X$ .

Namely, our witness will be a collection of assignments  $f_i \colon \mathbb{F}_q^{X_i} \to \mathbb{F}_q$ ,  $Qf_i \colon \mathbb{F}_q^{X_i^2} \to \mathbb{F}_q$ , and our intention is that  $f_i$ ,  $Qf_i$  are the Hadamard and quadratic Hadamard encodings of  $\vec{v}|_{X_i}$ . Thus, we think of the nodes of our CSG as the locations of the tables of these functions, and we use the tester above to define a set of constraints in order to verify it:

- 1. Sample  $i \in \{1, ..., m\}$ .
- 2. Run the linearity tester on  $f_i$ ,  $Qf_i$ .
- 3. Run the tensor tester on  $f_i$ ,  $Qf_i$
- 4. Run the self-correction constraint tester on  $f_i$ ,  $Qf_i$  to check the equation  $e_i$ . Namely, write  $e_i$  as  $\langle \alpha_i, v | X_i \rangle = c_i$ , and run the self-correction constraint tester on  $f_i, Qf_i$  with  $\alpha_i$  and  $c_i$ .

We note that the run-time of the reduction is  $O(m \cdot q^{\max_i |X_i|^2})$ , which is polynomial in n (this is the reason that we needed to go down to polyloglog many queries). We also note that overall, each constraint only looks at O(1) locations.

Using Lemma 2.7, one can analyze this PCP construction and show (roughly speaking) that for sufficiently small  $\delta > 0$ , if  $\{f_i, Qf_i\}_{i=1,\dots,m}$  pass this test with probability at least  $1-\delta$ , then one can find a collection of vectors  $v_i \in \mathbb{F}_q^{X_i}$  such that  $f_i, Qf_i$  are  $2\delta$ -close to the Hadamard and quadratic Hadamard encodings of  $v_i$ , and that  $v_i$  satisfies the equation  $e_i$ . This seems good, except that there is one issue: how do we make sure that the vectors  $v_i$  are consistent? Namely, suppose we had some variable x which is both in  $X_i$  as well as in  $X_i$ ; how do we make sure that it receives the same value in both  $v_i$  and  $v_i$ ?

To address that, one may try to use the Hadamard and quadratic Hadamard encodings to encode the entire vector  $\vec{v}$ ; this works but then the runtime of the reduction is  $2^{\theta(n^2)}$  (and for this, one doesn't need much of what we've done in the course thus far). To remedy the situation we need our initial quadratic solvability instance to have the *block property*.

#### 3.2 The Block Property

We need more structure from the PCP given to us in Theorem 1.1, and the specific structure we look for is called the block property. This additional feature can be guaranteed by a technique we have yet to see called "aggregation of queries", and we defer the discussion on how to achieve it to a later point.

Roughly speaking, the block property addresses the structure of the queries the PCP makes (in this case, the structure of the variables  $x_i$ 's that an equation depends on), and says that while the total number of these variables can be quite large (poly-logarithmic or doubly logarithmic), they can be read by looking into only much fewer number of "blocks" in the witness (typically constantly many).

Below, we specialize the discussion to quadratic equations, but the definition easily extends to general constraint satisfaction graph problems. We say an instance (X, E) of quadratic equations has the (k, s)-block property if the set of variables X can be partitioned into disjoint sets  $X_1 \cup \ldots \cup X_{n'}$  such that  $|X_i| \leq s$  for each i, each one of the equations  $e_j$  contains variables from most k of the blocks  $X_i$  and the variables of each monomial in  $e_j$  appear in the same block. Furthermore, this partition is given as part of the input. We remark that in this definition, k should be thought of as a constant, say 10, and s should be thought of as small but super constant, say poly(log log n).

With this definition in mind, we now state the variant of Theorem 1.1 that we will use:

**Theorem 3.1** (PCP with poly-loglog number of queries). There are absolute constants  $\varepsilon$ , C > 0 and  $k \in \mathbb{N}$  such that  $gap\text{-}QS[1, 1 - \varepsilon]$  is NP-hard on instances with alphabet size O(1) satisfying the (k, s)-block property for  $s = \text{poly}(\log \log n)$ .

We now prove Theorem 1.2 using Theorem 3.1, and the idea similar to the one from the previous section. Let (X,E) be an instance of quadratic solvability as in Theorem 3.1, and let  $X_1 \cup \ldots \cup X_{n'}$  be a partition of X into blocks as in the (k,s)-block property. For each  $i=1,\ldots,n'$ , we have a pair of functions  $f_i\colon \mathbb{F}_q^{X_i}\to \mathbb{F}_q$  and  $Qf_i\colon \mathbb{F}_q^{X_i^2}\to \mathbb{F}_q$ . The intention is that if  $v\in \mathbb{F}_q^X$  is a vector representing a solution to (X,E), then  $f_i,Qf_i$  will be the Hadamard and the quadratic Hadamard encodings of  $v|_{X_i}$ .

The locations of the tables  $f_i$ ,  $Qf_i$  together constitute the vertices of the CSG we construct  $\Psi$ , and we next describe the constraints of  $\Psi$ .

We sample an equation  $j \in \{1, ..., m\}$  and take the blocks  $i_1, ..., i_k$  that equation  $e_j$  depends on. We perform the linearity and tensor testers on  $f_i, Qf_i$  for each  $i \in \{i_1, ..., i_k\}$ ; then, thinking of the equation  $e_j$  as  $\langle \alpha_j, v \otimes v \rangle = c_j$ , we set  $\alpha_{j,i} = \alpha_j|_{X_i^2}$ , i.e. the coefficients of  $\alpha$  that are associated with monomials in  $X_i$ , and use local correction to "read off"  $Qf_i(\alpha_{j,i})$ , and check that these values add up to  $e_j$ . More precisely:

- 1. Sample  $j \in \{1, ..., m\}$ , and let  $i_1, ..., i_k$  be the k-blocks the equation  $e_j \in E$  depends on. Let  $\alpha_j$  be its vector of coefficients.
- 2. Run the linearity tester on  $f_i, Qf_i$  for all  $i \in \{i_1, \dots, i_k\}$ .
- 3. Run the tensor tester on  $f_i$ ,  $Qf_i$  for all  $i \in \{i_1, \dots, i_k\}$ .
- 4. Run the self-correction constraint tester on  $f_i$ ,  $Qf_i$  for all  $i \in \{i_1, \ldots, i_k\}$  to "read off"  $Qf_i(\alpha_{j,i})$ . Namely, for each  $i \in \{1, \ldots, i_k\}$  let  $\alpha_{j,i} = \alpha_j|_{X_i^2}$ , select  $x \in \mathbb{F}_q^{X_i^2}$  randomly and take  $a_i = Qf_i(x + \alpha_{j,i}) Qf_i(x)$ .
- 5. Check that  $\sum_{i \in \{i_1, \dots, i_k\}} a_i = c_j$ .

We note that the total number of queries made in the above test is 3k + 4k + 2k = O(k) = O(1), so we have our desired number of queries. It is also clear that the reduction is polynomial time.

The following lemma shows the correctness of the reduction, thereby finishing the proof of Theorem 1.2.

**Lemma 3.2.** Let (X, E) be a quadratic solvability instance satisfying the (k, s)-block property, and consider the constraint satisfaction graph problem  $\Psi$  constructed above. Then for all  $\varepsilon > 0$  there is  $\delta = \delta(k, \varepsilon) > 0$  such that the following holds:

- 1. If (X, E) is fully satisfiable, then  $\Psi$  is fully satisfiable.
- 2. If (X, E) is at most  $(1 \varepsilon)$ -satisfiable, then  $\Psi$  is at most  $(1 \delta)$ -satisfiable.

*Proof.* For the first item, if (X, E) is satisfiable, then we take a satisfying assignment  $v \in \mathbb{F}_q^X$  and set  $f_i, Qf_i$  to be the Hadamard and quadratic Hadamard encoding of  $v|_{X_i}$  for all i; then the above tester passes with probability 1.

For the second item, we choose  $\delta = \min\left(\frac{\varepsilon^2}{100}, \frac{1}{(2k+1)^2}\right)$  and assume counter-positively that there are  $f_i, Qf_i$  that pass this test with probability at least  $1 - \delta$ . We show how to construct an assignment to (X, E) that satisfies at least  $1 - \sqrt{\delta} > 1 - \varepsilon$  of the equations, and contradiction.

For each  $i=1,\ldots,k$ , consider  $f_i$  and choose  $v_i\in\mathbb{F}_q^{X_i}$  such that the function  $h_{v_i}$  is closest to  $f_i$  among all functions of the form  $h_v$  (if there are ties, break them arbitrarily). Thus, we have the vectors  $v_1,\ldots,v_k$ , and using them we can define an assignment  $A\colon X\to\mathbb{F}_q$  where  $A(x)=v_i(x)$  if  $x\in X_i$ ; note that this is well defined since the  $X_i$ 's are disjoint. In the rest of the argument, we show that the assignment A satisfies at least  $1-\sqrt{\delta}$  of the equations of (X,E).

By an averaging argument, for at least  $1-\sqrt{\delta}$  fraction of the j's, once we fix j the test passes with probability at least  $1-\sqrt{\delta}$ , and we show that A satisfies  $e_j$  for each such j. Indeed, fix such j; then we get that as the linearity tester+tensor tester pass on each one of  $i=i_1,\ldots,i_k$  with probability at least  $1-\sqrt{\delta}$ , Lemma 2.6 implies there is  $u_i$  such that  $f_i$  is  $2\sqrt{\delta}$ -close to  $h_{u_i}$  and  $Qf_i$  is  $2\sqrt{\delta}$ -close to  $h_{u_i\otimes u_i}$ .

By the choice of  $v_i$  as we must have that  $v_i = u_i$ . Indeed, otherwise as  $h_{v_i}$  is (1 - 1/q)-far from  $h_{u_i}$ , it is at least  $1 - 1/q - 2\sqrt{\delta} > 2\sqrt{\delta}$  far from  $f_i$  in contradiction to it being the closest.

Thus, with probability at least  $1 - 2k\sqrt{\delta}$  we have that  $Qf_i(x + \alpha_{j,i}) = h_{v_i \otimes v_i}(x + \alpha_{j,i})$  and  $Qf_i(x) = h_{v_i \otimes v_i}(x)$  for all i in the last step, so with probability at least  $1 - (2k+1)\sqrt{\delta}$  we get the  $a_i$ 's there sum up to  $c_j$  and

$$a_i = Qf_i(x + \alpha_{j,i}) - Qf_i(x) = h_{v_i \otimes v_i}(x + \alpha_{j,i}) - h_{v_i \otimes v_i}(x) = h_{v_i \otimes v_i}(\alpha_{j,i}).$$

Summing over i gives that with probability at least  $1 - (2k+1)\sqrt{\delta} > 0$  we have

$$c_j = \sum_{i \in \{i_1, \dots, i_k\}} a_i = \sum_{i \in \{i_1, \dots, i_k\}} a_i = h_{v_i \otimes v_i}(\alpha_{j,i}),$$

implying that A satisfies the equation  $e_i$ .

### 4 The Composition Technique

The idea we presented here is an instantiation of a technique called composition, which is analogous to composition (concatenation) of error correcting codes. We started with a PCP with relatively large number of queries, which will be referred to as the "outer PCP" and composed it with a PCP with much fewer queries which will be referred to as the "inner PCP". In our case, the outer PCP was the PCP construction from Theorem 3.1, and inner PCP was the inefficient PCP that can be constructed using the Hadamard code. For our overall construction to be efficient though, we made sure to use the inner PCP only on small enough pieces, and the main gain is that the number of queries is basically inherited from the inner PCP.

At a high level, our composed PCP construction wanted to check that some constraint in the outer PCP was satisfied (a quadratic equation), and to do that we needed to "push down" this check to the language of the inner PCP (in our case, the quadratic Hadamard code enables us to check quadratic equations).

Composition of PCPs is one of the most important ideas in PCP theory; for example, going from the poly(log n)-query PCP theorem we have already proved to Theorem 1.1 amounts to composing PCPs too; in that case, it is a composition of the algebraic PCP (i.e. the one constructed via sum-check and low-degree testing) with itself.

As seen here, to facilitate composition one needs to have the block property, and in the next lecture we will discuss the aggregation of queries technique that achieves that.

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lecture 12

#### Dor Minzer

In this lecture, we will present a transformation on PCPs called aggregation of queries. This technique enables one to achieve the block property which we used in the last few lectures in order to perform composition of PCPs.

# 1 Aggregation of Queries

Suppose that we have a PCP construction with s queries, namely that we know that  $\operatorname{gap-CSG}[1,1-\varepsilon]$  is NP-hard on instances with s queries and alphabet  $\Sigma=\{0,1\}$  (you should think of s as  $\operatorname{poly}(\log n)$ ). We recall that an instance of this problem is an s-uniform hypergraph H=(V,E) along with a collection of constraints on the edges  $\{C_e\}_{e\in E}$ . A constraint  $C_e$  is a collection of tuples  $(a_1,\ldots,a_s)\in\Sigma^s$  that are considered satisfactory, and the goal is to find an assignment  $A\colon V\to\Sigma$  that satisfies as many of the constraints as possible, i.e. that maximizes

$$|\{e = (v_1, \dots, v_s) \in E \mid (A(v_1), \dots, A(v_s)) \in C_e\}|.$$

It is easy to see that all of the PCP constructions and tests we constructed in this course can be formalized in this way, and in particular the poly( $\log n$ ) query PCP we constructed.

The idea of aggregation of queries is to enlarge the set of vertices of the graph, so that for each edge  $e \in E$ , there will be a vertex  $v_e$  in the graph whose label will encode together the labels of all of the vertices in e. Thus, verifying the constraint on e will only require us to read the label of  $v_e$ .

One simple way to do that is to consider the following construction: define the bi-partite graph G whose vertices are  $(V \cup V', E')$ , where V is the original set of vertices of H and in V' we have a vertex  $v_e$  for each edge  $e \in E$ . We connected v and  $v_e$  by an edge if v is a vertex in the edge e in H. The alphabets of the CSG defined on G are  $\Sigma$  on V, and  $\Sigma_2$  on V' where for each  $v_e$  we interpret a symbol from the alphabet as some tuple from  $C_e$  (i.e., as an assignment that satisfies e). The constraints on G are  $\Phi_{v,v_e}$ , and given the label  $\sigma$  of v and v of v of v equal to v in v of in v in v of the label assigned to v in the value v of the value v of the value v of the value v of the label assigned to v in the value v of the value v of the label assigned to v in the value v of the value v of the value v of the value v of the label assigned to v in the value v of the value v of the value v of the value v of the value v of the value v of the value v of the value v of the value v of the value v of the value v of the value v of the value v of the value v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v of v o

The issue with this approach is that we need to more effectively enforce that the new witness locations packing the values assigned to all the vertices in v are globally consistent, in the sense that a vertex v appearing in two different edges would be assigned the same value by them.

We resolve this issue by taking utilizing the idea of low-degree extensions and low-degree testing, again. In particular, we will think of the assignments to  $v_e$  as projections of low-degree polynomials over a large space and perform low-degree extensions to ensure global consistency of all of these polynomials.

## 1.1 Packing Into Curves

Let n=|V|, and identify V with  $\mathbb{H}^m$  where  $\mathbb{H}$  is a subset of a field  $\mathbb{F}_q$  of size  $h=|\mathbb{H}|=\log n, m=\frac{\log n}{\log\log n}$ , and the field size q is  $\log^{100} n$ . Thus, we can identify an assignment  $A\colon V\to \{0,1\}$  with an assignment  $A\colon \mathbb{H}^m\to \{0,1\}$ , and then consider its low-degree extension  $A_{\text{extension}}\colon \mathbb{F}_q^m\to \{0,1\}$  which is multivariate polynomial of individual degree at most h.

Our new CSG will contain, as part of it, locations for each entry of  $A_{\text{extension}}$ , and in particular we will want to design a test that ensures that a given table f of values is close to a truth table of a low-degree function. We have already seen how to solve this issue using the plane versus point encoding and the plane versus point test, so we may assume that f is close to a function of total degree at most mh.

Next, we will want to pack all of the values of the assignment A that are given to an edge  $e \in E$  into a single table. Fix an edge  $e \in E$ , and let  $v_1, \ldots, v_s \in \mathbb{H}^m$  be all of vertices of H that are in e. We intend to pack  $v_1, \ldots, v_g$  into a single curve, defined as follows:

**Definition 1.1.** A curve  $\gamma \colon \mathbb{F}_q \to \mathbb{F}_q^m$  is a tuple of univariate polynomials, i.e.  $\gamma(t) = (\gamma_1(t), \dots, \gamma_m(t))$ . The degree of a curve  $\gamma$  is  $\deg(\gamma) = \max_i \deg(\gamma_i)$ .

We have the following basic interpolation claim.

**Claim 1.2.** Let  $a_1, \ldots, a_s \in \mathbb{F}_q$  be distinct, and  $v_1, \ldots, v_s \in \mathbb{F}_q^m$ . Then there is a curve  $\gamma \colon \mathbb{F}_q \to \mathbb{F}_q^s$  of degree at most s-1 such that  $\gamma(a_i) = v_i$  for  $i=1,\ldots,s$ .

*Proof.* By interpolation, for each  $j=1,\ldots,m$  we may find a univariate polynomial  $\gamma_j\colon \mathbb{F}_q\to\mathbb{F}_q$  of degree at most s-1 such that  $\gamma_j(a_i)=(v_i)_j$  for all  $i=1,\ldots,s$ . The proof is concluded by taking  $\gamma(t)=(\gamma_1(t),\ldots,\gamma_m(t))$ .

For each edge  $e \in E$  given as  $e = (v_1, \ldots, v_s)$  and an additional point  $x \in \mathbb{F}_q^m$ , by Claim 1.2 we may pick a curve  $\gamma_{e,x}$  of degree at most s such that  $\gamma_e(i) = v_i$  for  $i = 1, \ldots, s$  and  $x = \gamma_e(s+1)$ . The idea is that the univariate function  $A_{\text{extension}} \circ \gamma_{e,x}$  then is a polynomial of degree at most  $mhs = \text{poly}(\log n)$ , so to give all of the values of  $A_{\text{extension}}$  concerning the edge e at once we may simply give the restriction of  $A_{\text{extension}}$  to  $\gamma_{e,x}$ . As mhs is much smaller than q, our hope is that the properties of low-degree polynomials will enable us to ensure the global consistency.

We next describe the "aggregation of queries" transformation more precisely. Our CSG will have nodes for each entry in the points table  $A_0$  and each entry in the planes table  $A_2$ , which are supposed to encode  $A_{\text{extension}}$ . Also, for each edge  $e \in H$  and point  $x \in \mathbb{F}_q^m$  our CSG will have mhs nodes specifying a univariate polynomial  $p_{e,x}$  of degree at most mhs, which is supposed to be  $A_{\text{extension}} \circ \gamma_{e,x}$ . We next describe the test:

- 1. Perform the Plane versus Point test on  $A_0$  and  $A_2$ . I.e. choose a point  $x \in \mathbb{F}_q^m$  and a plane P containing it, and check that  $A_0(x) = A_2[P](x)$ .
- 2. Choose  $e \in E$  an edge in H uniformly.
- 3. Sample a point  $z \in \mathbb{F}_q^m$  and read off the coefficients of  $p_{e,z}$  to construct a univariate polynomial of degree at most mhs.
- 4. Take  $i \in \mathbb{F}_q \setminus \{1, \dots, s+1\}$  randomly, compute  $y = \gamma_{e,z}(i)$  and check that  $p_{e,z}(i) = A_0(y)$ .
- 5. Compute  $\sigma_i = p_{e,z}(i)$  for each  $i = 1, \dots, s$ , and check that  $(\sigma_1, \dots, \sigma_s)$  satisfy the constraint of e.

It is clear that the new PCP construction has size which is polynomial in the size of H, and that the run-time of the reduction is also polynomial. The following lemma addresses the completeness and soundness of the construction.

**Lemma 1.3.** Denote by  $\Psi$  the CSG instance constructed above from H.

- 1. If H is satisfiable, then  $\Psi$  is satisfiable.
- 2. For all  $\varepsilon > 0$ , there is  $\delta > 0$  such that if H is at most  $(1 \varepsilon)$ -satisfiable, then  $\Psi$  is at most  $(1 \delta)$ -satisfiable.

*Proof.* The first item is clear, since we can take a satisfying assignment A of H and assign the tables  $A_0, A_2$  truthfully according to the low-degree extension of A, and then assign the rest of the witness according to the coefficients of  $A \circ \gamma_{e,x}$  for each  $e \in E$  and  $x \in \mathbb{F}_q^m$ .

For the second item, we prove counter-positively that if there are tables  $A_0$ ,  $A_2$  and a table of coefficients that satisfy at least  $1-\delta$  fraction of the constraints of  $\Psi$ , then there is an assignment to A satisfying more than  $1-\varepsilon$  of the constraints of H.

To see that, first note that by the analysis of the Plane versus Point test that as  $A_0(x) = A_2[P](x)$  with probability at least  $1 - \delta$ , it follows that there is a polynomial  $f: \mathbb{F}_q^m \to \mathbb{F}_q$  of degree at most mhs such that  $\Pr_{x \in \mathbb{F}_q^m} [f(x) = A_0(x)] \geqslant 1 - \delta - \frac{mhs}{q^{1/10}} \geqslant 1 - 2\delta$ , and we fix f henceforth.

By an averaging argument, for at least  $1-\sqrt{\delta}$  of the edges  $e\in E$ , the probability the test passes conditioned on choosing e is at least  $1-\sqrt{\delta}$ , and we show that A satisfies each such e. This would finish the proof as  $1-\sqrt{\delta}>1-\varepsilon$ .

Fix e, and note that over the randomness of the choice of z, the distribution of  $\gamma_{e,z}(i)$  for each  $i \in \mathbb{F}_q \setminus \{1,\ldots,s+1\}$  is uniform in  $\mathbb{F}_q^m$ , so we get that  $A_0(y) = f(y)$  with probability  $1 - 2\delta$ . Thus, we get that

$$\Pr_{z,i}\left[f\circ\gamma_{e,z}(i)=p_{e,z}(i)\wedge\text{rest of the test succeeds}\right]\geqslant 1-3\delta,$$

so there is some z such that  $\Pr_i[f \circ \gamma_{e,z}(i) = p_{e,z}(i)] \geqslant 1 - 3\delta$ . As  $f \circ \gamma_{e,z}$ , and  $p_{e,z}$  are univariate polynomials of degree at most mhs, it follows from the Schwarz-Zippel lemma that  $f \circ \gamma_{e,z} \equiv p_{e,z}$ , and from the test of the test we get that the values  $\sigma_i = p_{e,x}(i) = f(\gamma_{e,z}(i)) = f(v_i)$  for  $i = 1, \ldots, s$  satisfy the constraint e.

Therefore, defining  $A \colon \mathbb{H}^m \to \{0,1\}$  by taking A(v) = f(v) if  $f(v) \in \{0,1\}$  and arbitrarily otherwise, we get that A satisfies at least  $1 - \sqrt{\delta}$  of the constraints, and we are done.

### 1.2 The Block Property

We finish the lecture by observing that the above transformation gave us the block property. Indeed, each symbol of the tables  $A_0$  and  $A_2$  will be its own block, and for each  $e \in E$  and  $x \in \mathbb{F}_q^m$  we have a single block containing all of the coefficients of  $p_{e,x}$ . Note that these blocks are disjoint, and our tester looked at 4 blocks. We also note that the total number of queries made is O(mhs), therefore we only incurred a polynomial blow-up in the query complexity while keeping the soundness bounded away from 1 and achieving the block property. Summarizing, in the main features of the aggregation of queries that we used are:

1. Soundness and completeness: the transformation keeps perfect completeness, and if the original soundness was bounded away from 1, then the soundness after the transformation is still bounded away from 1.

- 2. Query complexity: if the original query complexity was s, then the new query complexity will be  $s' = s \operatorname{poly}(\log n)$ . Thus, in the case that s was poly-logarithmic to begin with, we only incur a polynomial blow-up in the query complexity.
- 3. The block property: the new CSG instance has the (k, s') block property for k = 4.

# 2 Some More Words on Composition

One way to think of the aggregation of queries technique is that it reduces us to checking that some univariate polynomial  $p_{e,x}$  satisfies some constraint (in the case above, that the values  $p_{e,x}(1), \ldots, p_{e,x}(s)$  satisfy some constraint  $C_e$ ), and that we managed to ensure global consistency using the low-degree test and the tables  $A_0, A_2$ .

Thus, we have effectively reduced our original problem to a similar looking problem of smaller scale: we want to verify that the values of assignment  $g\colon X'\to\{0,1\}$  (which you can think of as encoding the coefficients of  $p_{e,x}$ ) satisfies some constraint  $C_e$ . The main differences are (1) the domain X' is of much smaller size, and more specifically  $n'=\operatorname{poly}(\log n)$ , and (2) we need to check that the values of the assignment g are consistent with g. In light of (1), one may expect that we should be able to run the algebraic PCP construction restricted to the domain g, namely re-interpreting that as quadratic equations, running the sum-check protocol and using the low-degree test again to further reduce the number of queries from g to g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(g poly(

This is indeed possible, thankfully to the block property, in a similar manner to the composition step we did with the Hadamard code. Drawing further analogies, point (2) above is analogous to the fact we needed to check that our Hadamard encodings satisfy some quadratic equation, and indeed it can be achieved by our algebraic PCP. The details of this construction though get rather hairy and hence are omitted, but by now you have all of the tools and ideas necessary to prove the PCP theorem from scratch.

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lecture 13

### Dor Minzer

In this lecture, we restate the basic form of the PCP theorem using the Label-cover problem. We show how to use it to prove a weak hardness for approximation result for the problem of finding the largest clique in a graph, and then amplify this hardness. We also discuss of improved forms of the PCP theorem that are most relevant towards applications in hardness of approximation.

## 1 The Label Cover Problem

We have seen most of the proof of the basic PCP theorem, asserting that for some absolute constant  $\varepsilon > 0$ , the problem gap-CSG[1, 1 -  $\varepsilon$ ] is NP-hard on instances with O(1) queries and alphabet size O(1). In the previous lecture, we have also seen a transformation that reduces an instance of CSG with constant number queries to a different instance of CSG with 2 queries while preserving perfect completeness and keeping the soundness bounded away from 1. This last transformation gets us a version of the PCP theorem for special type of constraint satisfaction called (projection) label cover problems, defined as follows.

**Definition 1.1.** An instance of Label-cover  $\Psi$  consists of a bi-partite graph  $G=(L\cup R,E)$ , two alphabets  $\Sigma_L$ ,  $\Sigma_R$  and a projection constraint for each edge,  $\Phi=\{\Phi_e\}_{e\in E}$ . By projection constraint, we mean that for each  $e\in E$ , there is a map  $\phi_e\colon \Sigma_L\to \Sigma_R$  such that

$$C_e = \{ (\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma_L \}.$$

In words, a label cover instance  $\Psi$  is a constraint satisfaction graph wherein the underlying constraint graph is bipartite, and each constraint is of projection type. That is, for each edge  $e=(u,v)\in E$ , the label of u determines the label that v should get for the constraint on e to be satisfied. The value of a label-cover instance  $\Psi$ , denoted by  $\operatorname{val}(\Psi)$ , is the maximum fraction of constraints that can be satisfied in it.

### 1.1 The Basic PCP Theorem in the Language of Label Cover

We can formulate the basic PCP theorem we proved so far using the Label-cover problem, as follows:

**Theorem 1.2.** There are absolute constant  $\varepsilon > 0$  and  $k \in \mathbb{N}$  such that the problem gap-Label-Cover $[1, 1-\varepsilon]$  is NP-hard on instances with alphabet size at most k.

Theorem 1.2 is the analog of the Cook-Levin theorem for approximation problems, and as such almost all hardness of approximation results use it as a starting point. To motivate this discussion, note that one may associate with the Label-cover problem an approximation problem, in which the input is a Label-cover instance  $\Psi$ , and the goal is to approximate  $\operatorname{val}(\Psi)$ . In this language, Theorem 1.2 implies that there are  $\varepsilon > 0$  and  $k \in \mathbb{N}$  such that given an instance  $\Psi$  of Label-Cover, is NP-hard to approximate  $\operatorname{val}(\Psi)$  within factor  $1 - \varepsilon$ . Recall that for a maximization problem A (such as label cover), we say an algorithm Alg is an  $\alpha$ -approximation, for  $0 < \alpha \leqslant 1$ , if on an input  $\Psi$  of A it outputs a number  $\operatorname{Alg}(\Psi)$  such that  $\alpha\operatorname{Opt}(\Psi) \leqslant \operatorname{Alg}(\Psi) \leqslant \operatorname{Opt}(\Psi)$ .

**Corollary 1.3.** There exists  $\varepsilon > 0$  such that given a label-cover instance  $\Psi$  with constant size alphabet, it is NP-hard to approximate  $val(\Psi)$  within factor  $1 - \varepsilon$ .

*Proof.* Assume there is an algorithm Alg that approximates  $\mathsf{val}(\Psi)$  in polynomial time within factor  $\frac{1}{1-\varepsilon}$ , i.e. it outputs a number  $\mathsf{Alg}(\Psi)$  satisfying that  $(1-\varepsilon)\mathsf{val}(\Psi) \leqslant \mathsf{Alg}(\Psi) \leqslant \mathsf{val}(\Psi)$ . We use it to solve gap-Label-Cover $[1,1-\varepsilon]$ , which finishes the proof.

Indeed, given an instance  $\Psi$  of label cover, we run  $\mathsf{Alg}(\Psi)$  and get a number s; we accept if  $s>1-\varepsilon$  and otherwise reject. Note that if  $\mathsf{val}(\Psi)=1$ , then by the guarantee of the algorithm  $\mathsf{Alg}(\Psi)\geqslant 1-\varepsilon$ , hence we accept. If  $\mathsf{val}(\Psi)<1-\varepsilon$ , then  $\mathsf{Alg}(\Psi)<1-\varepsilon$  hence we reject. Thus the described algorithm runs in polynomial time and solves gap-Label-Cover $[1,1-\varepsilon]$ .

Thus, at least morally speaking one may expect one to get more hardness of approximation results from Theorem 1.2. Indeed, shortly after the proof of Theorem 1.2 (and actually even during earlier stages of it), researchers have been exploring connections between it and approximation problems, and today we will begin seeing some of this wonderful theory.

# 2 Hardness of Approximating the Maximum Clique

Our first example is the maximum clique problem. Recall that given a graph H = (V, E), a clique on H is a subset of vertices  $S \subseteq V$  such that any distinct  $u, v \in S$  have an edge between them in H. The goal in the maximum clique problem is to find, given a graph H, a clique of the largest possible size.

Clique is one of the classical NP-hard problems studied in the early 70's, and finding the largest possible clique in a given graph H is NP-hard. Today, we will see that even approximating the largest clique in a graph is NP-hard. For that, we introduce the appropriate gap notations for clique, and gap-preserving Karp reductions. For  $0 < \beta \leqslant \alpha \leqslant 1$ , an input to the problem gap-Clique $[\alpha, \beta]$  is a graph H promised to either contain a clique of fractional size at least  $\alpha$ , or not contain a clique of fractional size  $\beta$ , and the goal is to distinguish between these two cases.

## 2.1 The Basic Hardness of Approximation Result for Clique

We prove the following result:

**Theorem 2.1.** There are absolute constants  $0 < \beta \le \alpha \le 1$  for which gap-Clique  $[\alpha, \beta]$  is NP-hard.

The proof of Theorem 2.1 is by a polynomial time reduction from Theorem 1.2. Namely, we show a polynomial time map from an instance  $\Psi$  of label cover to a graph H such that:

- 1. Completeness: If  $val(\Psi) = 1$ , then  $Clique(H) \ge \alpha$ .
- 2. **Soundness:** If  $val(\Psi) < 1 \varepsilon$ , then  $Clique(H) < \beta$ .

We leave it to the reader to verify that such reduction indeed implies that gap-Clique  $[\alpha, \beta]$  is NP-hard.

Proof of Theorem 2.1. Let  $\Psi = (G = (L \cup R, E, \Sigma_L, \Sigma_R, \Phi))$  be a label cover instance as in Theorem 1.2. We construct a graph H = (V', E') as follows. For each edge  $e \in E$  of  $\Psi$  and a pair of labels to its endpoints that satisfy the constraint on e, that is  $(\sigma_1, \sigma_2) \in \Phi_e$ , we create a vertex  $v_{e,\sigma_1,\sigma_2} \in V'$ . As for the edges in H, we connect  $v_{e,\sigma_1,\sigma_2}$  and  $v_{e',\sigma'_1,\sigma'_2}$  by an edge if  $e, \sigma_1, \sigma_2$  and  $e, \sigma'_1, \sigma'_2$  that are consistent. This completes the description of the reduction.

To get a intuition for what the edges represent, we give a few examples. Suppose we have an edge  $e \in E$  in the original graph, and two distinct pairs of labels that satisfy it,  $(\sigma_1, \sigma_2) \neq (\sigma'_1, \sigma'_2)$ ; then the vertices  $v_{e,\sigma_1,\sigma_2}$  and  $v_{e',\sigma'_1,\sigma'_2}$  do not have an edge between them. Thus, in particular, a clique can contain at most a single vertex of the form  $v_{e,\sigma_1,\sigma_2}$  for each  $e \in E$ . We will often refer to the collection of vertices  $\{v_{e,\sigma_1,\sigma_2}\}_{\sigma_1 \in \Sigma_L, \sigma_2 \in \Sigma_R}$  as the cloud of e, and in this language we have observed that the cloud of each e forms an independent set in e. More generally, if we have two edges  $e_1 = (u_1, v_1)$  and  $e_2 = (u_2, v_2)$  sharing a vertex – say the left one, i.e.  $u_1 = u_2$  – as well as pairs  $(\sigma_1, \sigma_2)$  satisfying  $e_1$  and  $(\sigma'_1, \sigma'_2)$  satisfying  $e'_1$ , then  $v_{e,\sigma_1,\sigma_2}$  and  $v_{e',\sigma'_1,\sigma'_2}$  are connected by an edge only if  $\sigma_1 = \sigma'_1$ . Thus, if we have a clique of vertices in e, then for each vertex in the original graph e, all vertices e, and in the clique such that the left endpoint of e is e agree on e.

We denote  $k_L = |\Sigma_L|$  and  $k_R = |\Sigma_R|$ , and note that since each constraint  $\Phi_e$  has  $k_L$  satisfying pairs, the number of vertices in H' is  $k_L \cdot |E| = k_L \cdot m$ . We now prove the completeness of the reduction for  $\alpha = 1/k_L$  and  $\beta = (1 - \varepsilon)/k_L$ .

**Completeness:** We show that if  $\Psi$  is satisfiable, then H contains a clique of size m. Indeed, let  $A_L \colon L \to \Sigma_L$  and  $A_R \colon R \to \Sigma_R$  be satisfying assignments, and define

$$C = \{ v_{e,\sigma_1,\sigma_2} \mid e = (u, v), A_L(u) = \sigma_1, A_R(v) = \sigma_2 \}.$$

Then C is a clique in H, and |H| = m.

**Soundness:** We show that if  $\Psi$  is at most  $(1 - \varepsilon)$  satisfiable, then the largest clique in H has size at most  $(1 - \varepsilon)m$ . We do so counter-positively: we assume that C is a clique of size larger than  $(1 - \varepsilon)m$ , and deduce from it a pair of assignments  $A_L$  and  $A_R$  that satisfy more than  $1 - \varepsilon$  fraction of the constraints in  $\Psi$ .

Take C to be a clique of size larger than  $(1-\varepsilon)m$  in H. By our earlier observation for each  $u\in L$  there is a value  $\sigma_u\in \Sigma_L$  such that, if an edge  $e\in E$  contains u, say e=(u,v), is such that the clique C contains some vertex from the cloud of e, then such vertex must be  $v_{e,\sigma_1,\sigma_2}$  for  $\sigma_1=\sigma_u$ . Thus, we can define  $A_L(u)=\sigma_u$ . Similarly, for each  $v\in R$  there is a value  $\sigma_v\in \Sigma_R$  such that, if an edge  $e\in E$  contains v, say e=(u,v), is such that the clique C contains some vertex from the cloud of e, then such vertex must be  $v_{e,\sigma_1,\sigma_2}$  for  $\sigma_2=\sigma_v$ . Thus, we can define  $A_R(v)=\sigma_v$ 

By our earlier observations C may contain at most a single vertex from the cloud of each  $e \in E$ , hence it follows that there are more than  $(1-\varepsilon)m$  clouds from which C contains a vertex. Let  $E' \subseteq E$  be the set of  $e \in E$  such that C contains some vertex from the cloud of e. We argue that  $A_L$ ,  $A_R$  satisfy all edges in E', hence they satisfy at least  $|E'|/m > 1 - \varepsilon$  fraction of the constraints. Indeed, if  $e \in E'$  then there is a vertex of the form  $v_{e,\sigma_1,\sigma_2}$  in C. Writing e = (u,v), by construction  $(\sigma_1,\sigma_2)$  satisfies the constraint  $\Phi_e$ , and by the choice of  $A_L$  and  $A_R$  we have that  $A_L(u) = \sigma_1$  and  $A_R(v) = \sigma_2$ .

Just like in Corollary 1.3, Theorem 2.1 directly implies that it is NP-hard to approximate the size of the largest clique in a graph within factor  $\beta/\alpha$  where  $\alpha, \beta$  are the number from Theorem 2.1. Inspecting, we see that the  $\alpha$  and  $\beta$  we get yield that  $\beta/\alpha = 1 - \varepsilon$  where  $\varepsilon > 0$  is some positive absolute constant. This means that getting arbitrary good approximation of clique is NP-hard.

## 2.2 Hardness Amplification for Clique

Is it possible, though, to approximate the size of the largest clique in a graph within a not-so-good factor, say 10, or 100? It turns out not to be possible, and to do so we amplify the result of Theorem 2.1

**Theorem 2.2.** There are absolute constants  $0 < \beta \le \alpha \le 1$  such that for all  $t \in \mathbb{N}$ , the problem  $gap\text{-}Clique[\alpha^t, \beta^t]$  is NP-hard.

Thus, we get that for all  $t \in \mathbb{N}$ , approximating the largest clique within factor  $\beta^t/\alpha^t = (1-\varepsilon)^t$  is NP-hard, and as we may pick t to be as large as we wish (but constant), any constant factor approximation for clique is NP-hard.

*Proof of Theorem 2.2.* We show a reduction from Theorem 2.1. Namely, for each  $t \in \mathbb{N}$ , we show a polynomial time reduction from gap-Clique[ $\alpha$ ,  $\beta$ ] to gap-Clique[ $\alpha^t$ ,  $\beta^t$ ].

Given an instance G = (V, E) of gap-Clique $[\alpha, \beta]$ , we produce a graph G' = (V', E') as follows. The vertices of G' are all t-tuple of vertices from G, that is

$$V' = \{ (v_1, \dots, v_t) \mid v_i \in V \ \forall i = 1, \dots, t \}.$$

As for the edges, we connect  $(v_1, \ldots, v_t)$  and  $(u_1, \ldots, u_t)$  by an edge if for all  $i = 1, \ldots, t$ , either  $(v_i, u_i) \in E$  or  $v_i = u_i$ . This completes the description of the reduction.

**Completeness:** We show that if G contains a clique of size at least  $\alpha |V|$ , then G' contains a clique of size at least  $\alpha^t |V'|$ . Indeed, let  $C \subseteq V$  be a clique of size at least  $\alpha |V|$ , and define

$$C' = \{ (v_1, \dots, v_t) \mid v_i \in C \ \forall i = 1, \dots, t \}.$$

Then  $|C'| = |C|^t \ge \alpha^t |V|^t = \alpha^t |V'|$ , and C' is a clique in G'.

**Soundness:** We show that if G does not contain a clique of size  $\beta |V|$ , then G' does not contain a clique of size  $\beta^t |V'|$ . Indeed, let C' be any clique in G', and define for each i = 1, ..., t the set

$$C_i = \{ v \in V \mid \exists (v_1, \dots, v_t) \in C' \text{ such that } v_i = v \}$$
.

In words,  $C_i$  is the set of all possible vertices that appear as the *i*th coordinate of some vertex in C'. Note that  $C_i$  forms a clique in G; indeed, otherwise we would have  $v, u \in C_i$  that are not adjacent, and so we may find  $(v_1, \ldots, v_t)$  and  $(u_1, \ldots, u_t)$  in C' such that  $v_i = v$  and  $u_i = u$ , and by definition of the graph these two vertices are not adjacent in G', in contradiction to the fact that C' forms a clique. Thus,  $|C_i| < \beta |V|$ .

To finish the proof, note that  $C' \subseteq C_1 \times C_2 \times \ldots \times C_t$ , hence

$$C' \leq \prod_{i=1}^{t} |C_i| < \prod_{i=1}^{t} \beta |V| = \beta^t |V'|^t.$$

From Theorem 2.1 we get the following immediate corollary.

**Corollary 2.3.** For all C > 1, approximating the maximum clique in a graph within factor C is NP-hard.

## 2.3 PCP and Hardness of Approximation

Corollary 2.3 is an amazing consequence of the theory of PCPs, and to date this is the only known approach to proving hardness of approximation results for clique. In fact, almost all hardness of approximation results use the theory of PCPs and start from Theorem 1.2.

At a high level, the proof of Corollary 2.3 proceeded via two steps. In the first step we proved a weak hardness of approximation result for clique (in the form of Theorem 2.1), and in the second step we amplified it into a strong hardness of approximation result. It turns out that replicating the first step can be done for a vast class of approximation problems, and these are often referred to as APX hardness results. These

type of results say that for many problems there exists some constant factor within which it is NP-hard to approximate the optimum solution. Many of the combinatorial optimization problems that you know (such as 3SAT, Vertex-Cover, Set-Cover, Max-Cut etc.) fall into this category, and are hence at least somewhat hard to approximate.

Getting strong hardness of approximation results requires more efforts and more ideas. We were fairly lucky in the case of clique, for which we could directly perform amplification. The situation is more complicated though for other combinatorial optimization problems, which motivates the questions of if there are stronger forms of the PCP theorem that imply strong hardness of approximation results.

## 3 Extreme Versions of the PCP Theorem

Inspecting Theorem 1.2, one may wonder what additional features of it would be of help when proving hardness of approximation results. The above example of clique already highlights one important such aspect regarding the soundness of the result, and more specifically whether it could be taken to be close to 0. Additionally, one may observe that if we wish to investigate super-constant factor approximations for clique – say we want to show it is NP-hard to approximate within factor  $n^{\varepsilon}$  where n is the number of vertices in the graph – we need the soundness to be related to the size of the instance. Lastly, and this will only become more apparent once we see a few hardness of approximation results, one could hope that the structure of the constraints  $\Phi_e$  to be as restrictive and as simple as possible.

We summarize this discussion by stating a few aspects in which one may try to improve upon Theorem 1.2, as well as some buzzwords that are related to them.

- 1. **Hardness amplification.** Are there forms of Theorem 1.2 with small soundness? Namely, is it true that for every  $\varepsilon > 0$ , there is  $k \in \mathbb{N}$  such that the problem gap-Label-Cover $[1, \varepsilon]$  is NP-hard on instances with alphabet size at most k? We will see that the answer to this question is positive, and towards this end introduce a technique known as *parallel repetition*.
- 2. **Sub-constant error PCPs.** Are there forms of Theorem 1.2 in which the soundness is vanishing with the instance size? How about forms of the theorem in which the soundness is polynomially small in the instance size? Note that in such cases, the alphabet will also have to be of a size which is growing with the instance size.
  - PCPs with sub-constant errors are known, and we have already seen some of the ideas that go into constructing them (such as list-decoding in the plane versus point test), but proving it requires much more effort. Getting sub-constant error PCPs with 2 queries is even harder, but it is known by now. As for PCPs with polynomially small error, this is a well known open problem in the theory of PCPs known as the sliding scale conjecture.
- 3. **The simplicity of the constraints.** Once we see several PCP reductions, you will see that on top on needing small soundness, these reductions heavily use the fact we have projection constraints. It took time to realize, but it turns out that the simpler the structure the constraints is, the more useful PCP result one gets.

One of the most important examples for such structures are d-to-1 constraints, by which we mean that not only is the map  $\phi_e \colon \Sigma_L \to \Sigma_R$  a projection map, but it is also "not very far" from being a

<sup>&</sup>lt;sup>1</sup>In the case of clique such results are known while the corresponding forms of Theorem 1.2 are not, since there are ways to work-around this issue.

permutation. In the extreme case of d=1, one indeed wants each constraint  $\phi_e$  to be a permutation map; such PCPs are conjectured to exist but are not currently known. The statement that such PCPs exists is a well-known conjecture in complexity theory that goes by the name the Unique-Games Conjecture. For the case d=2, one wants each constraint  $\phi_e$  to be 2-to-1, namely that each  $\sigma_2 \in \Sigma_R$  has two pre-images under  $\Sigma_L$ . Such PCPs were conjectured to exist in the same paper introducing the Unique-Games Conjecture, and by now it is known how to construct them.

In the rest of this course, we will mainly discuss points 1 and 3 above. In particular, starting from the next lecture we will discuss the parallel repetition theorem, and long-code framework and how to use it to prove some optimal hardness of approximation results. We will then discuss the Unique-Games Conjecture, some of its consequences and recent developments regarding it.

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lectures 14,15

#### Dor Minzer

In this lecture we present the parallel repetition theorem, an amplification result that allows us to prove a PCP theorem with small soundness.

# 1 Gap Amplification via Parallel Repetition

Recall the basic PCP theorem:

**Theorem 1.1.** There are absolute constant  $\varepsilon > 0$  and  $k \in \mathbb{N}$  such that the problem gap-Label-Cover $[1, 1-\varepsilon]$  is NP-hard on instances with alphabet size at most k.

Our goal in this lecture is to prove an improved form of Theorem 1.1, in which the soundness is small:

**Theorem 1.2.** For all  $\varepsilon > 0$ , there is  $k \in \mathbb{N}$  such that the problem gap-Label-Cover $[1, \varepsilon]$  is NP-hard on instances with alphabet size at most k.

We intend to use Theorem 1.1 to prove Theorem 1.2; how can we do that? Given a label-cover instance, how do we construct a harder label-cover instance? To motivate this discussion, we take the 2-prover-1-round view on Theorem 1.1.

Suppose we have a computationally weak verifier V and two all powerful provers  $P_1$  and  $P_2$  that do not communicate. All 3 parties have a common label cover instance  $\Psi$ , and the verifier wishes to distinguish between the case that  $\operatorname{val}(\Psi)=1$  and the case that  $\operatorname{val}(\Psi)\leqslant 1-\varepsilon$ . To do that, the verifier may ask each one of the provers a question, get an answer and decided whether to accept or reject.

Write  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \{\Phi_e\}_{e \in E})$ . To execute the task above, the verifier can sample an edge  $e = (u, v) \in E$  uniformly, send u to  $P_1$  and v to  $P_2$ , and get labels  $\sigma_u \in \Sigma_L$  and  $\sigma_v \in \Sigma_R$  from them. The verifier then checks that these labels satisfy the constraint on e, that is that  $(\sigma_u, \sigma_v) \in \Phi_e$ , and if so accepts (and otherwise rejects).

It is easy to see that if  $val(\Psi) = 1$ , then there are provers' strategies that make V accept with probability 1. It is also true, and not very difficult to show (try!), that if  $val(\Psi) \le 1 - \varepsilon$ , then no provers' strategy can make V accept with probability more than  $1 - \varepsilon$ . Hence, the prover has a good advantage in distinguishing between two cases. Still it is only an  $\varepsilon$  advantage, and a natural question is how can V increase it?

## 1.1 Sequential Repetition

The first idea that comes to mind is that V should just repeat this protocol several times. Namely, after sampling an edge, sending each one of the endpoints to one of the provers, receiving answers and checking the constraint, the verifier could repeat this process again by sampling another edge and so on. Thus, we get a 2-prover-multiple-round game, an it is easy to show that the advantage of V indeed increases. Unfortunately, 2-prover-multiple-round games do not have a simple PCP interpretation and we will not be

able to prove Theorem 1.2 using this idea. An essentially identical idea is for V to have access to t pairs of provers  $(P_i, P_i')$  for  $i = 1, \ldots, t$ , and for each one of the pairs run the basic 2-prover-1-round game as before, independently. This operation, too, increases the advantage of the verifier, however the analogous PCP interpretation this would give us is a PCP with more than 2 queries (2t queries to be precise), which is not good enough for proving Theorem 1.2.

## 1.2 Parallel Repetition

The next idea is that we should adapt the idea above while making sure to keep the number of provers to be exactly 2. A natural variant is to simply send each one of them multiple challenges. That is, the t-fold repeated game proceeds by the verifier V picking t edges  $e_1, \ldots, e_t \in E$  uniformly at random, denoting  $e_i = (u_i, v_i)$  for  $i = 1, \ldots, t$  and send all of the challenges to each one of the provers in a single shot. That is, the verifier sends the first prover  $(u_1, \ldots, u_t)$  and sends to the second prover  $(v_1, \ldots, v_t)$ , and excepts to get from each one of them a tuple of labels, say  $(\sigma_{u_1}, \ldots, \sigma_{u_t})$  and  $(\sigma_{v_1}, \ldots, \sigma_{v_t})$ . The verifier then checks that for all  $i = 1, \ldots, t$ , the corresponding pair of labels  $(\sigma_{u_i}, \sigma_{v_i})$  satisfies the constraint on  $e_i$ , that is that  $(\sigma_{u_i}, \sigma_{v_i}) \in \Phi_{e_i}$ , and if so accepts and otherwise rejects. We call this game the t-fold repeated game, and denote it by  $\Psi^{\otimes t}$ .

So what does this operation do? Well clearly, if  $\operatorname{val}(\Psi) = 1$ , the provers can simply assign their vertices according to some pair of satisfying assignments  $A_L \colon L \to \Sigma_L$  and  $A_R \colon R \to \Sigma_R$  and make the verifier accept with probability 1. Also, if  $\operatorname{val}(\Psi) \leqslant 1 - \varepsilon$ , then on each one of the challenges  $e_i$ , the provers manage to win with probability at most  $1 - \varepsilon$ , and since the challenges are chosen independently the probability that they win on all t of them, and thus make the verifier accept, is at most  $(1 - \varepsilon)^t$ . Or is it?

## 1.2.1 An Instructive Example for Pitfalls in Parallel Repetition

Let us consider an example of a 2-prover-1-round game that exhibits an interesting possibility that may occur in parallel repetition. In the basic game  $\Psi$ , the verifier picks as challenges (x,y) uniformly from  $\{0,1\}^2$ , sends x to  $P_1$  and y to  $P_2$ , and expects to get as answer from  $P_1$  a vector  $a \in \{1,2\} \times \{0,1\}$  and from  $P_2$  a vector  $b \in \{1,2\} \times \{0,1\}$ . The verifier accepts if and only if  $a=b=(i,\sigma)$  and prover i received  $\sigma$  as a challenge.

In  $\Psi$ , the provers may use the following strategy:  $P_1$  can give an answer which is (2,0) and  $P_2$  can give the answer (2,0), and the probability that they win is the probability that y=0 which is 1/2. In general, it can be shown that  $\operatorname{val}(\Psi) \leqslant 1/2$ , since to win the provers must choose the same i, and conditioned on i – say i=1 – the second prover must send  $\sigma$  which is equal to x, but his answer is independent of x hence equal to x with probability at most 1/2.

What about the value of the 2-fold repeated game, that is  $\Psi^{\otimes 2}$ ? The argument above says that we should have that  $\operatorname{val}(\Psi^{\otimes 2}) \leqslant 1/4$ , alas this is false. Indeed, consider the setting of the 2-fold repeated game in which  $P_1$  receives challenges  $(x_1,x_2)$  and  $P_2$  receives challenges  $(y_1,y_2)$ , and they need to generate  $a(1),a(2)\in\{1,2\}\times\{0,1\}$  and  $b(1),b(2)\in\{1,2\}\times\{0,1\}$  so that  $a(1)=b(1)=(i_1,\sigma_1)$  and  $P_{i_1}$  received  $\sigma_1$  in their first coordinate, and  $a(2)=b(2)=(i_2,\sigma_2)$  and  $P_{i_2}$  received  $\sigma_2$  in their second coordinate. To do that,  $P_1$  simply outputs  $(1,x_1)$  and  $(2,x_1)$  and  $P_2$  simply outputs  $(1,y_2)$  and  $(2,y_2)$ . Note that if  $x_1=y_2$ , the provers win using this strategy, hence they make the verifier accept with probability at least 1/2!

## 1.2.2 Where Did We Go Wrong?

For the game above  $\Psi$ , it turns out that  $\operatorname{val}(\Psi^{\otimes 2}) = \operatorname{val}(\Psi)$ , so 2-fold repetition does not change the value of the game at all, let alone square it (as we claimed). The way the provers managed to do that is by correlating their answers to the challenges on both coordinates, so that with some probability they fail miserably (on both coordinates), but as a by-product they manage to win all coordinates with probability which is higher than expected. Inspecting our earlier "proof" of  $\operatorname{val}(\Psi^t) \leqslant \operatorname{val}(\Psi)^t$ , we see that we implicitly assumed that the answer that each prover gives to the challenge on the  $i^{\text{th}}$  coordinate only depends on that coordinate. This need not be the case, and as the above example shows that there are cases that the provers can use this to their advantage.

## 1.3 The Parallel Repetition Theorem

Still, it turns out that parallel repetition does work, in the sense that for large enough t it does decrease the probability V accepts in the case that  $val(\Psi) \leq 1 - \varepsilon$ . More precisely, one has:

**Theorem 1.3** (The Parallel Repetition Theorem). For all  $\varepsilon > 0$ , there exists  $\delta > 0$  such that the following holds. Let  $\Psi$  be a projection 2-prover-1-round game, and suppose that  $val(\Psi) \leq 1 - \varepsilon$ . Then

$$\mathsf{val}(\Psi^{\otimes t}) \leqslant (1 - \delta)^t.$$

In words, Theorem 1.3 states that the value of the t-fold repeated game does decrease exponentially with t. There are other interesting aspects of Theorem 1.3, such as for example the precise dependency of  $\delta$  on  $\varepsilon$ , and we may discuss that later on in the course.

We next show how to deduce Theorem 1.2 from Theorem 1.1 by appealing to the Parallel Repetition theorem.

Proof of Theorem 1.2. Let  $\varepsilon_0$  be from Theorem 1.1, take  $\delta_0$  from Theorem 1.3 for  $\varepsilon_0$  and choose  $t = \frac{\log(1/\varepsilon)}{\delta_0}$ . Given a label-cover instance  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \{\Phi_e\}_{e \in E})$  from Theorem 1.1, we construct a label cover instance  $\Psi' = (G' = (L' \cup R', E'), \Sigma_{L'}, \Sigma_{R'}, \{\Phi'_e\}_{e \in E'})$  as follows. The sides of the bi-partite graph G' are

$$L' = L^t = \{ (u_1, \dots, u_t) \mid u_i \in L \ \forall i = 1, \dots, t \}, \qquad R' = R^t = \{ (v_1, \dots, v_t) \mid v_i \in R \ \forall i = 1, \dots, t \}$$

(corresponding to challenges in the setting of parallel repetition), and label sets

$$\Sigma_{L'} = \Sigma_L^t, \qquad \Sigma_{R'} = \Sigma_R^t.$$

The edge set E' has an edge between  $(u_1, \ldots, u_t)$  and  $(v_1, \ldots, v_t)$  if  $(u_i, v_i) \in E$  for all  $i = 1, \ldots, t$ . The constraint on this edge then allows for tuples  $(\sigma_1, \ldots, \sigma_t) \in \Sigma_{L'}$  and  $(\tau_1, \ldots, \tau_t) \in \Sigma_{R'}$  such that  $(\sigma_i, \tau_i) \in \Phi_{u_i, v_i}$  for all  $i = 1, \ldots, t$ . This completes the description of the reduction.

Note that the reduction runs in time  $n^{O(t)}$ , hence polynomial. Next, we analyze the completeness and the soundness of the reduction.

**Completeness.** If  $\Psi$  is fully satisfiable, then we can use a satisfying assignment pair  $A_L$  and  $A_R$  of it to assign all tuples in  $\Psi'$  accordingly, and notice that it satisfies all of the constraints of  $\Psi$ .

**Soundness.** If  $\Psi$  is at most  $1-\varepsilon$  satisfiable, then as observed earlier the corresponding 2-prover-1-round game has value which is at most  $1-\varepsilon$ . Note that if we have an assignment to  $\Phi'$  satisfying at least  $\eta$  fraction of the constraints, then the provers may use it to win the t-fold repeated game  $\Psi^{\otimes t}$  with probability at least  $\eta$ ; indeed the edges of  $\Psi'$  exactly correspond to challenges that they may face in the t-fold repeated game. Thus, in  $\Psi'$  at most  $\operatorname{val}(\Psi^{\otimes t})$  of the constraints can be satisfied, and by Theorem 1.3 we have that  $\eta \leqslant \operatorname{val}(\Psi^{\otimes t}) \leqslant (1-\delta_0)^t \leqslant \varepsilon$ .

# 2 On the Proof of the Parallel Repetition Theorem

There are several known approach to prove Theorem 1.3 but none of them is very easy. Roughly speaking, known proofs (including the original proof by Ran Raz) go via the route of information theory, or via spectral graph theory. Our goal here will be to give some flavor of the proof and thus we will omit many (very crucial) details. Our presentation will follow the information theoretic approach to parallel repetition.

## 2.1 A Little Bit of Information Theory

There are many basic and important notions of information theory, such as entropy, mutual information and KL-divergence and all of their condition counterparts. To simplify presentation we will define as little of them as possible, at the expense of appealing to intuition (instead of rigorous proofs).

#### 2.1.1 Shannon Entropy

Still, we will need the most basic notion in information theory, namely the notion of Shannon Entropy defined as follows:

**Definition 2.1.** Let X be a discrete random variable getting values in X. The Shannon Entropy of X is

$$H(\mathbf{X}) = \sum_{x \in X} \Pr\left[\mathbf{X} = x\right] \log\left(\frac{1}{\Pr\left[\mathbf{X} = x\right]}\right).$$

Intuitively,  $H(\mathbf{X})$  measures the amount of randomness the random variable  $\mathbf{X}$ . To verify this intuition, it makes sense to ask what is the maximal entropy a random variable  $\mathbf{X}$  over X may have, and what sort of random variables achieve this maximum or values near it.

1. **Entropy of a random variable is at most logarithm of the size of the support.** Note that by Jensen's inequality,

$$H(\mathbf{X}) = \sum_{x \in X} \Pr\left[\mathbf{X} = x\right] \log\left(\frac{1}{\Pr\left[\mathbf{X} = x\right]}\right) = \underset{x \sim \mathbf{X}}{\mathbb{E}} \left[\log\left(\frac{1}{\Pr\left[\mathbf{X} = x\right]}\right)\right]$$

$$\leq \log\left(\underset{x \sim \mathbf{X}}{\mathbb{E}} \left[\frac{1}{\Pr\left[\mathbf{X} = x\right]}\right]\right)$$

since  $\log(z)$  is concave. As  $\mathbb{E}_{x \sim \mathbf{X}}\left[\frac{1}{\Pr[\mathbf{X} = x]}\right] = |X|$ , it follows that  $H(\mathbf{X}) \leqslant \log(|X|)$ .

2. Almost full entropy implies close to being uniform. For a random variable X whose distribution is uniform over X, the previous bound it tight as then

$$H(\mathbf{X}) = \sum_{x \in X} \frac{1}{|X|} \log(|X|) = \log(|X|).$$

Moreover, one may observe that the uniform distribution over X is the unique distribution for which equality holds (by inspecting the equality case of Jensen's inequality). In fact, one can show that a random variable  $\mathbf{X}$  that achieves near equality, that is a random variable  $\mathbf{X}$  that has entropy at least  $\log(|X|) - \varepsilon$ , is close to being uniformly distributed over X. Here, closeness is with respect to the statistical distance between random variables, which is defined as: for random variables  $\mathbf{X}$  and  $\mathbf{Y}$  distributed over  $\Omega$ , define

$$SD(\mathbf{X}, \mathbf{Y}) = \frac{1}{2} \sum_{\omega \in \Omega} \left| Pr[\mathbf{X} = \omega] - Pr[\mathbf{Y} = \omega] \right|.$$

Then, we have the following result, which can be proved using a result known as Pinsker's inequality:

**Claim 2.2.** If **X** is a distribution over X satisfying  $H(\mathbf{X}) \geqslant \log(|X|) - \varepsilon$ , then  $\mathsf{SD}(\mathbf{X}, \mathbf{U}) \leqslant \sqrt{\varepsilon}$  where **U** is the uniform distribution over X.

## 2.1.2 Conditional Shannon Entropy

We will also need the notion of conditional Shannon Entropies.

**Definition 2.3.** Let X be a discrete random variable getting values in X, and let E be an event. Then the Shannon entropy of X|E is

$$H(\mathbf{X}|E) = \sum_{x \in X} \Pr\left[\mathbf{X} = x \mid E\right] \log\left(\frac{1}{\Pr\left[\mathbf{X} = x \mid E\right]}\right).$$

Conditioning on an event can either increase or decrease the entropy of a random variable. Next, we define the Shannon entropy of a random variable conditioned on another random variable.

**Definition 2.4.** Let X, Y be a discrete random variable. Then the Shannon Entropy of X|Y is

$$H(\mathbf{X}|\mathbf{Y}) = \mathbb{E}_{y \sim \mathbf{Y}}[H(\mathbf{X}|\mathbf{Y} = y)].$$

Conditioning on a random variable can never increase the entropy of a random variable:

**Claim 2.5.** For jointedly distributed  $(\mathbf{X}, \mathbf{Y})$  discrete random variables we have that  $H(\mathbf{X}|\mathbf{Y}) \leq H(\mathbf{X})$ .

*Proof.* Write for convenience  $p_{x,y} = \Pr[\mathbf{X} = x, \mathbf{Y} = y]$  and  $p_{y|x} = \Pr[\mathbf{Y} = y \mid \mathbf{X} = x]$ , by Jensen's inequality

$$H(\mathbf{X}|\mathbf{Y}) = \sum_{x} \underset{y \sim \mathbf{Y}}{\mathbb{E}} \left[ p_{x|y} \log \left( \frac{1}{p_{x|y}} \right) \right] \leqslant \sum_{x} \underset{y \sim \mathbf{Y}}{\mathbb{E}} \left[ p_{x|y} \right] \log \left( \frac{1}{\mathbb{E}_{y \sim \mathbf{Y}} \left[ p_{x|y} \right]} \right),$$

and the proof is concluded by noting that  $\mathbb{E}_{y \sim \mathbf{Y}}\left[p_{x|y}\right] = p_x$ , so the last sum is exactly  $H(\mathbf{X})$ .

#### 2.1.3 Entropy Sub-additivity

The Shannon entropy has several important properties, which are all very plausible sounding. For example, if we think of  $H(\mathbf{X})$  as the amount of randomness in  $\mathbf{X}$ , then one may expect the following connection. Suppose we have  $(\mathbf{X}, \mathbf{Y})$  that is jointedly distribution, and we look at  $H(\mathbf{X}, \mathbf{Y})$ , which measures the amount of randomness in  $(\mathbf{X}, \mathbf{Y})$ . Then we expect it to be equal to the amount of randomness in  $\mathbf{X}$ , plus the amount of randomness in  $\mathbf{Y}$  conditioned on knowing  $\mathbf{X}$ . In notations, we expect that it will be true that

$$H(\mathbf{X}, \mathbf{Y}) = H(\mathbf{X}) + H(\mathbf{Y} \mid \mathbf{X}).$$

Indeed, this is true and not difficult to prove; write for convenience  $p_{x,y} = \Pr\left[\mathbf{X} = x, \mathbf{Y} = y\right]$  and  $p_{y|x} = \Pr\left[\mathbf{Y} = y \mid \mathbf{X} = x\right]$ , then

$$H(\mathbf{X},\mathbf{Y}) = \sum_{x,y} p_{x,y} \log \left(\frac{1}{p_{x,y}}\right) = \sum_{x,y} p_x p_{y|x} \log \left(\frac{1}{p_x p_{y|x}}\right) = \sum_{x,y} p_x p_{y|x} \log \left(\frac{1}{p_{y|x}}\right) + \sum_{x,y} p_x p_{y|x} \log \left(\frac{1}{p_x}\right),$$

and the first term is equal to  $H(\mathbf{Y} \mid \mathbf{X})$  while the second term is equal to  $H(\mathbf{X})$  (pushing the sum over y inside and notion that the sum of  $p_{y|x}$  over y is 1). Using Claim 2.5, we conclude that Shannon entropy sub-additivity:

**Claim 2.6.** Let  $(\mathbf{X}, \mathbf{Y})$  be jointedly distributed discrete random variables. Then  $H(\mathbf{X}, \mathbf{Y}) \leq H(\mathbf{X}) + H(\mathbf{Y})$ .

## 2.1.4 Entropy Decrease by Conditioning on an Event

The last fact we need about Shannon entropies is that if we have a random variable U distributed uniformly over a set U and an event E which is not too unlikely, then the entropy of U|E is still somewhat large:

**Claim 2.7.** Let U be a discrete uniform random variable over a universe U, and let E be some event. Then

$$H(\mathbf{U} \mid E) \geqslant H(\mathbf{U}) - \log\left(\frac{1}{\Pr[E]}\right).$$

*Proof.* We have

$$H(\mathbf{U} \mid E) = \sum_{u \in U} p_{u \mid E} \log \left( \frac{1}{p_{u \mid E}} \right) = \sum_{u \in U} p_{u \mid E} \log \left( \frac{\Pr[E]}{\Pr[\mathbf{U} = u \land E]} \right).$$

Since  $\Pr\left[\mathbf{U} = u \wedge E\right] \leqslant \Pr\left[\mathbf{U} = u\right] = \frac{1}{|U|}$ , we get that

$$H(\mathbf{U} \mid E) \geqslant \sum_{u \in U} p_{u \mid E} \log \left( |U| \cdot \Pr\left[E\right] \right) = \log(|U|) - \log \left( \frac{1}{\Pr\left[E\right]} \right) = H(\mathbf{U}) - \log \left( \frac{1}{\Pr\left[E\right]} \right).$$

## 2.2 The Information Theoretic Approach to Parallel Repetition

#### 2.2.1 The High Level Approach

Let  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \{\Phi_e\}_{e \in E})$  be a 2-player-1-round game as before, and consider the t-fold repeated game. In that game, the verifier samples challenges, which are uniformly chosen edges  $(\mathbf{X}_1, \mathbf{Y}_1), \ldots, (\mathbf{X}_t, \mathbf{Y}_t) \in_R E$ , sends the challenges  $\mathbf{X} = (\mathbf{X}_1, \ldots, \mathbf{X}_t)$  to the first prover, the challenges  $\mathbf{Y} = (\mathbf{Y}_1, \ldots, \mathbf{Y}_t)$  to the second prover, and expects answers  $\mathbf{A}(\mathbf{X}_1, \ldots, \mathbf{X}_t) = (\mathbf{A}_1, \ldots, \mathbf{A}_t)$  from the first prover and answers  $\mathbf{B}(\mathbf{Y}_1, \ldots, \mathbf{Y}_t) = (\mathbf{B}_1, \ldots, \mathbf{B}_t)$  from the second prover. We note that each answer  $\mathbf{A}_i$  and each answer  $\mathbf{B}_i$  may depend on all of the challenges the respective player has received, but we omit this from the notation to make it less cumbersome.

We say the provers win on coordinate i if  $(\mathbf{A}_i, \mathbf{B}_i) \in \Phi_{(\mathbf{X}_i, \mathbf{Y}_i)}$ , and denote this event by  $W_i$ . We also denote by  $W = W_1 \cap W_2 \cap \ldots \cap W_t$  the probability the players win all of the coordinates. In these notations, our goal is to show that  $\Pr[W] \leq (1 - \delta)^t$  for some  $\delta > 0$  depending only on  $\varepsilon$ .

To show this, we assume that this is not the case, and show by induction on s that then we may find coordinates  $i_1, i_2, \ldots, i_s$  such that  $\Pr\left[W_{i_s} \mid W_{i_1} \cap \ldots W_{i_{s-1}}\right] \leqslant 1 - \varepsilon/2 + O(\sqrt{\delta}) < 1 - \varepsilon/4$ . Once we show that we will be done, as then we get for s = t/100 that

$$\Pr\left[W\right] \leqslant \Pr\left[\bigwedge_{i=1}^{s} W_{i}\right] = \prod_{j=1}^{s} \Pr\left[W_{j} \mid \bigwedge_{i=1}^{j-1} W_{i}\right] \leqslant (1 - \varepsilon/4)^{s} \leqslant (1 - \varepsilon/4)^{t/100} < (1 - \delta)^{t}.$$

#### 2.2.2 Overview of the Argument

For s=1, the claim is obvious. We can take the coordinate i=1, and note that  $\Pr\left[W_1\right]$  is at most the probability the provers win in a single repetition game, which is at most  $1-\varepsilon$ . We now move on to the inductive part, which is where most of the action takes place. Suppose we proved the statement for  $s\geqslant 0$ , and let  $i_1,\ldots,i_s$  be the coordinates we found so far. Then, our goal is to find a new coordinate i such that even conditioned on winning coordinates  $i_1,\ldots,i_s$ , the probability the provers win coordinate i is still bounded away from 1.

To get some intuition, denote the event  $W_{\leqslant s} = W_{i_1} \cap \ldots W_{i_s}$ , and consider the distribution over the challenges conditioned on  $W_{\leqslant s}$ , that is the distribution of  $(\mathbf{X}, \mathbf{Y}) \mid W_{\leqslant s}$ . Intuitively, since the probability of  $W_{\leqslant s}$  is not very small, the overall amount of information it provides about the challenges is small, so for a typical coordinate i we get very little information about the challenge there.

To formalize this intuition, we used the tools we developed in information theory. Let us view the joint distribution of  $(\mathbf{X}, \mathbf{Y})$  as  $(\mathbf{U}_1, \dots, \mathbf{U}_t)$  where each  $\mathbf{U}_i$  is a uniformly chosen edge from G. Then by Claim 2.7

$$H(\mathbf{X}, \mathbf{Y} \mid W_{\leqslant s}) = H(\mathbf{U}_1, \dots, \mathbf{U}_t \mid W_{\leqslant s}) \geqslant H(\mathbf{U}_1, \dots, \mathbf{U}_t) - \log\left(\frac{1}{\Pr[W_{\leqslant s}]}\right).$$

Note that  $H(\mathbf{U}_1,\ldots,\mathbf{U}_t)=t\log(|E|)$ , and that  $\Pr\left[W_{\leqslant s}\right]\geqslant\Pr\left[W\right]\geqslant(1-\delta)^t$ , so we get that

$$H(\mathbf{U}_1, \dots, \mathbf{U}_t \mid W_{\leq s}) \geqslant t \log(|E|) - t \log\left(\frac{1}{1-\delta}\right),$$

and using  $\log(1/(1-\delta)) \le 2\delta$  which holds for sufficiently small  $\delta$ , we get that

$$H(\mathbf{U}_1,\ldots,\mathbf{U}_t\mid W_{\leqslant s})\geqslant t(\log(|E|)-2\delta).$$

Thus, thinking of this intuitively, this says that on average, on each one of the  $U_i$ 's we lost entropy of at most  $2\delta$  which is very little. We can formalize this by using the sub-additivity of entropy, namely Claim 2.6, to note that

$$H(\mathbf{U}_1,\ldots,\mathbf{U}_t\mid W_{\leqslant s})\leqslant \sum_{i=1}^t H(\mathbf{U}_i\mid W_{\leqslant s}),$$

so combining we get that

$$\frac{1}{t} \sum_{i=1}^{t} H(\mathbf{U}_i \mid W_{\leqslant s}) \geqslant \log(|E|) - 2\delta.$$

In particular, there exists  $i=1,\ldots,t$  such that  $H(\mathbf{U}_i\mid W_{\leqslant s})\geqslant \log(|E|)-2\delta$ , and by Claim 2.2 we get that  $\mathbf{U}_i\mid W_{\leqslant s}$  is close to uniform over E, namely that  $\mathsf{SD}(\mathbf{U}_i\mid W_{\leqslant s},\mathbf{U})\leqslant \sqrt{2\delta}$ .

Note that if coordinate i was sampled according to  $\mathbf{U}$  without the conditioning, the provers would win on it with probability at most  $1-\varepsilon$  by the assumption on the single repetition game. Above, we proved that the actual distribution over challenges they have is close to  $\mathbf{U}$ , hence we expect them to win on it with probability which is at most  $1-\varepsilon+\sqrt{2\delta}$ . This turns out to be true (up to little more error terms), but is non-trivial to prove and where much of the effort in the actual proof of the parallel repetition theorem. <sup>1</sup>

If we ignore all of these complications though, we have just proved that  $\Pr\left[W_i \mid W_{\leqslant s}\right] \leqslant 1 - \varepsilon + \sqrt{2\delta}$ , as we wished.

<sup>&</sup>lt;sup>1</sup>The reason is that to make this argument formal, we have to show that if the probability the provers win on coordinate i with high probability  $1 - \varepsilon/100$  and  $SD(\mathbf{U}_i \mid W_{\leqslant s}, \mathbf{U})$ , then one can use that to construct too good of a strategy to the basic game (with no repetition). To do that, one has to use the provers strategies, and in particular to be able to sample the rest of the coordinates of the game conditioned  $W_{\leqslant s}$ .

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lecture 16

#### Dor Minzer

Today, we prove it is NP-hard to approximate the set-cover problem within any constant factor.

# 1 The Set-cover Problem

An instance of the set cover problem consists of a universe  $\mathcal{U}$  as well as a collection subsets  $S_1, \ldots, S_m \subseteq \mathcal{U}$ . The goal is to find the smallest number of subsets, that is  $I \subseteq \{1, \ldots, m\}$  of smallest size, such that  $\{S_i\}_{i \in I}$  cover all of the universe  $\mathcal{U}$ , namely  $\bigcup_{i \in I} S_i = \mathcal{U}$ . Set cover is a classical NP-hard problem, and today we will study it via the approximation len.

## 1.1 An Approximation Algorithm for Set-cover: the Greedy Algorithm

The greedy algorithm for set cover is probably the first idea that comes to mind when first facing the problem. Starting with  $I=\emptyset$  and maintaining  $A=\mathcal{U}\setminus\bigcup_{i\in I}S_i$ , the idea is that at each step the algorithm picks the set  $S_i$  that covers as many of elements from A as possible, add i to I and continue. The following result states the performance of the greedy algorithm:

**Theorem 1.1.** Let  $(\mathcal{U}, \{S_i\}_{i \in I})$  be a set cover instance whose smallest cover has size k. Then the above greedy algorithm finds a set cover of size at most  $k \ln(|\mathcal{U}|)$ .

*Proof.* Let  $t \in \mathbb{N}$  be a parameter representing the step in the algorithm, let  $A_t$  be the set of uncovered elements in step t and let  $i_t$  be the index of the set we chose at that time. Consider a step t in the algorithm; since there is a set cover of  $\mathcal{U}$  consisting of k sets, there are k sets that cover  $A_t$ , so at least one of them covers at least 1/k fraction of the elements from  $A_t$ . Since we picked  $S_{i_t}$  greedily, it follows that  $|S_{i_t} \cap A_t| \geqslant \frac{|A_t|}{k}$ , hence

$$|A_{t+1}| = |A_t \setminus (A_t \cap S_{i_t})| = |A_t| - |A_t \cap S_{i_t}| \le \left(1 - \frac{1}{k}\right) |A_t|.$$

Thus,  $|A_t| \leqslant \left(1 - \frac{1}{k}\right)^t |\mathcal{U}|$  and taking  $t = k \ln(|\mathcal{U}|)$  we get that  $A_t = \emptyset$ , hence we end up with a cover.

In words, denoting  $n = |\mathcal{U}|$  to be the size of the universe of the set cover instance, we have shown that there is a  $\ln n$  approximation algorithm for set cover. Can one do better than this?

#### 1.2 $(\ell, m)$ -system sets: A Gadget for Set-cover

The rest of this lecture is devoted to establishing hardness of approximation results for set cover. To do that, we introduce a general framework in hardness of approximation, in which we first design a gadget — which is a mini instance of the problem we want to prove hardness for — that has a very good intended solution, but any other solution to it is significantly worse. We use this instance in a way that the "intended solutions" encode satisfying assignments to a label cover instance, and use it to do a reduction from label cover.

**Definition 1.2.** An  $(\ell, m, n)$  set system consists of a universe  $\mathcal{U}$  of size n and a collection of m sets  $A_1, \ldots, A_m$  and their complements  $B_1 = \overline{A_1}, \ldots, B_m = \overline{A_m}$ .

We say such collection forms an  $(\ell, m, n)$  instance if any collection of subsets  $\{A_i\}_{i \in I}$  and  $\{B_i\}_{i \in I'}$  that covers  $\mathcal{U}$  must contain a set and its complement, that is  $I \cap I' \neq \emptyset$ .

In words, an  $(\ell, m, n)$  set system is an instance of set cover that has a cover of size 2 (by taking a set and its complement), and any other cover (possibly much larger) must contain such cover. We have the following lemma proving the existence of  $(\ell, m, n)$  systems

**Lemma 1.3.** For all  $\ell \in \mathbb{N}$ , there is an  $(\ell, 2\ell, 2^{\ell})$  set system, and furthermore this system can be constructed in time  $2^{O(\ell)}$ .

*Proof.* Take  $\mathcal{U} = \{0,1\}^{\ell}$ , and define

$$A_i = \{ x \in \mathcal{U} \mid x_i = 0 \}, \qquad B_i = \{ x \in \mathcal{U} \mid x_i = 1 \}.$$

We leave it to the reader to verify this is an  $(\ell, 2\ell, 2^{\ell})$  set system.

# 2 A Reduction form Label-cover to Set-cover

We need the PCP theorem proved in previous lectures with an additional assumption of regularity. A bipartite graph  $G = (L \cup R, E)$  is called bi-regular if all of the vertices in L have the same degree, and all of the vertices in R have the same degree.

**Theorem 2.1.** For all  $\varepsilon > 0$ , there is  $k \in \mathbb{N}$  such that the problem gap-Label-Cover $[1, \varepsilon]$  is NP-hard on instances with alphabet size at most k and bi-regular constraint graphs.

We use Theorem 2.1 to prove a strong hardness of approximation result for set cover. It will be easier for us to work with weighted version of the set-cover problem; in the problem set, you will see that hardness for weighted set-cover can be converted to hardness for standard instances of set cover.

A weighted set cover instance is composed of a universe  $\mathcal{U}$ , a collection of sets  $S_1, \ldots, S_m \subseteq \mathcal{U}$  as well as a weight function  $w \colon \{1, \ldots, m\} \to [0, \infty)$  indicating, for each set  $S_i$ , its weight. The problem is to find the minimum weight set cover of  $\mathcal{U}$ , that is find  $I \subseteq \{1, \ldots, m\}$  such that  $(S_i)_{i \in I}$  cover all of the universe  $\mathcal{U}$ , and  $\sum_{i \in I} w(i)$  is as small as possible. We note that the standard set-cover problem corresponds to the case that the weight function w is the constant 1 function.

For  $a, b \in \mathbb{N}$ , we denote by gap-Weighted-set-cover[a, b] the problem in which one is given an instance of weighted set-cover that either has a cover of weight at most a, else all covers have weight at least b.

**Theorem 2.2.** For all  $\varepsilon > 0$ , there is  $\ell \in \mathbb{N}$  such that the problem gap-Weighted-set-cover $[\ell, \frac{\ell}{\varepsilon}]$  is NP-hard.

The rest of this section is devoted to the proof of Theorem 2.2.

#### 2.1 The Reduction from Label-cover to Set-cover

We show a reduction from gap-Label-cover  $[1, \varepsilon]$  and use Theorem 2.1 to finish off the proof. Namely, we show a polynomial time reduction that maps an instance  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \{\Phi_e\}_{e \in E})$  of Label-cover to an instance  $(\mathcal{U}, \{S_i\}_{i \in \mathcal{I}}, w)$  of weighted set cover such that:

<sup>&</sup>lt;sup>1</sup>We remark that the additional bi-regularity condition in 2.1 can be quite easily ensured elementary transformations.

- 1. If  $\Psi$  is satisfiable, then  $(\mathcal{U}, \{S_i\}_{i\in\mathcal{I}}, w)$  has a set cover of weight a = 2|L|.
- 2. If  $\Psi$  is at most  $\varepsilon$ -satisfiable, then  $(\mathcal{U}, \{S_i\}_{i\in\mathcal{I}})$  has no set-cover of weight  $b = \frac{1}{8\sqrt{\varepsilon}} |L|$ .

Choose  $\ell = |\Sigma_R|$ , and take an  $(\ell, 2\ell, 2^\ell)$  set system  $(A_1, \ldots, A_\ell, B_1, \ldots, B_\ell)$  with universe U as in Lemma 1.3. Re-labeling the indices, we think of the sets  $A_1, \ldots, A_\ell$  and  $B_1, \ldots, B_\ell$  as being indexed by  $\Sigma_R$  (in other words, we identify  $\{1, \ldots, \ell\}$  with  $\Sigma_R$ ).

The universe of the set cover instance. The universe of the set-cover instance we construct is tuples of edges from  $\Psi$  and universe elements of the set system, namely  $\mathcal{U} = E \times U$ .

The sets in the set cover instance. Recall that  $\Psi$  is a projection label cover, meaning that for every each  $e=(u,v)\in E$  we have a map  $\phi_e\colon \Sigma_L\to \Sigma_R$  such that  $\Phi_e=\{(\sigma,\phi_e(\sigma))\mid \sigma\in \Sigma_L\}$ . We define a set in our system,  $S_{u,\sigma_u}$  for each vertex  $u\in L$  and  $\sigma_u\in \Sigma_L$ , as well as a set  $S_{v,\sigma_v}$  for each  $v\in R$  and  $\sigma_v\in \Sigma_R$ . For  $v\in R$  and  $\sigma_v\in \Sigma_R$  we take

$$S_{v,\sigma_v} = \bigcup_{u:(u,v)\in E} \{e\} \times B_{\sigma_v}.$$

In words, we pick the B-set from our set system corresponding to  $\sigma_v$ , take several copies of it and attach to each one of them a name, which is the edge in the graph we associate it with.

For  $u \in L$  and  $\sigma_u \in \Sigma_L$ , we define

$$S_{u,\sigma_u} = \bigcup_{v:(u,v)\in E} \{e\} \times A_{\phi_{u,v}(\sigma_u)}.$$

In words, for each u and label for it  $\sigma_u$ , we go over the neighbours v of u in G, and consider the A-set in our set system corresponding to  $\phi_{u,v}(\sigma_u)$ . We take a union over these, but also attach a name to each copy representing the edge it came from.

The weight function. Finally, we describe the weight function. If G was a regular graph (as opposed to bi-regular), we could have picked the weight function to be the constant 1 function, but this is not necessarily the case. Tracing back the construction of the label cover instance, we expect the size of L to be much larger than the size of R, hence there are many more sets corresponding to L than to R, and the weight function we define aims at balancing this out. Specifically, we define  $w(S_{v,\sigma_v}) = \frac{|L|}{|R|}$  for each  $v \in R$  and  $\sigma_v \in \Sigma_R$  and  $w(S_{u,\sigma_u}) = 1$  for  $u \in L$  and  $\sigma_u \in \Sigma_L$ .

#### 2.2 High Level Idea of the Analysis

Before proceeding to the formal analysis of the reduction, we explain the high level idea of it, and for that it is best to assume that |L| = |R| so that the weight function can be ignored. Let us inspect an edge  $e \in E$  in  $\Psi$ , and consider ways to cover the universe elements associated with it. For that, writing e = (u, v), we can only pick sets generated either by u or by v. Further, note that in the definition of the  $S_u$ -sets we picked A's and in the definition of  $S_v$ -sets we picked B's, hence we may try to cover the universe element using the inteded cover in the set system. Inspecting, to do that we must pick  $S_{v,\sigma_v}$  and  $S_{u,\sigma_u}$  such that  $\phi_{u,v}(\sigma_u) = \sigma_v$ , namely pick up a pair of sets that were generated by a satisfying assignment of the edge e. Thus, the intended solution for our gadget set system can be utilized towards constructing a set cover (provided that we have a satisfying assignment of the edge).

However, by properties of our set system any pair collection of  $S_v$  and  $S_u$  sets that cover all universe elements from  $\{e\} \times U$  must follows this strategy to an extent. Indeed, by the properties of the set system, if we are forbidden from picking a pair  $S_{v,\sigma_v}$  and  $S_{u,\sigma_u}$  corresponding to satisfying assignment, we would not be able to cover all of the elements of U, and hence not all of the elements in  $\{e\} \times U$ .

With this in mind, the punchline is that the satisfying-assignment based cover can be executed so long as we have a satisfying assignment for  $\Psi$ , which then takes care of the completeness of the reduction. As for the soundness of the reduction, since  $\Psi$  has no good single assignment we cannot pick one global assignment for  $\Psi$  that would allow us to cover all edges. In fact, any collection of sets that comes from a global assignment will completely cover the elements of  $\{e\} \times U$  only for very few edges  $e \in E$  (since the label cover has small soundness). Thus, typically for a vertex  $u \in L$  and  $v \in R$  we would need to pick many of the sets it generated to get a complete cover.

### 2.3 The Completeness of the Reduction.

Suppose  $\Psi$  is satisfiable and let  $A_L\colon L\to \Sigma_L$  and  $A_R\colon R\to \Sigma_R$  be assignments that satisfy  $\Psi$ . We choose the sets |L|+|R| sets  $\{S_{u,A_L(u)}\}_{u\in L}$  and  $\{S_{v,A_R(v)}\}_{v\in R}$  and note that they form a set cover. Indeed, consider any element of the form  $(e,x)\in \mathcal{U}$  and write e=(u,v). Then we have picked the sets  $S_{u,A_L(u)}$  which contains  $\{e\}\times A_{\phi_{u,v}(A_L(u))}=\{e\}\times A_{A_R(v)}$  (where we used the fact that  $\phi_{u,v}(A_L(u))=A_R(v)$  since (u,v) is satisfied) and  $S_{v,A_R(v)}$  which contains  $\{e\}\times B_{A_R(v)}$ , and since  $A_{A_R(v)}\cup B_{A_R(v)}=U$ , at least one of these sets contains (e,x).

By the definition of the weight function, it follows we have a set cover of weight 2|L|.

#### 2.4 The Soundness of the Reduction

Next, we show the soundness of the reduction. Towards this end, assume that  $\Psi$  is at most  $\varepsilon$  satisfiable and that our set cover instance has cover C of weight at most  $\beta |L|$ . For  $u \in L$  and  $v \in R$  define

$$\mathsf{Labels}(u) = \{ \sigma_u \in \Sigma_R \mid S_{u,\sigma_u} \in \mathcal{C} \}, \qquad \mathsf{Labels}(v) = \{ \sigma_v \in \Sigma_R \mid S_{v,\sigma_v} \in \mathcal{C} \}.$$

In words, for each vertex in the graph we define the set of labels that are associated with sets that are in our set cover C. Then the total weight of the set cover instance is

$$\sum_{u \in L} |\mathsf{Labels}(u)| + \frac{|L|}{|R|} \sum_{v \in R} |\mathsf{Labels}(v)|,$$

and by assumption this is at most  $\beta |L|$ . Thus, we get that  $\sum_{u \in L} |\mathsf{Labels}(u)| \leqslant \beta |L|$  hence by an averaging argument for at least 3/4 of  $u \in L$  we have that  $|\mathsf{Labels}(u)| \leqslant 4\beta$ , and we refer to such vertices as good. Also,  $\frac{|L|}{|R|} \sum_{v \in R} |\mathsf{Labels}(v)| \leqslant 4\beta |L|$  hence  $\frac{1}{|R|} \sum_{v \in R} |\mathsf{Labels}(v)| \leqslant 4\beta$  so by an averaging argument for at least 3/4 of  $v \in R$  we have that  $|\mathsf{Labels}(v)| \leqslant 4\beta$ ; we also refer to such vertices as good.

Note that sampling  $e \in E$  and writing e = (u, v), by the bi-regularity of G, the vertex u is distributed uniformly in E and hence is good expect with probability 1/4, and v is distributed uniformly in E and hence is good expect with probability 1/4. Thus, both endpoints of E are good with probability at least 1/2, and we denote the set of these edges by  $E' \subseteq E$ . We will show an assignment that satisfies many of these edges.

The following claim says that if for every edge  $e = (u, v) \in E$ , the label sets Labels(u) and Labels(v) contain a pair of assignments that satisfy the constraint on e.

**Claim 2.3.** Let  $e \in E$  be any edge, and write e = (u, v). Then there are pairs of labels  $\sigma_u \in \mathsf{Labels}(u)$  and  $\sigma_v \in \mathsf{Labels}(v)$  that satisfy  $\Phi_e$ , namely such that  $(\sigma_u, \sigma_v) \in \Phi_e$ .

*Proof.* Otherwise, looking at the universe elements of the form (e,x), only the sets  $S_{v,\sigma}$  and  $S_{u,\sigma'}$  may cover them, and if there is no pair such as in the claim, then all of these sets from  $\mathcal{C}$  give us elements of the form  $\{e\} \times A_i$  for  $i \in I$  and  $\{e\} \times B_j$  for  $j \in J$  where  $I \cap J = \emptyset$ . By the properties of our set system,  $(A_i)_{i \in I}, (B_j)_{j \in J}$  do not form a cover of U, hence there is some  $x \in U$  not covered by them, and then  $(e,x) \in \mathcal{U}$  is not be covered.

The list decoding assignment. We are now ready to describe a good assignment for  $\Psi$  by an idea called list decoding. The idea that for edges  $e=(u,v)\in E'$ , the list of labels of u and v are short, and by Claim 2.3 contain a pair of satisfying assignment. Thus, if we pick a label for each vertex uniformly from its list, the probability that an edge  $e=(u,v)\in E'$  is satisfied is at least 1 over the product of the sizes of the lists of u and v, which is significant (as these lists are short).

More precisely, define  $A_L$  and  $A_R$  in a randomized manner;: for each  $u \in L$  independently, pick  $A_L(u) \in \mathsf{Labels}(u)$  uniformly, and for each  $v \in R$  pick  $A_R(v) \in \mathsf{Labels}(v)$  uniformly. We analyze the expected fraction of edges that  $A_L$  and  $A_R$  satisfy. Fix  $e \in E'$  and write e = (u, v). Then by Claim 2.3 there is a pair of labels  $\sigma_u^\star \in \mathsf{Labels}(u)$  and  $\sigma_v^\star \in \mathsf{Labels}(v)$  that satisfy the constraint between u and v, and we note that  $\Pr\left[A_L(u) = \sigma_u^\star\right] = \frac{1}{|\mathsf{Labels}(u)|} \geqslant \frac{1}{4\beta}$  since u is good. Similarly,  $\Pr\left[A_R(v) = \sigma_v^\star\right] \geqslant \frac{1}{4\beta}$ , and since these events are independent it follows that

$$\Pr[A_L, A_R \text{ satisfy } e] \geqslant \Pr[A_L(u) = \sigma_u^{\star}] \Pr[A_R(v) = \sigma_v^{\star}] \geqslant \frac{1}{16\beta^2}$$

Hence, by linearity of expectation, the expected number of constraints that  $A_L$  and  $A_R$  satisfy is at least  $\frac{|E'|}{16\beta^2} = \frac{|E|}{32\beta^2}$ , in particular it follows that there is an assignment to  $\Psi$  satisfying at least  $1/32\beta^2$  fraction of constraints. As  $\operatorname{val}(\Psi) \leqslant \varepsilon$ , it follows that  $\beta \geqslant \frac{1}{8\sqrt{\varepsilon}}$ . This finishes the soundness analysis.

#### 2.5 Reflecting on Theorem 2.2

One immediate corollary of Theorem 2.2 is that it is NP-hard to approximate the set-cover problem within any constant factor. In fact, it turns out that one can prove super-constant hardness of approximation results for set cover using this approach, and even get hardness of approximation result of up to factor  $\Theta(\log n)$ . To do that, one needs to make sure that  $\ell$  is a not-too-large-growing function of the instance size (which is the alphabet size of  $\Psi$ ), and that the soundness of the label-cover instance is vanishing with the instance size at sufficient rate (say  $\varepsilon = 1/\log n$ ). This is an example where PCPs with sub-constant soundness come in handy in hardness of approximation results, but we will not elaborate on this further.

We remark that by now it is known that it is NP-hard to approximate Set-cover within factor  $(1 - o(1)) \ln n$ , which is optimal by the greedy algorithm above.

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lectures 17-20

#### Dor Minzer

Today we present the long-code framework in hardness of approximation, and use it to prove several tight inapproximability results. En route, we give a brief introduction to discrete Fourier analysis over the Boolean hypercube.

# 1 Tight Inapproximability Results: Introduction

Our primary objective in the upcoming lectures will be to prove tight inapproximability results for the 3Lin and 3SAT problems that we already saw in lecture 1. Below, we give a brief introduction to these problems.

# 1.1 The Complexity of Linear Equations over Finite Fields

Linear equations over fields are probably one of the most basic object in mathematics. A first course in linear algebra typically begins with a few lectures discussion how to solve a system of linear equations over a field, conditions for a solution to exist and so on. Typically, the matrix ranking algorithm (Gaussian elimination) is presented, and throughout the course many more applications of this method are presented. Thus, it makes sense to consider the complexity of solving linear systems of equations over fields from a TCS view. Since objects need to have a finite description in computer-science, it makes sense that we will discuss finite fields; otherwise, we may run into issues such as how do we even represent real-numbers, which we wish to avoid.

Given a prime power q, consider the field  $\mathcal{F}_q$  and define the  $3\mathrm{Lin}_q$  problem as follows. An instance of the problem (X,E) consists of a set of variables  $X=\{x_1,\ldots,x_n\}$  that are supposed to be assigned with values from  $\mathbb{F}_q$ , as well as a set E of equations. Each equation  $e\in E$  is of the form  $a_{1,e}x_i+a_{2,e}x_j+a_{3,e}x_k=b_e$ , where  $a_{1,e},a_{2,e},a_{3,e},b_e$  are all field elements. Given an instance of  $3\mathrm{Lin}_q$ , the goal is to find an assignment  $A\colon X\to \mathbb{F}_q$  that satisfies as many of the equations as possible.

Given a system (X, E) promised to be fully satisfiable, we can use our favorite Gaussian elimination algorithm to efficiently find a satisfying assignment  $A \colon X \to \mathbb{F}_q$ . Writing this in gap problems notations, we conclude that gap- $3 \text{Lin}_q[1,1]$  is in the class P. What happens though, if instead of promising that the system (X,E) is satisfiable, we only promise that it is  $(1-\varepsilon)$ -satisfiable, where  $\varepsilon > 0$  is very small? Can we efficiently find a decent assignment for the instance in this case as well?

A quick inspection of the Gaussian elimination algorithm shows that it fails miserably, so we are back to the drawing board algorithmically. A naive idea one may try is to simply choose an assignment  $A \colon X \to \mathbb{F}_q$  randomly. That is, for each variable  $x_i$  in the system, choose the value of  $A(x_i)$  from  $\mathbb{F}_q$  uniformly; how well does this assignment perform? Fixing an equation  $e \in E$  in the system, say  $a_{1,e}x_i + a_{2,e}x_j + a_{3,e}x_k = b_e$ , we note that if at least one of the coefficients on the left hand side are non-zero, then the distribution of  $a_{1,e}A(x_i) + a_{2,e}A(x_j) + a_{3,e}A(x_k)$  is uniform over  $\mathbb{F}_q$ . Hence, that element will be equal to  $b_e$  with probability 1/q. Therefore, A satisfies the equation e with probability 1/q, so by linearity of expectation the expected number of equations that A satisfies is at least  $\frac{1}{q}|E|$ .

Given such "expectation guarantee", there are a few standard techniques often allow one to deduce a proper (often times, even deterministic) algorithm that achieves this expected value; you will see some of them in the problem set. For the  $3\mathrm{Lin}_q$  problem as above, it is indeed not hard to convert this algorithm that works "in expectation" to an algorithm that finds an assignment satisfying at least 1/q fraction of the equations; in any case, it follows that there is an assignment that satisfies at least 1/q fraction of the equations, hence gap- $3\mathrm{Lin}_q[1-\varepsilon,1/q]$  is also in P (regardless of what  $\varepsilon$  is).

Surely though, this naive algorithm can be improved? I doesn't even look at the system (X, E)!

**Theorem 1.1.** For all prime powers q, and for all  $\varepsilon, \delta > 0$ , the problem gap- $3Lin_q[1-\varepsilon, 1/q+\delta]$  is NP-hard.

In other words, the trivial algorithms above (the Gaussian elimination and the choose-a-random-assignment algorithms) are the best one can do for  $3\text{Lin}_q$ . We will prove Theorem 1.1 in the upcoming lectures, and for simplicity we will focus on the case that q=2.

## 1.2 The Complexity of 3SAT

The 3SAT problem is the poster NP-complete problem. Recall that a 3CNF formula consists of a set of variables  $X = \{x_1, \ldots, x_n\}$  and a formula over X,  $\phi(x_1, \ldots, x_n) = C_1 \wedge C_2 \wedge \ldots \wedge C_m$  wherein each clause  $C_i$  is of the form  $\alpha \vee \beta \vee \gamma$  where each one of  $\alpha, \beta, \gamma$  is a literal (a variable from X or its negation).

Viewing 3SAT as an optimization problem, given a 3CNF formula  $\phi(x_1,\ldots,x_n)$ , the goal is to find an assignment  $A\colon X\to\{0,1\}$  that satisfies as many of the clauses in  $\phi$  as possible. In this terminology, the Cook-Levin Theorem asserts that gap-3SAT[1,1] is NP-hard. Using the basic PCP theorem and some elementary ideas, one can show that there is  $\varepsilon>0$  such that gap-3SAT[1,1- $\varepsilon$ ] is NP-hard, meaning that given a satisfiable 3CNF formula  $\phi$ , it is NP-hard to find an assignment that satisfies at least  $1-\varepsilon$  of the clauses. In particular, it is NP-hard to approximate 3SAT within factor  $1-\varepsilon$  for some explicit (but small)  $\varepsilon>0$ . How well can one approximate 3SAT, though?

Well, we can try a random assignment idea again. Sample  $A: X \to \{0,1\}$  by taking  $A(x_i)$  to be a random bit chosen independently for each  $x_i \in X$ . Observe that each individual clause of the form  $C = (\alpha \lor \beta \lor \gamma)$  is satisfied with probability at least  $1 - 2^{-3} = 7/8$ , so in expectation A satisfies at least 7/8 of the clauses of  $\phi$ . Using standard techniques, one can convert this guarantee to a proper, efficient algorithm that given a formula  $\phi$  finds an assignment satisfying at least 7/8 of its clauses. Thus, gap-3SAT[1, 7/8] is in P. But surely, one can do better? The algorithm above doesn't even look at  $\phi$ !

**Theorem 1.2.** For all  $\varepsilon > 0$ , the problem gap-3Sat[1,  $7/8 + \varepsilon$ ] is NP-hard.

In other words, the choose-a-random-assignment algorithm is, once again, achieves the best possible approximation ratio by an efficient algorithm (assuming  $P \neq NP$ ). The techniques we show herein will can also be used to establish Theorem 1.2. We may prove a slightly weaker result to avoid some complications, though.

#### 1.3 The Long-code Paradigm

In this section, we begin the discussion about the Long-code paradigm, which is a general approach for proving hardness of approximation results using the PCP theorem. To motivate the discussion, we will consider a somewhat larger class of problems that include both 3SAT and 3Lin, and discuss the steps that one often has to take in order to prove hardness results for a problem in this class.

#### 1.3.1 Predicates and Testers that Use the Predicate

The 3SAT and the 3Lin problems are two examples of problems known as constraint satisfaction problems. There are several (non-equivalent) definitions of constraint satisfaction problem, and we present one which will help us for the purpose of this lecture. A (Boolean) constraint satisfaction problem is defined by a predicate  $P \colon \{0,1\}^r \to \{0,1\}$ , and an instance of it (X,E) consists of a set of variables  $X = \{x_1,\ldots,x_n\}$  as well as a set of constraints E. Each constraint has the form  $P(\alpha_1,\ldots,\alpha_r)=1$ , where  $\alpha_1,\ldots,\alpha_r$  are literals. The goal is to find an assignment  $A \colon X \to \{0,1\}$  that satisfies as many of the constraints of (X,E) as possible.

In this terminology, the 3Lin problem is the constraint satisfaction problem corresponding to the predicate P wherein r=3 and P(x,y,z)=1 if  $x+y+z=0 \pmod 2$ . The 3SAT problem is the constraint satisfaction problem with r=3 corresponding to the predicate  $P(x,y,z)=(x\vee y\vee z)$ .

To prove a hardness of approximation result for some predicate P, one needs to find a locally testable error correcting code, whose local tester performs checks that correspond to the predicate P. In other words, one needs to find a code  $C \subseteq \{0,1\}^N$  and a local tester  $\mathcal{T}$  that on input  $w=(w_1,\ldots,w_N)$ , samples r locations  $i_1,\ldots,i_r\in[N]$  (in a randomized way) from w and then checks that  $P'(w_{i_1},\ldots,w_{i_r})=1$ . Here P' is the same as the predicate P, except that we allow to apply negations on some coordinates; for example, P' may be defined as  $P'(x_1,\ldots,x_r)=P(1-x_1,x_2,\ldots,x_r)$ .

The tester  $\mathcal{T}$  should accept codewords from C with high probability, say c (which is typically 1 or close to it). For weak hardness results, it suffices to show that if the tester  $\mathcal{T}$  accepts w with probability close to c, then w is close to a codeword. For strong hardness results, one needs to venture into the list decoding regime, and show that if the tester  $\mathcal{T}$  accepts w with probability at least s (which may be much smaller than c), then w is "correlated" with some codeword from C. Indeed, the quality of the eventual hardness result we will get will be s/c. Thus, the ratio between s and c that we are able to achieve determines the quality of the hardness result we prove, so we will try to get s and c to be far from each other..

Remark 1.3. We stress that, as far as we know, finding such a code and a test is not sufficient for proving a hardness of approximation result. Indeed, in the coming lectures we will develop such code and test that have parameters that correspond to the requirement needed from Theorem 1.1, but we will need to work harder to turn this into a proof of Theorem 1.1. There is a well known conjecture in TCS, called the Unique-Games Conjecture, which if true would say that any code and test and above would yield a hardness of approximation result with matching parameters automatically, and we may discuss it later in the course.

#### 1.3.2 One Code for all Testers

So, does it mean that for every single new constraint satisfaction problem we face, we need to come up with a new code and a new local tester  $\mathcal{T}$ ? For the tester  $\mathcal{T}$  this is inevitable, since the tester itself has to only performs checks that correspond to the predicate we want to prove hardness for. For the code, though, there is no a-priori reason there would not be one, universal, nice enough could that would be rich enough to facilitate local testers of many different forms.

And indeed, ideally, we would like to have a single code C that will work for all hardness results, so that at each time we only have to be concerned with designing the tester  $\mathcal{T}$ . Intuitively, the best chance for us to achieve such property is if the code C is maximally "redundant". Namely, the information in a codeword is so well spread so well that we can access or decode any part of it by applying any predicate on several

<sup>&</sup>lt;sup>1</sup>The word correlated here appears with quotation marks since we will not actually be able to achieve correlation with a codeword, but some other notion of list-decodability that will be sufficient for our purpose.

well-chosen coordinates of it. Indeed, this is because we want to facilitate many completely different local tests (one for each predicate P), and this raises the question of what is the Boolean code C that has the most redundancies? A good candidate for such a code would be a code C of the worst possible rate (ignoring trivialities such as repetition codes). This code has a name: it is called the Long-code (the word "long" precisely describes the fact that the encoding of an element there is very, very long), and we formally define it below:

**Definition 1.4** (The Long-code). Let  $n \in \mathbb{N}$  and let  $i \in \{1, ..., n\}$ . The long code encoding of i is the truth table of the function  $f_i \colon \{0,1\}^n \to \{0,1\}$  defined by  $f_i(x) = x_i$ . The long-code is the set  $\mathsf{LC} = \{(f_i(x))_{x \in \{0,1\}^n} \mid i \in [n] \}$ .

Thus, for each coordinate  $i \in [n]$ , we encode i by the truth table of the dictatorship function  $f_i(x) = x_i$  over  $\{0,1\}^n$ , which is a string of length  $2^n$  bits. In other words, we encode a string of  $\log n$  bit (the index i) by a string of length  $2^n$ . Thus, the encoding of an index i is doubly exponential in the length of i, so indeed this code has a very bad rate hence many "redundancies". This used to be not-so-good for us early on in the course, but in the upcoming lectures it will be crucial for proving Theorem 1.1.

In the literature, local testers for the long code are often referred to as dictatorship tests. The reason for that comes from social choice theory. We can think of a Boolean function  $f: \{0,1\}^n \to \{0,1\}$  as a voting scheme wherein there are n-voters. Voter i casts their vote  $x_i$  between two candidates, 0 and 1, and the function f is then applied to aggregate all of these votes: the winner of the elections is candidate  $f(x_1,\ldots,x_n)$ . With this in mind, the function  $f_i$  in the definition of the long-code really merits the name "dictatorship"; the outcome of the scheme would always be the opinion of the i<sup>th</sup> voter, regardless of the opinions of the rest.

# 2 Designing a Dictatorship Test for 3Lin

In this section, we develop a dictatorship test for the 3Lin problem.

So, our goal is to query a given function  $f \colon \mathbb{F}_2^n \to \mathbb{F}_2$  in 3 locations, check some linear equation on them, and say whether f is a long-code codeword or not based on it. Where do we even start? Well, this is not clear, but we have already seen something similar to that earlier in the course. More specifically, we saw a local tester for the Hadamard code over  $\mathbb{F}_2$ . Recall that in the Hadamard code, for each  $\alpha \in \mathbb{F}_2^n$  we have a codeword, which is the truth table of  $h_\alpha \colon \mathbb{F}_2^n \to \mathbb{F}_2$  defined by  $h_\alpha(x) = \langle \alpha, x \rangle$ . We saw a local tester for the Hadamard code, which given oracle access to a supposed codeword  $f \colon \mathbb{F}_2^n \to \mathbb{F}_2$ , samples  $x, y \in \mathbb{F}_2^n$  uniformly, and checks that f(x) + f(y) = f(x+y). We saw that if f is a Hadamard codeword, then the test passes with probability 1, and if the test passes with probability  $\geqslant 1 - \varepsilon$  for  $\varepsilon < 1/8$ , then f is  $2\varepsilon$ -close to a Hadamard codeword.

Note that the long-code is a sub-code of the Hadamard code; indeed,  $f_i = h_\alpha$  for  $\alpha = e_i$ . Thus, we can use the above test to ensure that codewords will be accepted, and narrow down the class of functions that perform well in the test to functions close to  $h_\alpha$  for some  $\alpha \in \mathbb{F}_2^n$ . This is a good start, but for the test to be useful for us for the purpose of Theorem 1.1, we need to improve this tester in two ways:

- 1. We would like to be able to argue about functions that pass the test with probability  $s=1/2+\delta$  (as opposed to probability close to 1) because we want to get a strong hardness result for 3Lin.
- 2. We would like to narrow down further the functions that perform well in the test, and (roughly) only allow such functions to be  $h_{\alpha}$  for  $\alpha$  of small Hamming weight. Ideally, we would have liked to only allow  $\alpha$  to have Hamming weight 1 (and thus be a long-code codeword), but we will not be able to do

so. Still, if we manage to guarantee  $\alpha$  to have constantly small Hamming weight, this will correspond to at most constantly many long-code codewords.

# 2.1 Analyzing the Linearity Test in the List Decoding Regime

We start off by resolving the first issue, and present an analysis of the linearity tester in the small soundness regime. That is, we have a function  $f: \{0,1\}^n \to \{0,1\}$  such that

$$\Pr_{x,y \in \mathbb{F}_2^n} [f(x) + f(y) = f(x+y)] = \frac{1}{2} + \delta, \tag{1}$$

and we would like to argue that f must have some Hadamard-ish codeword behaviour. As we saw earlier in the course, if  $\delta$  is close to 1/2, then f must be close to some Hadamard codeword  $h_{\alpha}$ . In the current context, when  $\delta$  is thought of as positive (but small) constant, it is natural to expect that f will be correlated with Hadamard codeword  $h_{\alpha}$ . This turns out to be true, and for that we will need some basic tools from discrete Fourier analysis. <sup>2</sup>

Fix f as above, and let  $\alpha \in \mathbb{F}_2^n$ . We want to show that f and  $h_v$  are correlated, namely that for some  $\alpha$  the number

$$c_{\alpha} = \Pr_{x \in \mathbb{F}_2^n} [f(x) = h_{\alpha}(x)] - \Pr_{x \in \mathbb{F}_2^n} [f(x) \neq h_{\alpha}(x)]$$

is bounded away from 0. We re-write  $c_{\alpha}$  in a more suggestive form, and for that purpose we first observe that  $(-1)^{f(x)+h_{\alpha}(x)}=1$  if  $f(x)=h_{\alpha}(x)$  and -1 otherwise. Therefore,

$$c_{\alpha} = \mathbb{E}_{x \in \mathbb{F}_{2}^{n}} \left[ (-1)^{f(x) + h_{\alpha}(x)} \right] = \mathbb{E}_{x \in \mathbb{F}_{2}^{n}} \left[ (-1)^{f(x)} (-1)^{h_{\alpha}(x)} \right].$$

The last expectation looks like the  $L_2$  inner product between two functions, which are  $(-1)^{f(x)}$  and  $(-1)^{h_{\alpha}(x)}$ . This suggests that it may be a good idea to define a certain vector space with the  $L_2$  inner product on it, and use some tools from linear algebra to study it. This is indeed the case, but to make our lives (and notations) easier, it is convenient to switch to  $(\{1, -1\}, \cdot)$  notations as opposed to  $(\{0, 1\}, + \pmod{2})$  notations.

# **2.1.1** The Notational Switch: Going from $\{0,1\}$ to $\{1,-1\}$

Instead of working with bits  $b \in \{0,1\}$ , it will be more convenient for us to work with signs,  $(-1)^b \in \{1,-1\}$  (thus, 1 represents 0 and -1 represents 1). Thus, instead of thinking about the function  $f:\{0,1\}^n \to \{0,1\}$ , we can think of  $F:\{-1,1\}^n \to \{-1,1\}$  defined by  $F(z)=(-1)^{f(z)}$  where  $z_i=(-1)^{x_i}$  for each i. Also, instead of thinking about the function  $h_\alpha$ , we will think of the function  $\chi_\alpha:\{-1,1\}^n \to \{-1,1\}$ , defined as  $\chi_\alpha(z)=(-1)^{h_v(x)}$  where  $z_i=(-1)^{x_i}$ . Note that  $\chi_\alpha$  takes the form:

$$\chi_{\alpha}(z) = (-1)^{\langle \alpha, x \rangle} = (-1)^{\sum_{i:\alpha_i=1}^{\sum} x_i} = \prod_{i:\alpha_i=1} (-1)^{x_i} = \prod_{i:\alpha_i=1}^{i} z_i,$$

namely addition modulo 2 translated into multiplying signs. The function  $\chi_{\alpha}$  often goes by the name character (it has a special meaning when viewed as a homomorphism from  $\mathbb{F}_2$  to reals with absolute value 1), and we will adopt this terminology. We note that with these notations, the parameter  $c_{\alpha}$  we considered earlier takes a nice form:  $c_{\alpha} = \mathbb{E}_{z \in \{-1,1\}^n} \left[ F(z) \chi_{\alpha}(z) \right]$ .

<sup>&</sup>lt;sup>2</sup>We remark that discrete Fourier analysis is a rich enough topic to merit a separate course, so our presentation here will naturally be very partial.

#### 2.1.2 Discrete Fourier Analysis

Now that we presented the quantity we wish to study as an inner product, we formally define the inner product space that we work with and state some basic properties of it.

**Definition 2.1.** We define the inner product between real-valued functions over  $\{-1,1\}^n$  as follows. For functions  $F,G:\{-1,1\}^n \to \mathbb{R}$ , define

$$\langle F, G \rangle = \underset{z \in \{-1,1\}^n}{\mathbb{E}} [F(z)G(z)].$$

It is easy to check that this definition satisfies all of the properties of inner product, so now we can think of the space of real-valued functions over  $\{-1,1\}^n$  as a vector space equipped with an inner product structure; we shall denote this space by  $L_2(\{-1,1\}^n)$ . We note that the dimension of  $L_2(\{-1,1\}^n)$  is  $2^n$ .

So why do inner products arise from considering functions f that satisfy (1)? Is there anything special about the functions  $\chi_v$  with respect to this inner product that would explain the conclusion we are expecting to get? First, note that for all  $\alpha \in \mathbb{F}_2^n$ ,

$$\|\chi_{\alpha}\|_{2}^{2} = \langle \chi_{\alpha}, \chi_{\alpha} \rangle = \underset{z \in \{-1,1\}^{n}}{\mathbb{E}} \left[ \chi_{\alpha}(z) \chi_{\alpha}(z) \right] = \underset{z \in \{-1,1\}^{n}}{\mathbb{E}} \left[ \chi_{\alpha}(z)^{2} \right] = \underset{z \in \{-1,1\}^{n}}{\mathbb{E}} \left[ 1 \right] = 1,$$

so each  $\chi_{\alpha}$  is a unit vector in this vector space. Second, note that if  $\alpha = \vec{0}$ ,  $\chi_{\alpha}$  is the constant 1 function, and if  $\alpha \neq \vec{0}$ , then

$$\mathbb{E}_{z}[\chi_{\alpha}(z)] = \mathbb{E}_{z}\left[\prod_{i:\alpha_{i}\neq 0} z_{i}\right] = \prod_{i:\alpha_{i}\neq 0} \mathbb{E}_{z}[z_{i}] = 0,$$

so  $\chi_{\alpha}$  has average 0 (and hence is orthogonal to  $\chi_{\vec{0}}$ . Third, for  $\alpha, \alpha' \in \mathbb{F}_2^n$  we have

$$\chi_{\alpha}(z)\chi_{\alpha'}(z) = \prod_{i:\alpha_i=1} z_i \cdot \prod_{i:\alpha_i'=1} z_i = \prod_{\substack{i \text{ such that} \\ \alpha_i=1,\alpha_i'=0 \text{ or} \\ \alpha_i=0,\alpha':=1}} z_i = \chi_{\alpha \oplus \alpha'}(z),$$

so if  $\alpha \neq \alpha'$  then  $\langle \chi_{\alpha}, \chi_{\alpha'} \rangle = \mathbb{E}_{z \in \{-1,1\}^n} \left[ \chi_{\alpha}(z) \chi_{\alpha'}(z) \right] = \mathbb{E}_{z \in \{-1,1\}^n} \left[ \chi_{\alpha \oplus \alpha'}(z) \right] = 0$ . In other words, we have just shown the following lemma:

**Lemma 2.2.** The set  $\{\chi_{\alpha}\}_{{\alpha}\in\mathbb{F}_2^n}$  is an orthonormal set in  $L_2(\{-1,1\}^n)$ .

With Lemma 2.2 and our earlier observation that the dimension of  $L_2(\{-1,1\}^n)$  is  $2^n$ , we get that the set  $\{\chi_\alpha\}_{\alpha\in\mathbb{F}_2^n}$  is an *orthonormal basis* for  $L_2(\{-1,1\}^n)$ . Therefore, given any real-valued function over  $\{-1,1\}^n$ , say  $G\colon\{-1,1\}^n\to\mathbb{R}$ , we can represent G as a linear combination of  $\chi_\alpha$ :

$$G(z) = \sum_{\alpha \in \mathbb{F}_2^n} \widehat{G}(\alpha) \chi_{\alpha}(z).$$

The coefficients  $\widehat{G}(\alpha)$  are called the Fourier coefficients of G. As  $\chi_{\alpha}$  is an orthonormal basis, we can say a few things about the coefficients of G:

1. Parseval's equality: we have a basic result known as Parseval's equality, which asserts that

$$\mathbb{E}_{z}\left[G(z)^{2}\right] = \langle G, G \rangle = \left\langle \sum_{\alpha \in \mathbb{F}_{2}^{n}} \widehat{G}(\alpha) \chi_{\alpha}, \sum_{\alpha' \in \mathbb{F}_{2}^{n}} \widehat{G}(\alpha') \chi_{\alpha'} \right\rangle = \sum_{\alpha, \alpha' \in \mathbb{F}_{2}^{n}} \widehat{G}(\alpha) \widehat{G}(\alpha') \left\langle \chi_{\alpha}, \chi_{\alpha'} \right\rangle = \sum_{\alpha \in \mathbb{F}_{2}^{n}} \widehat{G}(\alpha)^{2}.$$

In particular, if G has 2-norm equal to 1 (as in our case of interest, wherein G will be  $\pm 1$  valued), then the sum of squares of Fourier coefficients of G is also 1.

2. A formula for the Fourier coefficients: for any  $\alpha \in \mathbb{F}_2^n$  we have that

$$\langle G, \chi_{\alpha} \rangle = \left\langle \sum_{\alpha' \in \mathbb{F}_2^n} \widehat{G}(\alpha') \chi_{\alpha'}, \chi_{\alpha} \right\rangle = \sum_{\alpha' \in \mathbb{F}_2^n} \widehat{G}(\alpha') \left\langle \chi_{\alpha'}, \chi_{\alpha} \right\rangle = \widehat{G}(\alpha).$$

Hence, a Fourier coefficient  $\widehat{G}(\alpha)$  is the inner product of G with the corresponding basis function  $\chi_{\alpha}$ .

In particular, from the last remark it follows that the parameters  $c_{\alpha}$  that we defined earlier are none other than the Fourier coefficients of the function F! It therefore makes sense that the above inner product perspective will be useful for us to understand functions satisfying (1) (provided that, indeed, our guess that it implies correlation with a Hadamard codeword is indeed correct). But how do we do that?

Well, the first step is to phrase (1) in terms of the function F instead of f, and a quick inspection shows that it is equivalent to

$$\Pr_{x,y \in \{-1,1\}} \left[ F(x)F(y) = F(xy) \right] \geqslant \frac{1}{2} + \delta, \tag{2}$$

where  $(xy)_i = x_iy_i$ . Still, it is not clear how to apply our inner-product Fourier machinery, and we need to arithmetize this probability statement into an expectation statement. Note that given (2), we get that

$$\Pr_{x,y \in \{-1,1\}} \left[ F(x)F(y) \neq F(xy) \right] \leqslant \frac{1}{2} - \delta,$$

SC

$$\mathbb{E}_{x,y \in \{-1,1\}^n} \left[ F(x)F(y)F(xy) \right] = \Pr_{x,y \in \{-1,1\}} \left[ F(x)F(y) = F(xy) \right] - \Pr_{x,y \in \{-1,1\}} \left[ F(x)F(y) \neq F(xy) \right] \geqslant 2\delta.$$

We can now try to plug in our Fourier expansion for F and hope for the best. Indeed, we write

$$F(x) = \sum_{\alpha \in \mathbb{F}_2^n} \widehat{F}(\alpha) \chi_{\alpha}(x), \qquad F(y) = \sum_{\beta \in \mathbb{F}_2^n} \widehat{F}(\beta) \chi_{\beta}(y), \qquad F(xy) = \sum_{\gamma \in \mathbb{F}_2^n} \widehat{F}(\gamma) \chi_{\gamma}(xy),$$

and note that  $\chi_{\gamma}(xy) = \chi_{\gamma}(x)\chi_{\gamma}(y)$ . We get that

$$\mathbb{E}_{x,y\in\{-1,1\}^n}[F(x)F(y)F(xy)] = \mathbb{E}_{x,y\in\{-1,1\}^n}\left[\sum_{\alpha,\beta,\gamma\in\mathbb{F}_2^n}\widehat{F}(\alpha)\widehat{F}(\beta)\widehat{F}(\gamma)\chi_{\alpha}(x)\chi_{\beta}(y)\chi_{\gamma}(x)\chi_{\gamma}(y)\right]$$

$$= \mathbb{E}_{x,y\in\{-1,1\}^n}\left[\sum_{\alpha,\beta,w\in\mathbb{F}_2^n}\widehat{F}(\alpha)\widehat{F}(\beta)\widehat{F}(\gamma)\chi_{\alpha\oplus\gamma}(x)\chi_{\beta\oplus\gamma}(y)\right]$$

$$= \sum_{\alpha,\beta,\gamma\in\mathbb{F}_2^n}\widehat{F}(\alpha)\widehat{F}(\beta)\widehat{F}(\gamma)\mathbb{E}_{x,y\in\{-1,1\}^n}\left[\chi_{\alpha\oplus\gamma}(x)\chi_{\beta\oplus\gamma}(y)\right]$$

$$= \sum_{\alpha,\beta,\gamma\in\mathbb{F}_2^n}\widehat{F}(\alpha)\widehat{F}(\beta)\widehat{F}(w)\mathbb{E}_{x\in\{-1,1\}^n}\left[\chi_{\alpha\oplus\gamma}(x)\right]\mathbb{E}_{y\in\{-1,1\}^n}\left[\chi_{\beta\oplus\gamma}(y)\right].$$

Note that unless  $\alpha = \beta = \gamma$  the corresponding summand is 0, hence we get that

$$2\delta \leqslant \mathop{\mathbb{E}}_{x,y \in \{-1,1\}^n} \left[ F(x) F(y) F(xy) \right] = \sum_{\alpha \in \mathbb{F}_2^n} \widehat{F}(\alpha)^3.$$

By Parseval's equality, the squares of  $\widehat{F}(\alpha)$  sum up to 1, so if they were all very small, the sum of third powers would be even smaller. This says that at least one of these numbers is large; indeed:

$$2\delta \leqslant \sum_{\alpha \in \mathbb{F}_n^n} \widehat{F}(\alpha)^3 \leqslant \max_{\alpha} \widehat{F}(\alpha) \cdot \sum_{\alpha \in \mathbb{F}_n^n} \widehat{F}(\alpha)^2 = \max_{\alpha} \widehat{F}(\alpha).$$

Thus, we have just proved the following theorem.

**Theorem 2.3.** Suppose  $F: \{-1,1\}^n \to \{-1,1\}$  satisfies that  $\Pr_{x,y \in \{-1,1\}} [F(x)F(y) = F(xy)] \geqslant \frac{1}{2} + \delta$ . Then there exists  $\alpha \in \mathbb{F}_2^n$  such that  $\widehat{F}(\alpha) \geqslant 2\delta$ .

Tracing back, we see that

$$\Pr_{x} [f(x) = h_{\alpha}(x)] = \frac{1}{2} (1 + c_{\alpha}) = \frac{1}{2} (1 + \widehat{F}(\alpha)) \geqslant \frac{1}{2} + \delta,$$

so Theorem 2.3 gives a positive answer to our guess, and indeed any f satisfying (1) must be correlated with a Hadamard codeword. We are therefore done arguing about the first item in Section 2.

In the future, we may need an additional property regarding Fourier coefficients that is related to this test. In words, Theorem 2.3 guarantees that under the condition specified therein, there is a Fourier character on which F has a significant coefficient. Can there be many such Fourier coefficients?

**Lemma 2.4.** Suppose  $F: \{-1,1\}^n \to \{-1,1\}$  is any function, and let  $\varepsilon > 0$ . Then the number of  $\alpha$ 's such that  $\widehat{F}(\alpha) \geqslant \varepsilon$  is at most  $1/\varepsilon^2$ .

*Proof.* Denoting the number of these v's by k, we note that by Parseval's equality,

$$1 = \mathop{\mathbb{E}}_{z} \left[ F(z)^{2} \right] = \sum_{\alpha} \widehat{F}(\alpha)^{2} \geqslant k\varepsilon^{2},$$

and re-arranging gives  $k \leq 1/\varepsilon^2$ .

Next, we shift our attention to the second item in Section 2.

#### 2.2 The Noisy Linearity Test

Theorem 2.3 gives us a tester for the Hadamard code which almost fits the conditions stated in 1.3. The main difference is that in the soundness, we managed to show correlation with a Hadamard codeword, as opposed to correlation with a long-code codeword. As discussed earlier, we will not be able to fully resolve this issue under the standard notion of what "correlation" is; there are less standard notions which we will be able to achieve. For the moment, we will adapt an ad hoc ad approach, but remark that the more principled notions are concerned with parameters called "influences" and "low-degree influences" of a function; we may discuss them at a later point in the course.

So, how do we turn Theorem 2.3 into a result that at least somewhat resembles correlation with a long code word? Well, morally speaking, our goal here is to distinguish between functions of the form  $\chi_v$  for v which has large cardinality (we will want to penalize them so that the test rejects them often), and functions  $\chi_v$  for which the cardinality of v is small.

## 2.2.1 Applying Noise

To motivate our approach consider the  $\alpha=e_1$ , so that  $\chi_{\alpha}(z)=z_1$ , and  $\alpha=e_1+\ldots+e_r$ , where r is a large constant, so that  $\chi_{\alpha}(z)=z_1\cdots z_r$ . Suppose we have an input  $z\in\{-1,1\}^n$ , and we lightly perturb it to arrive at an input  $z'\in\{-1,1\}^n$ . By that, we mean that we take an  $\varepsilon$ -biased distributed  $a\in\{-1,1\}^n$ , meaning that  $a_i=1$  with probability  $1-\varepsilon$  and otherwise  $a_i=-1$ , and define z'=az. What can we say about  $\chi_{\alpha}(z)$  and  $\chi_{\alpha}(z')$  in the two cases above?

- 1. If  $\alpha = e_1$ , then  $\chi_{\alpha}(z') = a_1 z_1 = a_1 \chi_v(z)$ , so  $\chi_{\alpha}(z') = \chi_v(z)$  with probability  $1 \varepsilon$ . Thus, the values of the function on these two points are very correlated.
- 2. If  $\alpha=e_1+\ldots+e_r$ , then  $\chi_\alpha(z')=\chi_\alpha(z)\prod_{i=1}^r a_i$ . Looking at  $\prod_{i=1}^r a_i$  and thinking of r as a large constant, the distribution of the products seems to be close to uniform in  $\{-1,1\}$ . Indeed, if  $r>1/\varepsilon$  we expect there would be few -1's among  $a_1,\ldots,a_r$ , and if r is much larger than that we expect that the probability there would be an odd number of -1's to be roughly 1/2. This turns out to be true, hence if  $r>r_0(\varepsilon)$ , the values  $\chi_\alpha(z')$  and  $\chi_\alpha(z)$  are barely correlated.

The above observation points out to a property that distinguishes Hadamard codewords corresponding to v of small support size (which we think of as long-code words), and Hadamard codewords corresponding to v of large support size. This property is called noise sensitivity.

Upon seeing this, a natural test to consider would be: (1) apply the linearity test, that is, choose  $x, y \in \{-1, 1\}^n$  and check that F(x)F(y) = F(xy), and (2) apply the noise test, that is, choose  $a \in \{-1, 1\}^n$  which is  $\varepsilon$ -biased, and check that F(xa) = F(x). This combined test can be shown to work (well, almost), in the sense that long-code codewords pass it with probability  $1 - \varepsilon$ , and if the test passes with probability  $1/2 + \varepsilon$  on F, then F is correlated with  $\chi_v$  for v of small cardinality.

The primary issue with this test is that it is no longer of a 3Lin form. We are making an AND of two linear equations, which is no longer a linear equation. Hence we cannot use it to prove hardness for 3Lin. To resolve this issue, we need to incorporate the noise test into the linearity test.

#### 2.2.2 Incorporating the Noise Test into the Linearity Test

We now present a single test that combines the linearity test and the noise test together. The test picks  $x,y \in \{-1,1\}^n$  uniformly and independently, and  $a \in \{-1,1\}^n$  according to the  $\varepsilon$ -biased distribution independently, and checks that F(axy) = F(x)F(y). We call this the noisy linearity test, and with respect to it we have the following theorem:

**Theorem 2.5.** Let  $F: \{-1,1\}^n \to \{-1,1\}$  be a function, and  $\varepsilon > 0$ .

- 1. If F is a long-code codeword, that is,  $F(x) = x_i$  for some  $i \in [n]$ , then the noisy linearity tester passes with probability  $1 \varepsilon$ .
- 2. If F passes the noisy linearity tester with probability  $1/2 + \delta$ , then there is  $\alpha \in \mathbb{F}_2^n$  such that

$$(1-2\varepsilon)^{|\alpha|}\widehat{F}(\alpha) \geqslant 2\delta.$$

In particular, there is  $\alpha$  of size at most  $\frac{\ln(1/\delta)}{2\varepsilon}$  such that  $\widehat{F}(\alpha) \geqslant 2\delta$ .

*Proof.* For the first item, suppose that  $F(x) = x_i$ . Note that the test passes if and only if  $a_i = 1$ , which happens with probability  $1 - \varepsilon$ , and the first item is proved.

For the second item, note that under the assumption we have that

$$\mathop{\mathbb{E}}_{x,y,a} \left[ F(axy)F(x)F(y) \right] \geqslant 2\delta.$$

We now use the Fourier expansion of F as in Theorem 2.3. We have

$$\mathbb{E}_{x,y\in\{-1,1\}^n,a}\left[F(x)F(y)F(axy)\right] = \mathbb{E}_{x,y\in\{-1,1\}^n,a}\left[\sum_{\alpha,\beta,\gamma\in\mathbb{F}_2^n}\widehat{F}(\alpha)\widehat{F}(\beta)\widehat{F}(\gamma)\chi_{\alpha}(x)\chi_{\beta}(y)\chi_{\gamma}(x)\chi_{w}(y)\chi_{\gamma}(a)\right] \\
= \sum_{\alpha,\beta,w\in\mathbb{F}_2^n}\widehat{F}(\alpha)\widehat{F}(\beta)\widehat{F}(\gamma)\mathbb{E}_{x}\left[\chi_{\alpha\oplus\gamma}(x)\right]\mathbb{E}_{y}\left[\chi_{\beta\oplus\gamma}(y)\right]\mathbb{E}_{a}\left[\chi_{\gamma}(a)\right].$$

As before, unless  $\alpha = \beta = \gamma$  the corresponding summand is 0. As for the expectation over a, we have

$$\mathbb{E}_{a}\left[\chi_{\gamma}(a)\right] = \mathbb{E}_{a}\left[\prod_{i:\gamma_{i}=1}a_{i}\right] = \prod_{i:\gamma_{i}=1}\mathbb{E}_{a}\left[a_{i}\right] = \prod_{i:\gamma_{i}=1}(1-2\varepsilon) = (1-2\varepsilon)^{|\gamma|}.$$

Combining, we get that

$$2\delta \leqslant \underset{x,y \in \{-1,1\}^n,a}{\mathbb{E}} \left[ F(x)F(y)F(axy) \right] \leqslant \underset{\alpha \in \mathbb{F}_2^n}{\sum} (1-2\varepsilon)^{|\alpha|} \widehat{F}(\alpha)^3 \leqslant \underset{\alpha}{\max} (1-2\varepsilon)^{|\alpha|} \widehat{F}(\alpha) \underset{\alpha \in \mathbb{F}_2^n}{\sum} \widehat{F}(\alpha)^2,$$

and the proof is concluded by appealing to Parseval's equality to say that 
$$\sum_{\alpha \in \mathbb{F}_2^n} \widehat{F}(\alpha)^2 = 1$$
.

Theorem 2.5 is an important milestone towards proving the hardness of approximation of 3Lin, and provided a very strong form of the PCP theorem called Unique-Games PCPs (which is conjectured to exists but not known), it implies Theorem 1.1 almost immediately.

To see a proper NP-hardness result though we will need to work harder. This will also allow us to see where the structure of the constraints in our PCP theorem enters the picture at all.

# 3 Utilizing the Long-code Encoding in PCPs

#### 3.1 Local Testing and Verifying Constraints via the Long-code

Having designed a dictatorship tester that fits the mold in Section 1.3, we now try to understand how this is all related to getting a hardness of approximation result for 3Lin using the PCP theorem. Our intention is to use the ideas above to carry out a reduction from the label cover problem to the 3Lin problem, so let us think of a label cover instance  $\Psi = (L \cup R, E, \Sigma_L, \Sigma_R, \{\Phi_e\}_{e \in E})$ . Therein, we are supposed to assign a label from  $\Sigma_L$  to each vertex  $u \in L$ , and a label from  $\Sigma_R$  to each vertex from  $v \in R$ . In our reduction, we will attempt to encode the labels for the vertices of  $\Psi$  using the long-code encodings, and then use the ideas above to verify that the encodings that we get are indeed long-code encodings. We will also have to be able to verify, using these encodings, constraints on the edges of  $\Psi$ .

To be more specific, fix a vertex  $u \in L$  and suppose we want to assign u the label  $\sigma_u \in \Sigma_L$ . Thinking of "[n]" in the discussion so far as  $\Sigma_L$ , we will want to encode that label via its corresponding long code

codeword, that is, by the function  $f_u\colon\{-1,1\}^{\Sigma_L}\to\{-1,1\}$  defined as  $f_u(z)=z_{\sigma_u}$ . Similarly, for  $v\in R$ , we want to encode the fact that v is supposed to get the label  $\sigma_v\in\Sigma_L$  via the long-code codeword corresponding to the function  $f_v\colon\{-1,1\}^{\Sigma_R}\to\{-1,1\}$  defined as  $f_v(x)=x_{\sigma_v}$ . As usual in PCP though — and as we have seen several times by now — while when thinking about the reduction we have the legitimate honest encodings in mind, for the reduction to be sound we must design a tester that indeed makes sure that the encodings are as we expect them to be. Hence, to facilitate the soundness of such reduction we need to:

- 1. Ensure that given functions  $g_u \colon \{-1,1\}^{\Sigma_L} \to \{-1,1\}$ ,  $g_v \colon \{-1,1\}^{\Sigma_L} \to \{-1,1\}$  are indeed valid long-code encodings of some labels for u and v. We will not be able to guarantee such as strong property even in the 99% regime we were only able to guarantee closeness to a legal codeword, and we are now aiming for a low-soundness result. We did see some result in the course in this regime namely the plane versus line test and here we expect to get a similar-in-spirit list decoding type statement, saying that we can associate  $g_u$  and  $g_v$  with a short list of possible labels.
- 2. Check the constraint between u and v using the encodings  $g_u$  and  $g_v$ .

Addressing each one of these issues separately is not too difficult using the ideas we've seen so far. Indeed, for the first item we can run the linearity+noise tester on each one of  $g_u$  and  $g_v$  separately. The second issue is also not very difficult to handle, and in a sense we have seen something along these lines happening when we applied the quadratic Hadamard code and used it to check quadratic equations in the encoded vector. Still, the details in the case of the long-code are somewhat different, and we discuss them next.

Verifying the constraints. The second item requires a bit more thought; recall that the constraint between u and v is a projection constraint, meaning that it is defined by a map  $\phi_{u,v} \colon \Sigma_L \to \Sigma_R$ . Thus, given a point  $x \in \{-1,1\}^{\Sigma_R}$ , we can define the pull-back point  $y = \phi_{u,v}^{-1}(x)$  defined by  $y_i = x_{\phi_{u,v}(i)}$  for each  $i \in \Sigma_L$ . In words, for each label  $\sigma \in \Sigma_R$ , in y all coordinates corresponding to the pre-images of  $\sigma$  under  $\phi_{u,v}$  have the value  $x_\sigma$ . We note that if  $f_u$  and  $f_v$  are legitimate long code encodings of labels  $\sigma_u$  and  $\sigma_v$ , then

$$f_u(y) = y_{\sigma_u} = x_{\phi_{u,v}(\sigma_u)}, \qquad f_v(x) = x_{\sigma_v},$$

so if  $(\sigma_u, \sigma_v)$  satisfy the constraint on e = (u, v), that is, if  $\phi_{u,v}(\sigma_u) = \sigma_v$ , then  $f_u(y) = f_v(x)$  for every choice of x. If, on the other hand,  $(\sigma_u, \sigma_v)$  do not satisfy the constraint on e = (u, v), then choosing x uniformly, the values of  $x_{\phi_{u,v}(\sigma_u)}$  and  $x_{\sigma_v}$  are independent, and hence are equal with probability 1/2.

It follows that to address the second item, we may hope to test  $g_u$  and  $g_v$  by taking  $x \in \{-1,1\}^{\Sigma_R}$  uniformly, setting  $y = \phi_{u,v}^{-1}(x)$  and checking that  $g_u(y) = g_v(x)$ . This almost works; the vigilant reader may notice that the issue is that while the distribution of x is uniform, the distribution of y is not. In fact, the number of y's that are possible to get in this way is negligible. Therefore, since we expect  $g_u$  only to be correlated with a long-code codeword, it may well be the case there will be errors on all of these points y, making this test meaningless.

Fortunately, this is an issue we have already encountered and we know how to solve. We can use random self-correction: we will take  $x \in \{-1,1\}^{\Sigma_R}$  uniformly,  $y = \phi_{u,v}^{-1}(x)$  and  $z \in \{-1,1\}^{\Sigma_L}$  uniformly and then test that  $g_u(zy)g_u(z) = g_v(x)$ . The idea is that if  $g_u$  is a long-code codeword, then  $g_u(zy)g_u(z) = g_u(y)$  hence the test remains the same for legitimate encodings. For the soundness now, each one of the points z and zy is distributed uniformly in  $\{-1,1\}^{\Sigma_L}$ , so a malicious adversary cannot corrupt all of these locations together.

# 3.2 Combining the Tests into a Single Test

Everything we said so far makes sense, but there is one significant issue that we have to deal with. The tester above check that an AND of 3 linear equations, which is not a linear equation. We could use such testers to prove hardness results for soundness close to 1, but since we are shooting for soundness which is close to 1/2, this is not good enough.

Fortunately, there is a magical way of combining all of the above testers. Namely, we can design a test that checks a single linear equation which incorporates together the linearity+noise tests for both  $g_u$  and  $g_v$ , as well as the constraint verification test. Here it is:

- 1. Sample  $x \in \{-1,1\}^{\Sigma_R}$  uniformly and set  $y = \phi_{u,v}^{-1}(x)$ .
- 2. Sample  $z \in \{-1,1\}^{\Sigma_L}$  uniformly and  $a \in \{-1,1\}^{\Sigma_L}$  according to the  $\varepsilon$ -biased measure. Namely, for each  $i \in \Sigma_L$  independently, set  $a_i = 1$  with probability  $1 \varepsilon$ , and  $a_i = -1$  otherwise.
- 3. Test that  $g_u(zya)g_u(z) = g_v(x)$ .

We analyze the test in the following theorem, and to state it we need to introduce some notation. For a character  $\alpha \in \mathbb{F}_2^{\Sigma_L}$ , we define  $\beta = \pi_{u,v}^{\mathsf{odd}}(\alpha) \in \mathbb{F}_2^{\Sigma_R}$  as the vector  $\beta$  in which  $\beta_j = 1$  if and only if the number of preimages i of j under  $\phi_{u,v}$  such that  $\alpha_i = 1$  is odd. In other words,  $\beta_j = \sum_{i:\phi_{u,v}(i)=j} \alpha_i$ .

**Theorem 3.1.** Suppose that  $g_u: \{-1,1\}^{\Sigma_L} \to \{-1,1\}$  and  $g_v: \{-1,1\}^{\Sigma_R} \to \{-1,1\}$  are functions such that  $\Pr_{x,y,z,a} [g_u(zya)g_u(z) = g_v(x)] \geqslant \frac{1}{2} + \delta$ . Then

$$\sum_{|\alpha| \leqslant \frac{\ln(1/\delta)}{\varepsilon}} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 \geqslant \delta^2.$$

*Proof.* From the premise of Theorem 3.1, we have that

$$\mathbb{E}_{x,y,z,a} \left[ g_u(zya) g_u(z) g_v(x) \right] \geqslant 2\delta,$$

and we next use Fourier analysis to analyze the left hand side. We have

$$\mathbb{E}_{x,y,z,a} \left[ g_u(zya) g_u(z) g_v(x) \right] = \mathbb{E}_{x,y,z,a} \left[ \sum_{\alpha \in \mathbb{F}_2^{\Sigma_L}} \widehat{g_u}(\alpha) \chi_{\alpha}(zya) \sum_{\gamma \in \mathbb{F}_2^{\Sigma_L}} \widehat{g_u}(\gamma) \chi_{\gamma}(z) \sum_{\beta \in \mathbb{F}_2^{\Sigma_R}} \widehat{g_v}(\beta) \chi_{\beta}(x) \right] \\
= \sum_{\substack{\alpha,\gamma \in \mathbb{F}_2^{\Sigma_L} \\ \beta \in \mathbb{F}_2^{\Sigma_R}}} \widehat{g_u}(\alpha) \widehat{g_u}(\gamma) \widehat{g_v}(\beta) \mathbb{E}_{x,y,z,a} \left[ \chi_{\alpha}(zya) \chi_{\gamma}(z) \chi_{\beta}(x) \right],$$

and we analyze the inner expectation. By the multiplicativity of characters, we get that

$$\mathbb{E}_{x,y,z,a} \left[ \chi_{\alpha}(zya) \chi_{\gamma}(z) \chi_{\beta}(x) \right] = \mathbb{E}_{a} \left[ \chi_{\alpha}(a) \right] \mathbb{E}_{z} \left[ \chi_{\alpha \oplus \gamma}(z) \right] \mathbb{E}_{x} \left[ \chi_{\beta}(x) \chi_{\alpha}(\phi_{u,v}^{-1}(x)) \right].$$

The first expectation is equal to  $(1-2\varepsilon)^{|\alpha|}$ , the second expectation is non-zero if and only if  $\alpha=\gamma$ . As for the third expectation, we note that

$$\chi_{\alpha}(\phi_{u,v}^{-1}(x)) = \prod_{i:\alpha_i=1} \phi_{u,v}^{-1}(x)_i = \prod_{i:\alpha_i=1} x_{\phi_{u,v}(i)} = \chi_{\phi_{u,v}^{\mathsf{odd}}(\alpha)}(x),$$

so the last expectation is equal to  $\mathbb{E}_x\left[\chi_{\beta\oplus\phi_{u,v}^{\mathrm{odd}}(\alpha)}(x)\right]$ , hence it is non-zero if and only if  $\beta=\phi_{u,v}^{\mathrm{odd}}(\alpha)$ . Thus, we get that

$$2\delta \leqslant \underset{x,y,z,a}{\mathbb{E}} \left[ g_u(zya)g_u(z)g_v(x) \right] = \sum_{\alpha \in \mathbb{F}_2^{\Sigma_L}} (1 - 2\varepsilon)^{|\alpha|} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha)).$$

In the previous argument, at this stage we simply pulled out one of the Fourier coefficients outside and used Parseval's inequality to bound, but this time a bit more care is needed. Taking square and using Cauchy-Schwarz, we get that

$$\begin{split} (2\delta)^2 &\leqslant \left(\sum_{\alpha \in \mathbb{F}_2^{\Sigma_L}} \widehat{g_u}(\alpha) \cdot (1 - 2\varepsilon)^{|\alpha|} \widehat{g_u}(\alpha) \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))\right)^2 \\ &\leqslant \sum_{\alpha \in \mathbb{F}_2^{\Sigma_L}} \widehat{g_u}(\alpha)^2 \cdot \sum_{\alpha \in \mathbb{F}_2^{\Sigma_L}} (1 - 2\varepsilon)^{2|\alpha|} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 \\ &= \sum_{\alpha \in \mathbb{F}_2^{\Sigma_L}} (1 - 2\varepsilon)^{2|\alpha|} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2. \end{split}$$

Note that the contribution from  $\alpha$  such that  $|\alpha| \ge \ln(1/\delta)/\varepsilon$  is at most

$$(1-2\varepsilon)^{\frac{2\ln(1/\delta)}{\varepsilon}}\sum_{\alpha\in\mathbb{F}_2^{\Sigma_L}}\widehat{g_u}(\alpha)^2\widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2\leqslant e^{-4\ln(1/\delta)}=\delta^4,$$

so we conclude that

$$\sum_{|\alpha| \leqslant \frac{\ln(1/\delta)}{\varepsilon}} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 \geqslant \sum_{|\alpha| \leqslant \frac{\ln(1/\delta)}{\varepsilon}} (1 - 2\varepsilon)^{2|\alpha|} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 \geqslant \delta^2.$$

#### 3.3 What Does Theorem 3.1 Even Mean?

Ideally, instead of Theorem 3.1 we would have liked to say that there is an  $\alpha$  with small cardinality such that the product  $|\widehat{g_u}(\alpha)|$   $|\widehat{g_v}(\phi_{u,v}^{\sf odd}(\alpha))|$  is significant. This means that each one of the Fourier coefficients  $|\widehat{g_u}(\alpha)|$  and  $|\widehat{g_v}(\phi_{u,v}^{\sf odd}(\alpha))|$  is significant. We encourage the reader to indeed think of Theorem 3.1 for now in this way, and next explain how one may go about using such statement.

Note that if both  $\alpha$  and  $\phi_{u,v}^{\sf odd}(\alpha)$  are not the all 0 vectors, then the supports of  $\alpha$  and  $\phi_{u,v}^{\sf odd}(\alpha)$  contain pairs of labels  $\sigma_u$  and  $\sigma_v$  that satisfy the constraint  $\phi_{u,v}$ . Indeed, to see that take any  $\sigma_v \in \mathsf{supp}(\phi_{u,v}^{\sf odd}(\alpha))$  and any pre-image of it  $\sigma_u$  from the support of  $\alpha$  (there exists such one by the definition of  $\phi_{u,v}^{\sf odd}$ ). Thus, looking at the Fourier coefficients of  $g_u$  gives us potential way of choosing labels for u: look at all of the  $\alpha$ 's of small cardinality such that  $|\widehat{g_u}(\alpha)|$  is significant, choose one of them, and choose the label  $\sigma_u$  of u to be random from the support of  $\alpha$ . This is indeed going to be the idea, however the execution will be a bit different so as to work with the conclusion we get from Theorem 3.1.

There is one issue though: what if the  $\alpha$  that we chose is  $\vec{0}$ ? In that case, we would not be able to get any label out of it. We will ensure that this never happens by forcing the Fourier coefficients of our functions  $g_u$  and  $g_v$  corresponding to  $\vec{0}$  to always be 0. Note that

$$\widehat{g_u}(\vec{0}) = \mathop{\mathbb{E}}_{z} [g_u(z)],$$

so we will want to force  $g_u$  has expectation 0. We will do that by forcing  $g_u$  to be an *odd function*, meaning that g(-z) = -g(z). We note that dictatorships (which are legitimate assignments) are odd functions, so this will not hurt our completeness. To achieve this, we will use a technique called *folding*.

# 4 NP-hardness of 3Lin: the Proof of Theorem 1.1

In this section, we combine the tools we developed over the last few lectures to prove Theorem 1.1. We do so by reducing from the PCP theorem proved in previous lectures, which we restate below for convenience.

**Theorem 4.1.** For all  $\eta > 0$ , there is  $k \in \mathbb{N}$  such that the problem gap-Label-Cover $[1, \eta]$  is NP-hard on instances with alphabet size at most k and bi-regular constraint graphs.

In the next section, we give a formal description of the reduction from label cover to 3Lin. Following that in subsequent sections, we analyze the completeness and the soundness of the reduction. For convenience, we will reduce the label cover problem to weighted version of the 3Lin problem, in which each equation is assigned a weight, and instead of counting the fraction of equations that are satisfied, we count the total weight of the equations that are satisfied.<sup>3</sup>

#### 4.1 The Reduction

Given a label cover instance  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \Phi = (\phi_e)_{e \in E})$ , we construct a weighted 3Lin instance (X, E, w) as follows.

The variables of the system. For every vertex  $u \in L$  and a location in its long-code  $z \in \{-1,1\}^{\Sigma_L}$  we create a variable  $g_u(z)$ . For every vertex  $v \in R$  and a location in its long-code  $x \in \{-1,1\}^{\Sigma_R}$ , we create a variable  $g_v(x)$ .

**The equations of the system.** The equations and the weights of them are defined according to the follows randomized process:

- 1. Choose an edge  $(u, v) \in E$  uniformly.
- 2. Take  $x \in \{-1,1\}^{\Sigma_R}$  uniformly and  $z \in \{-1,1\}^{\Sigma_R}$  uniformly. Let  $y = \phi_{u,v}^{-1}(x)$ .
- 3. Take  $a \in \{-1,1\}^{\Sigma_R}$  according to the  $\varepsilon$ -biased distribution, that is,  $a_i = 1$  with probability  $1 \varepsilon$  and otherwise  $a_i = -1$ .
- 4. Create the equation  $g_u(ayz)g_u(z)g_v(x) = 1$ .

Folding the variables. Recall that for each u, viewing the assignment to the variables  $g_u(z)$  as a function over z, we wanted to ensure that  $g_u$  is an odd function. We can do this by having a variables only for z such that  $z_1 = 1$ . Thus, in each equation in which a variable  $g_u(z)$  appeared wherein  $z_1 = -1$ , we can replace it by  $-g_u(-z)$ . Thus, the number of variables in our system is in fact smaller and an assignment to them only specifies the values of the function  $g_u$  on half of the points in  $\{-1,1\}^{\Sigma_L}$ . There is a unique way though to

<sup>&</sup>lt;sup>3</sup>As in the case of the Set-cover problem, there are standard techniques that can be used to convert this result into a NP-hardness result for unweighted instances.

complete these values to an odd function, and this is the function that we will have in mind as specified by an assignment of values to the constructed system of linear equations.

This completes the description of the reduction, and we next analyze it.

## 4.2 The Completeness of the Reduction

**Lemma 4.2.** If  $\Psi$  is satisfiable, then there is an assignment to (X, E, w) that satisfies at least  $1 - \varepsilon$  fraction of the equations.

*Proof.* Suppose that  $\Psi$  is satisfiable, and let  $A_L$  and  $A_R$  be satisfying assignments. We define an assignment to the variables of the equations by giving to  $g_u(z)$  the value  $z_{A_L(u)}$ , and giving to  $g_v(x)$  the value  $x_{A_R(u)}$ . A randomly chosen equation from the system takes the form  $g_u(ayz)g_u(z)g_v(x)=1$  for  $(u,v)\in E$  chosen uniformly and x,y,z,a as above, which using our chosen assignment this equation amounts to

$$(ayz)_{A_L(u)} z_{A_L(u)} x_{A_R(v)} = 1.$$

Note that the left hand side is equal to

$$a_{A_L(u)}y_{A_L(u)}z_{A_L(u)}z_{A_L(u)}x_{A_R(v)} = a_{A_L(u)}y_{A_L(u)}x_{A_R(v)} = a_{A_L(u)}x_{\phi_{u,v}(A_L(u))}x_{A_R(v)} = a_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L(u)}x_{A_L$$

where in the last transition we used the fact that  $A_L$  and  $A_R$  satisfy all constraints, and in particular the constraint on e=(u,v), so  $\phi_{u,v}(A_L(u))=A_R(v)$ . Thus, as the probability that  $a_{A_L(u)}=1$  is  $1-\varepsilon$ , we get that our assignment satisfies  $1-\varepsilon$  fraction of the equations.

#### 4.3 The Soundness of the Reduction

Fix  $\varepsilon > 0$ . We show that for every  $\delta > 0$ , for sufficiently small  $\eta > 0$ , if at least  $\frac{1}{2} + \delta$  of the equations can be satisfied, then we can find an assignment to  $\Psi$  satisfying at least  $\delta' > 0$  fraction of the constraints. Formally:

**Lemma 4.3.** For all  $\varepsilon, \delta > 0$  there is  $\delta' > 0$  such that if there is an assignment to (X, E, w) satisfying at least  $1/2 + \delta$  of the equations, then  $\mathsf{val}(\Psi) \geqslant \delta'$ .

Thus, taking  $\eta$  in the PCP to be smaller than  $\delta$ ', we conclude that if  $val(\Psi) < \eta$ , then at most  $\frac{1}{2} + \delta$  of the equations in the system can be satisfied, which gives the soundness of the construction.

The rest of this section is devoted to the proof of Lemma 4.3. For an edge  $e = (u, v) \in E$ , denote

$$\delta_{u,v} = \mathop{\mathbb{E}}_{x.z.a} [g_u(ayz)g_u(z)g_v(x)].$$

Note that the fraction of equations that are satisfied is  $\mathbb{E}_{(u,v)\in E}[(1+\delta_{u,v})/2]$ , so by the assumption we get that  $\mathbb{E}_{(u,v)\in E}[\delta_{u,v}]\geqslant 2\delta$ . Thus, defining

$$E' = \{ e \in E \mid \delta_e \geqslant \delta \},\,$$

and noting that  $\delta_{u,v} \leq 1$  always, we get by an averaging argument that E' contains at least  $\delta$  fraction of the edges in E. We next describe a probabilistic assignment to  $\Psi$ , and show that it satisfies each edge in  $e \in E'$  with significant probability.

## 4.3.1 Defining the Probabilistic Assignment

Next, we describe a probabilistic assignment to the vertices of  $\Psi$  based on the functions  $g_u$  and  $g_v$ .

The assignment to the left vertices. We define the assignment for  $u \in L$  as follows. Looking at the values of the variables  $g_u(z)$  as values of a Boolean function  $g_u$ , we note that by Parseval's equality that  $\sum_{\alpha} \widehat{g_u}(\alpha)^2 = \mathbb{E}_z \left[ g_u(z)^2 \right] = 1$ , so  $\widehat{g_u}(\alpha)^2$  is a distribution over characters. Thus, to choose the label of u, we choose  $\alpha \in \mathbb{F}_2^{\Sigma_L}$  with probability  $\widehat{g_u}(\alpha)^2$ , and then choose  $A_L(u)$  uniformly from the support of  $\alpha$ .

The assignment to the right vertices. We define the assignment for a vertex  $v \in R$  in a similar way. We choose  $\beta \in \mathbb{F}_2^{\Sigma_L}$  with probability  $\widehat{g_v}(\beta)^2$ , and then choose  $A_R(v)$  uniformly from the support of  $\beta$ .

# 4.3.2 Analyzing the Probabilistic Assignments

We next analyze the performance of the probabilistic assignment. Fix  $e = (u, v) \in E'$ , so that we know that  $\mathbb{E}_{x,z,a} [g_u(ayz)g_u(z)g_v(x)] \geqslant \delta$ . Hence, from Theorem 3.1 we get that

$$\sum_{|\alpha| \leqslant \frac{\log(1/\delta)}{\varepsilon}} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 \geqslant \delta^2,$$

and we next relate the left hand side to the probability that the probabilistic assignment satisfies e. Inspecting, the term  $\widehat{g_u}(\alpha)^2\widehat{g_v}(\phi_{u,v}^{\text{odd}}(\alpha))^2$  corresponds to the probability that u chose the character  $\alpha$  and v chose the character  $\beta = \phi_{u,v}^{\text{odd}}(\alpha)$ . Note that by folding, we have ensured that  $\alpha$  nor  $\beta$  can be  $\vec{0}$  (otherwise the probability would be 0), hence there are pairs of labels in the supports of  $\alpha$  and  $\beta$  that satisfy the constraint between u and v. Thus, conditioned on u and v picking the characters  $\alpha$  and  $\beta$ , the probability that they choose a pair of labels that satisfy  $\phi_{u,v}$  is at least  $\frac{1}{|\alpha||\beta|}$ . Hence, the probability that the probabilistic assignment above satisfies e is at least

$$\begin{split} \sum_{\alpha} \frac{1}{|\alpha|} \frac{1}{\phi_{u,v}^{\mathsf{odd}}(\alpha)} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 &\geqslant \sum_{|\alpha| \leqslant \frac{\log(1/\delta)}{\varepsilon}} \frac{1}{|\alpha|^2} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 \\ &\geqslant \frac{\varepsilon^2}{\log(1/\delta)^2} \sum_{|\alpha| \leqslant \frac{\log(1/\delta)}{\varepsilon}} \widehat{g_u}(\alpha)^2 \widehat{g_v}(\phi_{u,v}^{\mathsf{odd}}(\alpha))^2 \\ &\geqslant \frac{\varepsilon^2}{\log(1/\delta)^2} \delta^2. \end{split}$$

Therefore, letting  $W_e$  be the event that the probabilistic assignment satisfies the edge e, we have that  $\sum_{e \in E} W_e$  represents the number of constraints in  $\Psi$  that are satisfied, and

$$\mathbb{E}\left[\sum_{e \in E} W_e\right] \geqslant \sum_{e \in E'} \mathbb{E}\left[W_e\right] \geqslant \sum_{e \in E'} \frac{\varepsilon^2}{\log(1/\delta)^2} \delta^2 = \frac{\varepsilon^2}{\log(1/\delta)^2} \delta^2 \ E' \geqslant \frac{\varepsilon^2}{\log(1/\delta)^2} \delta^3 |E|.$$

In particular, there is an assignment to  $\Psi$  satisfying at least  $\delta' = \frac{\varepsilon^2}{\log(1/\delta)^2} \delta^3$  of the constraints.

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lecture 21

#### Dor Minzer

Today we present stronger forms of the PCP theorem that are conjectured to hold but not known. In the upcoming lectures, we will discuss some of their implications and recent related results.

## 1 On the Structure of the Constraints in Label Cover

## 1.1 The PCP + Parallel Repetition + Fourier framework

Recall that in the label-cover problem, an instance  $\Psi$  consists of a graph  $G=(L\cup R,E)$ , alphabets  $\Sigma_L$  and  $\Sigma_R$  and a collection of projection constraints on the edges  $\Phi=\{\Phi_e\}_{e\in E}$ . That is, for each  $e\in E$  the constraint  $\Phi_e$  are defined by a projection map  $\phi_e\colon \Sigma_L\to \Sigma_R$  as

$$\Phi_e = \{ (\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma_L \}.$$

In the first half of the course, we saw that gap-Label-cover $[1,1-\varepsilon]$  is NP-hard for some absolute constant  $\varepsilon>0$  on alphabets  $|\Sigma_L|=k$ ,  $|\Sigma_R|=2$  where k is an absolute constant. We then used the parallel repetition to improve upon the soundness of the PCP, and in the last lecture we saw how one may use Fourier analysis to get optimal hardness of approximation results for some problems. This framework, that is, the combination of the PCP Theorem, the Parallel Repetition Theorem and Fourier analysis has been very fruitful in the decade or so following the proof of the PCP Theorem, but for some reason there were some (in fact, many) problems for which this approach did not seem to give optimal hardness of approximation results.

To see this, we dissect the hardness result we saw for 3Lin and explain one of the challenges there that we fortunately managed to overcome. As a result of parallel repetition, the alphabet of the sides L and R grows exponentially to  $k^\ell$  and  $2^\ell$  where  $\ell$  is the number of repetition. Thus, the alphabet of the left side is much larger than that of the right side, hence there are many more points in  $\{-1,1\}^{\Sigma_L}$  compared to  $\{-1,1\}^{\Sigma_R}$ . When proving the hardness result for 3Lin, this point presented some difficulties; more precisely, when we took  $x \in \{-1,1\}^{\Sigma_R}$  uniformly and then looked at the pull-back point  $y = \phi_{u,v}^{-1}(x) \in \{-1,1\}^{\Sigma_L}$ , the point y is very much not random looking and we cannot directly look at the value of the long-code of y there (as it is very cheap to corrupt all of these points). Fortunately, in the case of 3Lin we were able to overcome this issue by using local correction.

There are cases, however, where we cannot use local correction. Suppose that we were trying to prove a hardness result for 2Lin instead of 3Lin (which is the same problem except that in each equation we have two variables), or the very related problem of Max-Cut. In that case we cannot afford to perform local correction: if we wish to perform local correction, we are already investing 2 in that, so we cannot query anything else to compare this value against. This barrier, and other manifestations of it, present themselves in numerous problems wherein one has a candidate construction for a dictatorship test but does not know how to use it for a NP-hardness reduction.

## 1.2 Circumventing the Local Correction Barrier

Thus, to make progress on problems in which this barrier exists, researchers had to come up with rather adhoc solutions. This includes inspecting other parameters of PCP that can be used, on top of the parameters we've discussed in this course, for the purpose of a specific problem. This also includes more ingenious ways of combining the above ingredients to circumvent this barrier (smooth PCPs, randomized noise rates and so on), but even these ideas only led to progress on a limited class of problems. Some notable problems for which these techniques did not work very well are the Vertex Cover problem, the Max-Cut problem and the 2SAT problem.

This situation naturally sparks the question of whether there are yet other, stronger forms of the PCP theorem that would allow one to circumvent these issues altogether. And while we do not know the answer to that, in 2002 a conjecture regarding the existence of such PCP theorem has been made, which we discuss in the next section.

## 2 The d-to-1 and the Unique-Games Conjectures

### 2.1 The Statements of the Conjectures

An instance of the d-to-1 Games problem is special type of instance of the Label-cover problem, wherein each constraint is a d-to-1 constraint. Formally:

**Definition 2.1.** An instance of d-to-1-Games is  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \Phi = \{\Phi_e\}_{e \in E})$ , wherein G is a bi-regular bipartite graph,  $\Sigma_L$  and  $\Sigma_R$  are finite alphabet with  $|\Sigma_L| = d |\Sigma_R|$ , and for each  $e \in E$ , the constraint  $\Phi_e$  is a d-to-1 constraint. By that, we mean that there is a d-to-1 map  $\phi_e \colon \Sigma_L \to \Sigma_R$  such that

$$\Phi_e = \{ (\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma \}.$$

In the context of d-to-1-Games, d should be thought of as a small constant, say d=2. The smaller the d, the better. For the smallest possible d, that is, for d=1, d-to-1-Games take the more well-known name Unique-Games.

**Definition 2.2.** The Unique-Games problem is the d-to-1-Games problem for d = 1.

The d-to-1-Games Conjecture and the Unique-Games Conjecture assert, morally speaking, that the statement of the PCP theorem holds for d-to-1 Games and Unique-Games respectively. More precisely, the d-to-1 Games Conjecture states that

**Conjecture 2.3.** For all  $d \ge 2$  and for all  $\varepsilon > 0$ , there is  $k \in \mathbb{N}$  such that gap-d-to-1-Games  $[1, \varepsilon]$  is NP-hard on instances with alphabet sizes at most k.

For d=1, the situation is a bit more delicate. Given an instance of Unique-Games which is promised to be fully satisfiable, it is possible to efficiently find a satisfying assignment. Indeed, one takes some vertex  $u \in L$ , guess their label  $\sigma_u$  and then use the 1-to-1 constraints to propagate this and get the labels for all other vertices in the graph. In words, fully satisfiable instances of Unique-Games are easy to solve. The statement of the Unique-Games Conjecture states that, except for that, Unique-Games are just as hard as Label-cover instances:

**Conjecture 2.4.** For all  $\varepsilon, \delta > 0$ , there is  $k \in \mathbb{N}$  such that gap-Unique-Games $[1 - \varepsilon, \delta]$  is NP-hard on instances with alphabet sizes at most k.

### 2.2 Proving Via Parallel Repetition?

d-to-1 Games. One may attempt to prove Conjecture 2.3 for some  $d \in \mathbb{N}$  via a strategy similar to the one we've seen in this course. Namely, start off with a basic result saying that gap-d-to-1-Games $[1, 1 - \varepsilon]$  is NP-hard for some  $\varepsilon > 0$  and  $d \in \mathbb{N}$ , and then perform parallel repetition to amplify the gap. And indeed, while the first step works (that is, one can get a basic result of this form), the parallel repetition step does not. Indeed, applying t-fold parallel repetition on a d-to-1-Games instance leads to  $d^t$ -to-1-Games instance, so the parallel repetition operation does not preserve d-to-1-ness.

**Unique-Games.** Ok, but we can still try to prove Conjecture 2.4 for some  $d \in \mathbb{N}$  via this strategy, since parallel repetition does preserve uniqueness. That is, we want to start off with a basic result stating that gap-Unique-Games $[1-\varepsilon,1-\varepsilon']$  is NP-hard for some  $\varepsilon < \varepsilon'$ , and then perform parallel repetition to amplify the gap. If we had an "ideal" parallel repetition theorem which states that  $\operatorname{val}(\Psi^{\otimes t}) = \operatorname{val}(\Psi)^t$  and  $\varepsilon$  was arbitrarily smaller than  $\varepsilon'$  (say,  $\varepsilon' = \varepsilon^{0.99}$ ), then this approach could be in fact made to work. Alas, such "ideal" parallel repetition theorem is not known — in fact it is false. Moreover, the basic PCP result for Unique-Games one wants to amplify, is also not known.

In other words, it is unclear how to go about proving Conjectures 2.3 and 2.4. And indeed, despite being proposed in 2002 until recently there hasn't been much progress towards a proof of these results.

## 2.3 Implications of Conjectures 2.3 and 2.4

In contrast to the lack of progress towards a proof of Conjectures 2.3 and 2.4, there has been much progress in understanding their power and their implications. In the same paper that suggested these conjectures, it was shown that they imply improved inapproximability results for the vertex cover and 2SAT problems that bypassed the best known hardness result that can be achieved by existing PCP techniques.

It took a while longer, but it was later realized that, if true, Conjecture 2.4 in fact implies *tight inap-proximability* results for all constraint satisfaction problems. This result, known as Raghavendra's theorem, is a beautiful culmination of many ideas that were developed in UGC based reduction, among which are connections to Fourier analysis, Gaussian geometry and Semi-definite Programming relaxation.

In this course, we will not prove Raghavendra's theorem or even state it, and instead focus on predecessors of it which got the UGC train started. Namely, we are going to discuss the Max-cut and Vertex-cover problems.

## 3 The Max-cut Problem

Recall that given a graph G=(V,E), a cut in G is a set of vertices  $S\subseteq V$ . Denoting by  $E(S,\bar{S})$  the set of edges that go from S to its complement, the size of the cut defined by S is  $E(S,\bar{S})$ , and the fractional size of the cut defined by S is  $\frac{|E(S,\bar{S})|}{|E|}$ .

In an undergraduate algorithm course, one often sees that the Min-cut problem, which asks, given a graph G, to find the smallest cut in it. This is a well known problem in the class P, and a typical textbook way of showing that is by using LP-duality to establish the Min-cut Max-flow algorithm, and then solving the Max-flow problem by one of the many existing polynomial time algorithms for it. What about the maximization version of the cut problem, though?

In the Max-cut problem, the input is again a graph G=(V,E), and the task is to find a cut of maximum size. This problem is another well-known NP-hard problem, and we will care about the approximation version of it. Here, for  $\alpha \in (0,1)$ , an  $\alpha$ -approximation algorithm for Max-cut is an algorithm that on a graph G outputs a cut whose size is as least  $\alpha \mathsf{MC}(G)$ , where  $\mathsf{MC}(G)$  denotes the size of the maximum cut in G. How well can one approximate Max-cut?

**Theorem 3.1.** There is a polynomial time  $\frac{1}{2}$ -approximation for Max-cut.

*Proof.* Given a graph G=(V,E), we choose a cut  $S\subseteq V$  randomly, by including each  $v\in V$  in S with probability 1/2. Note that for any edge  $e=(u,v)\in E$ , the probability it belong to the cut S is 1/2, so denoting by  $Z_e$  the event that e crosses the cut, we get that the expected size of the cut of S is

$$\mathbb{E}\left[\sum_{e \in E} Z_e\right] = \sum_{e \in E} \mathbb{E}\left[Z_e\right] = \sum_{e \in E} \frac{1}{2} = \frac{|E|}{2}.$$

Hence, in expectation the cut S has size |E|/2, and by standard techniques again one can de-randomize this algorithm.

In light of Theorem 3.1 and previous lectures, one may expect that the next result would state that achieving a better approximation ratio than 1/2 is NP-hard (or maybe UGC-hard since we talked about UGC before). However, here the plot thickens:

**Theorem 3.2.** For  $\alpha_{\text{GW}} \approx 0.878$ , there is a polynomial time  $\alpha_{\text{GW}}$ -approximation for Max-cut.

The rest of this lecture is devoted to the proof of Theorem 3.2. Our approach will be to first phrase the Max-cut problem as an integer program, which by itself is not very useful since integer programming is NP-hard. We will then consider a convex relaxation of this program which is known as the Semi-definite Programming relaxation. The benefit of this is that, unlike integer programs, such convex optimization problems can be solved by polynomial time algorithm. The down-side is, though, that we will get a solution to the relaxed version of the problem, which does not give us a cut in the graph. The final step in our approach will be a rounding phase, wherein we will turn the solution of the relaxed program into a Max-cut by a rounding algorithm.

#### 3.1 The Integer Program Formulation

First, we phrase the Max-cut problem as an integer program. For each vertex  $v \in V$  we create a variable  $x_v$  that is supposed to be assigned a value from  $\{-1,1\}$ . The idea is that  $x_v = 1$  will represent that v is on the left side, and  $x_v = -1$  will represent that v is on the right side. Thus, for  $(u,v) \in E$ ,  $x_ux_v = -1$  if and only if (u,v) crosses the cut, and otherwise  $x_ux_v = 1$ . Therefore, the following program is a formulation of the Max-cut problem over G:

$$\max \qquad \frac{1}{2} \sum_{(u,v) \in E} 1 - x_u x_v$$
 subject to  $x_v \in \{-1,1\} \qquad \forall v \in V.$ 

However, integer programming is NP-hard in general, so this formulation does not get us anywhere. That being said, this formulation does motivate us to look at a higher dimensional, *Semi-definite Program* (SDP in short) formulation of the problem.

### 3.2 The Goemans-Williamson Algorithm for Max-cut

In this section, we show the algorithm that proves Theorem 3.2, which goes by the name the Goemans-Williamson algorithm.

#### 3.2.1 The Semi-definite Programming Relaxation

In the SDP formulation of the problem, we allow each variable  $x_u$  to take a value in the unit ball in  $\mathbb{R}^r$  (where r may be polynomially large in n = |V|).

$$\max \qquad \frac{1}{2} \sum_{(u,v) \in E} 1 - \langle x_u, x_v \rangle$$
 subject to  $\|x_v\|_2 = 1$   $\forall v \in V$ .

This optimization problem now can be solved, at least approximately. We will not discuss convex optimization in this course further, but we remark that the point is that this program is convex: this is really an optimization problem over the cone of PSD matrices, where the matrix in question is  $|V| \times |V|$  matrix of inner products  $J = (\langle x_u, x_v \rangle)_{u,v \in V}$ .

Let  $\{x_v\}_{v\in V}$  be a vector solution to the above program. Amazingly, we can turn this vector-valued solution into pretty good integral-valued solution, that is, a cut in the graph G!

### 3.3 The Rounding Procedure

In this section, we show how to turn the vector-valued solution to the above SDP program relaxation into a decent cut in G. Suppose the optimum size of the cut in our graph G is  $\rho |E|$ , where  $\rho \in [1/2, 1]$ . First, it is clear that the optimum of the SDP program is at least  $\rho |E|$  (why?), so in particular

$$\frac{1}{2} \sum_{(u,v) \in E} 1 - \langle x_u, x_v \rangle \geqslant \rho |E|.$$

We now generate a randomized cut from the vector solution. Take a random vector h from the unit ball in  $\mathbb{R}^m$ , and define

$$L = \{ v \mid \langle x_v, h \rangle \leqslant 0 \}; \qquad R = \{ v \mid \langle x_v, h \rangle > 0 \}.$$

Our goal is to analyze the expected number of edges that crosses the cur (L, R). Fix an edge  $(u, v) \in E$ ; then the probability that (u, v) is cut is  $\theta_{u,v}/\pi$ , where  $\theta_{u,v}$  is the angle between u and v. Thus, by linearity of expectation the expected size of the cut is

$$\sum_{(u,v)\in E} \frac{\theta_{u,v}}{\pi} = \sum_{(u,v)\in E} \frac{\operatorname{Arccos}(\langle x_u,x_v\rangle)}{\pi} \geqslant \sum_{(u,v)\in E} \alpha_{GW} \left(1-\langle x_u,x_v\rangle\right) \geqslant \alpha_{GW}\rho \left|E\right|.$$

Here,  $\alpha_{GW} = \min_{z \in [-1,1]} \frac{\mathsf{Arccos}(z)/\pi}{(1-z)/2}$ . Given this expectation guarantee, one can again use standard tools to design a proper approximation algorithm that achieves this approximation ratio.

## 3.4 The Goemans-Willaimson algorithm for almost bipartite graphs

With a more careful analysis, one can show that if the original size of the cut was very large, say  $\rho = 1 - \varepsilon$  for small  $\varepsilon$ , then the above analysis could be significantly improve.

**Theorem 3.3.** Suppose G = (V, E) has a cut of size  $(1 - \varepsilon) |E|$ . Then the expected size of the cut in the Goemans-Williamson algorithm is at least  $\left(1 - \frac{2}{\pi}(1 + o(1))\sqrt{\varepsilon}\right) |E|$ .

# 3.5 Optimal Algorithms for Max-cut

The algorithmic guarantees given by Theorems 3.2 and 3.3 seem rather bizarre. A-priori, there is no reason to believe that the best approximation ratio achievable for Max-cut is provided by this ad-hoc-ish approach of solving a convex programming relaxation and then rounding it to an integral solution.

It turns out, though, that the algorithm we presented today is the best polynomial time approximation algorithm for Max-cut. At least assuming the Unique-Games Conjecture. In the next lecture, we will present a reduction that proves this last assertion.

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.408 Topics in Theoretical Computer Science Fall 2022 Lectures 22,23

#### Dor Minzer

Today, we will present a reduction from Unique-games to Max-cut which shows that, assuming the Unique-Games Conjecture, the Goemans-Williamson algorithm achieves essentially the best approximation ratio for Max-cut (among polynomial time algorithms). Towards this end we further discuss the long code framework, and the notions of "influences" and "low-degree influences" from analysis of Boolean functions.

# 1 The Long-code Framework, Influence Style

#### 1.1 Motivation

Recall that the hardness result we showed for 3Lin began by constructing a local tester for the long code with the properties that: (1) codewords of the long code pass the test with probability close to 1, and (2) any word that passes the test with probability significantly more than 1/2 can be associated with a few (constantly many) long code codewords.

To be more specific, we managed to design a test that if a function  $f: \{-1,1\}^n \to \{-1,1\}$  passes with probability  $1/2 + \delta$  then there is a Fourier character  $\alpha \in \mathbb{F}_2^2$  of size  $O_{\varepsilon,\delta}(1)$  such that  $\left| \widehat{f}(\alpha) \right| \geqslant 2\delta$ . Thus, we thought of the support of  $\alpha$  as the set of potential dictators (with which we can associate longcode codewords) that f is associated with. This is a rather ad-hoc way of arriving at dictator — is there a more natural and direct notion that captures our association to long code codewords?

It turns out that the answer is yes, and in fact this more general notion is critical to prove many other hardness of approximation results. In particular, it is essential for the reduction we will see today from Unique-games to Max-cut. To present, we will first consider the Max-cut problem and design a local tester for the long code using the Max-cut predicate. Such local testers for the long code often go by the name *dictatorship tests*.

#### 1.2 A Dictatorship Tester for Max-cut

Recall that in the Max-cut problem the input is a graph G=(V,E), and we wish to partition the vertices into two sides so that the number of edges crossing from one side to the other is maximized. Alternatively, we may view this problem as a constraint satisfaction problem, as follows. With each vertex  $v \in V$  we associate a variable  $x_v$  which is supposed to be label by either 1 or -1, and with each equation  $e=(u,v)\in E$  we associate the equation  $x_u\neq x_v$ . The goal now is to label the variables by labels from  $\{-1,1\}$  and satisfy as many of the equations as possible. Thus, we see that the predicate corresponding to Max-cut is  $P:\{-1,1\}^2\to\{0,1\}$  defined as  $P(a,b)=1_{a\neq b}$ .

We now wish to design a dictatorship tester for the long-code using this predicate. In other words, we way to construct a distribution  $\mu$  over  $\{-1,1\}^n \times \{-1,1\}^n$  such that:

- 1. Long code codewords pass the test with probability close to 1: if  $f: \{-1,1\}^n \to \{-1,1\}$  is a dictator, that is,  $f(x) = x_i$  for some  $i \in [n]$ , then the probability that P(f(x), f(y)) = 1 for  $(x,y) \sim \mu$  is large c.
- 2. Far-from-long code codewords pass the test with noticeably smaller probability: if  $f: \{-1,1\}^n \to \{-1,1\}$  doesn't look like a dictator at all, then the probability that P(f(x),f(y))=1 for  $(x,y)\sim \mu$  is at most s, where s is much smaller than c.

Indeed, constructing such dictatorship tests is often a key step in proving a hardness of approximation results (not only for Max-cut), but in general converting such tests into a proper hardness of approximation results is a non-trivial tasks by itself.

In this language, the power of the Unique-Games Conjecture is that it allows one to bypass this last hurdle, and indeed if one is willing to assume this conjecture there is almost an immediate translation between dictatorship tests and hardness of approximation results. We will not show this connection in full generality and instead focus on the case of Max-cut.

#### 1.3 Influences

To make the question more precise we must clarify what we mean by "doesn't look like a dictator at all". For this we define the notion of influences of coordinates on a function f that capture how much the value of f depends on the ith coordinate of its input.

**Definition 1.1.** Let  $f: \{-1,1\}^n \to \{-1,1\}$  be a function, and  $i \in [n]$  be a coordinate. The influence of i is defined as

$$I_i[f] = \Pr_{x \sim \{-1,1\}^n} [f(x) \neq f(xe_i)],$$

where  $xe_i$  is the point x with the ith coordinate flipped.

Note that if f is a dictatorship, say  $f(x) = x_1$ , then  $I_1[f] = 1$  and  $I_i[f] = 0$  for any other i. Thus, we can think of the influence of a coordinate i as measuring "how much f is alike the dictator i". Though this is not completely precise, this turns out to be a good and useful notion to consider for the purposes of PCPs. Let us consider a few examples:

- 1. Parity functions. If  $f(x) = x_1 x_2 \cdots x_d$ , then the influence of each  $i \in [d]$  is 1, and the influence of any other variable is 0.
- 2. The Majority function. Suppose n is odd, and define f(x) = 1 if  $\sum_{i=1}^{n} x_i > 0$  and f(x) = -1 otherwise. What is  $I_i[f]$ ? Well, by symmetry it is clear that all of the influences of f are equal, so we fix i = 1. Note that sampling  $x \sim \{-1, 1\}^n$ , the probability that  $f(x) \neq f(xe_1)$  is the probability that  $\sum_{i=1}^{n} x_i$  changes its sign when we change  $x_1$ . Thus, it must be the case that  $\sum_{i=2}^{n} x_i = 0$ , which happens with probability

$$\frac{\binom{n-1}{(n-1)/2}}{2^{n-1}} \approx \sqrt{\frac{2}{\pi}} \frac{1}{\sqrt{n}}$$

**Definition 1.2.** Let  $f: \{-1,1\}^n \to \{-1,1\}$  be a function,  $i \in [n]$  be a coordinate and  $\tau > 0$ . We say f has  $\tau$ -small influences if for all  $i \in [n]$ ,  $I_i[f] \leq \tau$ .

# 1.4 Constructing the Dictatorship Tester

With the notion of influence in mind, we can now re-phrase the question above more precisely. We wish to construct a distribution  $\mu$  over  $\{-1,1\}^n \times \{-1,1\}^n$  such that:

1. Long code codewords pass the test with probability close to 1: if  $f: \{-1,1\}^n \to \{-1,1\}$  is a dictatorship

$$\Pr_{(x,y)\sim\mu} \left[ f(x) \neq f(y) \right] \geqslant c.$$

2. Far-from-long code codewords pass the test with noticeably smaller probability: if  $f: \{-1,1\}^n \to \{-1,1\}$  has  $\tau$ -small influences, then

$$\Pr_{(x,y)\sim\mu} \left[ f(x) \neq f(y) \right] \leqslant s + o(1),$$

where the o(1) goes to 0 as  $\tau$  goes to 0.

3. c and s are far apart.

A natural idea is to take the distribution  $\mu$  to be the uniform distribution over (x,y) such that y=-x, and for this distribution it is clear that one gets that c=1. However, this distribution fails the second property, as any odd function pases this test with probability 1; for example, majority. How can we change this distribution so as to penalize majority (yet keep the performance of dictatorship functions relatively untouched)?

Recall that in the 3-Lin lecture, we wanted to distinguish between low-weight Hadamard codewords and high-weight Hadamard codewords, and for that we applied the noise test. We noticed that long-code codewords only get slightly penalized, whereas high weight Hadamard codewords get heavily penalized. Why shouldn't we try such idea?

More precisely, consider the distribution  $\mu$  over (x,y) where we pick  $x \sim \{-1,1\}^n$  uniformly, set z = -x and then sample y to be a noisy version of z. That is, for each  $i \in [n]$  independently set  $y_i = z_i$  with probability  $1 - \varepsilon$ , and otherwise sample  $y_i$  uniformly from  $\{-1,1\}$ . In other words, we flip all of the coordinates of x (so that checking "equality" turns into checking "inequality"), and then apply noise.

What can we say about this test, then? If f is a dictatorship, say  $f(x) = x_1$ , then  $f(x) = x_1$  and  $f(y) = y_1$ , so the test fails only if we resampled the first coordinate and got a different value than the original one, which happens with probability  $\varepsilon \cdot \frac{1}{2}$ . Hence, we get that  $c = 1 - \varepsilon/2$ .

What about functions f that have  $\tau$ -small influences? Intuitively, such functions must depend on many coordinates, so we expect that a slight noise will have several "chances" to change the value of f at a point x. Namely we expect that  $f(x) \neq f(y)$  with probability noticeably bigger than  $\varepsilon$ . Indeed, this is correct and is the content of the "Majority is Stablest" theorem:

**Theorem 1.3** (Majority is Stablest). For all  $\varepsilon > 0$  and  $\eta > 0$ , there is  $\tau > 0$  such that the following holds. Suppose that  $f: \{-1,1\}^n \to \{-1,1\}$  is a function such that  $\mathbb{E}[f] = 0$  and  $\max_i I_i[f] \leqslant \tau$ . Then

$$\Pr_{(x,y)\sim \mu}[f(x)\neq f(y)]\leqslant 1-\frac{1}{\pi}\mathrm{Arccos}(1-\varepsilon)+\eta.$$

The proof of this result goes beyond the scope of this course, and we will use it in a black-box way. Recalling that  $\operatorname{Arccos}(1-\varepsilon) = \sqrt{2\varepsilon} + O(\varepsilon)$ , we get that  $s = 1 - \frac{\sqrt{2}}{\pi}\sqrt{\varepsilon} + O(\varepsilon)$ , hence we get a gap between c and s in the potential dictatorship test above.

We summarize the properties of the dictatorship test  $\mu$ :

1. If  $f: \{-1,1\}^n \to \{-1,1\}$  is a dictatorship, then

$$\Pr_{(x,y)\sim\mu}\left[f(x)\neq f(y)\right]\geqslant 1-\varepsilon/2$$

for large c.

2. If  $f: \{-1,1\}^n \to \{-1,1\}$  has  $\tau$ -small influences, for sufficiently small  $\tau \leqslant \tau_0(\varepsilon,\eta)$ , then

$$\Pr_{(x,y)\sim \mu}[f(x)\neq f(y)]\leqslant \frac{1}{\pi}\mathrm{Arccos}(\varepsilon-1)+\eta.$$

We will convert this dictatorship test into a hardness of approximation result for Max-cut, and get that approximating Max-cut within any factor larger than  $\alpha = \max_{\varepsilon>0} \frac{1-\operatorname{Arccos}(1-\varepsilon)/\pi}{1-\varepsilon/2}$  is NP-hard (assuming the Unique Games Conjecture). Note that  $\alpha$  is the approximation ratio that the Goemans-Williamson algorithm achieves, hence we would get that the Goemans-Williamson approximation algorithm for Max-cut is tight!

## 1.5 A Majority is Stablest Result for Bounded Functions

To use the above ideas in a reduction and to carry out the analysis, it will be necessary for us to consider an arithmetic expression that measure the size of the cut defined by f, that is,  $\Pr_{(x,y)\sim\mu}[f(x)\neq f(y)]$ . We will also need to generalize this quantity as well as the Majority is Stablest theorem for functions that get values in [-1,1] (as opposed to only  $\{-1,1\}$ ).

Note that for  $\{-1,1\}$ -valued functions, we have that f(x)f(y)=-1 if  $f(x)\neq f(y)$  and otherwise it is 1, hence we can write that

$$\Pr_{(x,y)\sim\mu}[f(x) \neq f(y)] = \frac{1}{2} \mathop{\mathbb{E}}_{(x,y)\sim\mu}[1 - f(x)f(y)].$$

The expression on the right hand side makes sense for general functions, and we will use it as our generalization.

**Definition 1.4.** Let  $\rho \in [0,1]$ , and let  $x \in \{-1,1\}^n$ . The distribution over  $\rho$ -correlated points with x, denoted by  $T_{\rho}x$ , is defined by the following randomized process: for each  $i \in [n]$  independently, set  $y_i = x_i$  with probability  $\rho$ , and otherwise sample  $y_i$  uniformly from  $\{-1,1\}$ .

For  $\rho \in [-1,0]$  and  $x \in \{-1,1\}^n$ , the distribution over  $\rho$ -correlated points with x, denoted by  $T_{\rho}x$ , is  $-T_{-\rho}x$ . In other words, we sample  $y \sim T_{-\rho}x$  and output -y.

With this terminology in mind, we define the stability of f:

**Definition 1.5.** Let  $\rho \in [-1,1]$  and  $f: \{-1,1\}^n \to [-1,1]$  be a function. We define

$$\mathsf{Stab}_{\rho}(f) = \underset{\substack{x \sim \{-1,1\}^n \\ y \sim \mathsf{T}_{\sigma}x}}{\mathbb{E}} [f(x)f(y)].$$

Thus, for Boolean-valued f we have that  $\Pr_{(x,y)\sim\mu}[f(x)\neq f(y)]=\frac{1}{2}-\frac{1}{2}\mathsf{Stab}_{-1+\varepsilon}(f)$ . With the notion of stability in mind we can state the majority is stablest theorem for bounded functions, but for technical reasons we shall need to replace the notion of influences with the notion of low-degree influences.

#### 1.5.1 Fourier Coefficients, Influences and Low-degree Influences

Recall the discrete Fourier transform of  $f: \{-1,1\}^n \to \{-1,1\}$  is given as

$$f(x) = \sum_{\alpha \in \mathbb{F}_2^n} \widehat{f}(\alpha) \chi_{\alpha}(x).$$

The influences of a function f can be related to its Fourier transform as follows:

**Claim 1.6.** For  $f: \{-1,1\}^n \to \{-1,1\}$  and  $i \in [n]$ , we have

$$I_i[f] = \sum_{\alpha:\alpha_i=1} \widehat{f}(\alpha)^2.$$

*Proof.* Note that  $f(x) \neq f(xe_i)$  if  $\left(\frac{f(x) - f(xe_i)}{2}\right)^2 = 1$ , and otherwise  $\left(\frac{f(x) - f(xe_i)}{2}\right)^2 = 0$ . Hence

$$I_i[f] = \mathbb{E}_x \left[ \left( \frac{f(x) - f(xe_i)}{2} \right)^2 \right].$$

Consider the function  $g(x) = \frac{f(x) - f(xe_i)}{2}$ ; we will use Parseval's equality to evaluate the last expectation, and for that we compute the Fourier coefficients of g. Expanding the Fourier expansion of f, we have that

$$g(x) = \frac{1}{2} \left( \sum_{\alpha} \widehat{f}(\alpha) \chi_{\alpha}(x) - \sum_{\alpha} \widehat{f}(\alpha) \chi_{\alpha}(xe_i) \right) = \frac{1}{2} \left( \sum_{\alpha} \widehat{f}(\alpha) \chi_{\alpha}(x) (1 - \chi_{\alpha}(e_i)) \right)$$
$$= \sum_{\alpha: \alpha_i = 1} \widehat{f}(\alpha) \chi_{\alpha}(x),$$

and the claim follows from Parseval.

We remark that quantities such as  $f(x) - f(xe_i)$  are often thought of as the derivative of f in direction i, and so they make sense for general functions (as opposed to only Boolean valued functions). This can be used to generalize the notion of influence of variables to general functions as norms of this derivative.

In addition, due to the formula above one can ask how much of the influence of f comes from the "low-degree" part of f and how much of it comes from the "low-degree" part, and with respect to it we define low-degree influences:

**Definition 1.7.** Let  $d \in \mathbb{N}$ ,  $f : \{-1, 1\}^n \to \mathbb{R}$  and  $i \in [n]$ . The degree d influence of f is defined as

$$I_i^{\leqslant d}[f] = \sum_{\substack{\alpha \in \mathbb{F}_2^n : |\alpha| \leqslant d \\ \alpha_i = 1}} \widehat{f}(\alpha)^2.$$

We end this section with a simple property of low-degree influences (which is the primary reason we use it instead of influences), stating that there can not be too many variables with large low-degree influence.

**Lemma 1.8.** Let  $f: \{-1,1\}^n \to \mathbb{R}$ ,  $d \in \mathbb{N}$ . Then  $\sum_{i=1}^n I_i^{\leqslant d}[f] \leqslant d\|f\|_2^2$ . Consequently, if  $f: \{-1,1\}^n \to [-1,1]$ , then for all  $\tau > 0$  the number of coordinates  $i \in [n]$  for which  $I_i^{\leqslant d}[f] \geqslant \tau$ , is at most  $\frac{d}{\tau}$ .

Proof. By definition,

$$\sum_{i=1}^{n} I_{i}^{\leqslant d}[f] = \sum_{i=1}^{n} \sum_{\substack{\alpha: |\alpha| \leqslant d \\ \alpha_{i}=1}} \widehat{f}(\alpha)^{2} = \sum_{\alpha: |\alpha| \leqslant d} \sum_{i=1}^{n} 1_{\alpha_{i}=1} \widehat{f}(\alpha)^{2} = \sum_{\alpha: |\alpha| \leqslant d} |\alpha| \, \widehat{f}(\alpha)^{2},$$

which is at most 
$$d\sum_{\alpha: |\alpha| \leqslant d} \widehat{f}(\alpha)^2 \leqslant d\sum_{\alpha} \widehat{f}(\alpha)^2 \leqslant d\|f\|_2^2$$
.

#### 1.5.2 Majority is Stablest for Bounded Functions

We are now ready to state the Majority is Stablest theorem for bounded functions, and we state it separately for positive  $\rho$ 's and negative  $\rho$ 's. For  $\rho > 0$ , we have:

**Theorem 1.9** (Majority is Stablest). Let  $\rho \in [0,1]$  and fix  $\eta > 0$ . Then there are  $d \in \mathbb{N}$  and  $\tau > 0$  such that if  $f : \{-1,1\}^n \to [-1,1]$  has  $\mathbb{E}[f] = 0$  and  $\max_i I_i^{\leq d}[f] \leq \tau$ , then

$$\mathsf{Stab}_{\rho}(f) \leqslant 1 - \frac{2}{\pi}\mathsf{Arccos}(\rho) + \eta.$$

The stability of majority. We note that the reason for the name of this theorem is that the stability of the majority function is the right hand side. Indeed, taking  $h: \{-1,1\}^n \to \{-1,1\}$  to be the majority function, that is, h(x) = 1 if  $|\{i \mid x_i = 1\}| \geqslant 1$  and otherwise h(x) = -1, one has that  $\operatorname{Stab}_{\rho}(h) = \frac{1}{\pi} \operatorname{Arccos}(\rho) + o(1)$ : to see that, note that we may define, for each  $v \in \{+1,-1\}^n$  the function  $h_v: \{-1,1\}^n \to \{-1,1\}$  which is 1 if  $\langle v,x\rangle > 0$  and -1 otherwise. Thus, the majority function is  $h_v$  for v=1, and by symmetry it follows that the stability of all  $h_v$ 's are the same. Hence,

$$\begin{split} \mathsf{Stab}_{\rho}(\mathsf{Majority}) &= \mathop{\mathbb{E}}_{v} \left[ \mathsf{Stab}_{\rho}(h_{v}) \right] = \mathop{\mathbb{E}}_{v} \left[ 1 - 2 \mathop{\Pr}_{(x,y)} \mathop{\Pr}_{\rho\text{-correlated}} \left[ h_{v}(x) \neq h_{v}(y) \right] \right] \\ &= 1 - 2 \mathop{\mathbb{E}}_{(x,y)} \left[ \mathop{\mathbb{E}}_{v} \left[ 1_{\mathsf{sign}(\langle v, x \rangle) \neq \mathsf{sign}(\langle v, y \rangle)} \right] \right]. \end{split}$$

Fixing x and y, we have that  $\mathbb{E}_v\left[1_{\mathsf{sign}(\langle v,x\rangle)\neq\mathsf{sign}(\langle v,y\rangle)}\right]\approx \frac{1}{\pi}\theta(x,y)+o(1)$ . This is because v can be thought of as a random vector on the unit sphere, and it produces different signs with x and y if and only if they lie in different sides of the hyperplane it is normal to. Since v is a random vector, the hyperplane it is normal to is also random, hence the probability it passes between x and y is proportional to the angle between them. Also, we have that  $\theta(x,y) = \operatorname{Arccos}\left(\frac{\langle x,y\rangle}{\|x\|_2\|y\|_2}\right)$ , and  $\langle x,y\rangle = (\rho+o(1))n$  with high probability and so  $\theta(x,y) \approx \operatorname{Arccos}(\rho)$ , so we get  $\operatorname{Stab}_{\rho}(\operatorname{Majority}) \approx 1 - \frac{2}{\pi}\operatorname{Arccos}(\rho)$ .

Hence, the above theorem says that the stability of majority is the largest possible (up to o(1)) within the class of functions with small influences.

For  $\rho \leq 0$ , we have the following result.

**Theorem 1.10** (Majority is Stablest). Let  $\rho \in [-1,0]$  and fix  $\eta > 0$ . Then there are  $d \in \mathbb{N}$  and  $\tau > 0$  such that if  $f : \{-1,1\}^n \to [-1,1]$  has  $\mathbb{E}[f] = 0$  and  $\max_i I_i^{\leq d}[f] \leq \tau$ , then

$$\operatorname{\mathsf{Stab}}_{\rho}(f)\geqslant \frac{2}{\pi}\operatorname{\mathsf{Arccos}}(-\rho)-1-\eta.$$

# 2 A Reduction from Unique-games to Max-cut

## 2.1 The Starting Point of the Reduction

We first recall the Unique-games problem and the Unique-Games Conjecture, which is the problem we reduce from and the hardness assumption we require to carry out the proof.

**Definition 2.1.** An instance of Unique-Games is an instance of Label-cover  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \Phi = \{\Phi_e\}_{e \in E})$  wherein  $|\Sigma_L| = |\Sigma_R|$  and furthermore each constraint  $\Phi_e$  is a permutation. That is, for each  $e \in E$  there is a 1-to-1 map  $\phi_e \colon \Sigma_L \to \Sigma_R$  such that

$$\Phi_e = \{ (\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma_L \}.$$

Recall the Unique-games conjecture, which asserts that given a Unique-games instance it is NP-hard to distinguish between the case it is highly satisfiable and the case only a small fraction of the constraints can be satisfied.

**Conjecture 2.2.** For all  $\varepsilon, \delta > 0$  there is  $k \in \mathbb{N}$  such that gap-UniqueGames $[1 - \varepsilon, \delta]$  is NP-hard on instances with alphabet size at most k.

We will further assume that the Unique-games instances we are dealing with are over regular graphs; this can be added as an assumption if you'd like, however this can also be arranged by standard techniques.

#### 2.2 The Reduction

We are now ready to present the reduction. Let  $\rho = 1 - \varepsilon$ .

Starting with a Unique-games instance  $\Psi=(G=(L\cup R,E),\Sigma_L,\Sigma_R,\Phi)$ , we wish to construct a Max-Cut instance with the properties described above. The idea will be to introduce, for each vertex  $u\in L$  a separate hybercube  $\{-1,1\}^{\Sigma_L}$ , and using a cut in that hypercube to encode the label that u is supposed to get in  $\Psi$ . More specifically, we will want to associate with each label  $\sigma$  of u which is supposed to have high value; this will be the dictatorship cut, i.e. the cut defined by  $f_u(x)=x_\sigma$ . Once we do that, we will be able to argue that if  $\Psi$  has a good assignment, then the graph we produce G will have a large cut corresponding to the dictatorship functions in each hypercube.

To ensure soundness, we must take care of two potential issues:

- 1. Penalizing cuts that are defined by functions that do not "resemble" any dictatorship. We have already dealt with this issue the last section, wherein we argued that in that case the cut size would be at most  $1 \frac{1}{\pi} \mathsf{Arccos}(\rho) + o(1)$  if f does not have any coordinate with significant low-degree influence.
- 2. Penalizing violating the constraints of  $\Psi$ . Namely, suppose we have two vertices  $u \in L$ ,  $v \in R$  that have an edge between them, and they have been assigned by dictatorship functions  $f_u(x) = x_{\sigma_u}$ ,  $f_v(x) = y_{\sigma_v}$ , but  $\sigma_v$ ,  $\sigma_u$  do not satisfy the constraint between u and v in  $\Psi$ . In that case, we would want to penalize this cut, as it does not correspond to a good assignment in  $\Psi$ . To deal with this issue, our edges will not really be inside the hypercube of each vertex v, but rather across hypercubes. For that, it is important to note that there is a natural bijection between the hypercube of v and the hypercube of v respecting the constraint between them, which is simply v0 where v1 where v2 where v3 where v4 where v5 where v6 and the

This almost finishes the informal overview of the reduction, except that if we were to execute the plan as is, we would get a bipartite graph (the sides being the hypercubes of V and the hypercubes of U), and to remedy that we only leave one of these sides alive, and take two steps in the graph of  $\Psi$  instead of one.

We now proceed to the formal construction of the reduction. Given  $\Psi = (G = (L \cup R, E), \Sigma_L, \Sigma_R, \Phi)$ , we construct a weighted max-cut instance G = (V', E', w) as follows.

- The vertices: For each u ∈ L we construct a cube over Σ<sub>L</sub>, {u} × {-1,1}<sup>Σ</sup>, which we refer to as the long-code of u. A ±1 assignment to these vertices should be thought as a potential encoding of one of the labels in Σ<sub>L</sub> for u.
- The edges are weighted according to the following randomized process. Sample  $v \in R$  and  $u, u' \in L$  two neighbours of v independently. Let x be a uniformly chosen vector from  $\{-1,1\}^{\Sigma_R}$ , and sample  $y \sim T_{-\rho}x$ . Consider the points

$$z = \phi_{v,u}(x),$$
  $z' = \phi_{v,u'}(y),$  where  $\phi_{v,u}(y)_{\sigma} = y_{\phi_{(v,u)}(\sigma)} \ \forall \sigma \in \Sigma_L.$ 

The edge output by the process is (z, z').

We prove the following lemma, encapsulating the analysis of the reduction.

**Lemma 2.3.** For all  $\rho \in (0,1)$ ,  $\delta > 0$  there is  $\eta > 0$  such that:

- 1. Completeness: if  $\Psi$  is at least  $1-\eta$  satisfiable, then there is a cut in G of weight at least  $\frac{1}{2}(1+\rho)-\delta$ .
- 2. Soundness: if  $\Psi$  is at most  $\eta$  satisfiable, then G has no cut whose weight exceeds  $1 \frac{1}{\pi} \mathsf{Arccos}(\rho) + \delta$ .

## 2.3 Analysis of the reduction

We now analyze the construction. First, we show the completeness of the construction, asserting that if  $\Psi$  is highly satisfiable, then there exists a large cut on the graph we have constructed.

#### 2.4 Completeness

Suppose there are labelings  $A_L \colon L \to \Sigma_L$  and  $A_R \colon R \to \Sigma_R$  satisfying at least  $1 - \eta$  fraction of the edges. We assign  $\pm 1$  values to the cube of u according to the dictatorship assignment of A(u). Namely, we define the cut in the graph G by

$$f(u,x) = x_{A_L(u)} \text{ for } (u,x) \in V \times \{-1,1\}^{\Sigma_L}.$$

We analyze the weight of the cut defined by f. Looking at the process describing the weights of the edges in G', Since the graph of  $\Psi$  is regular, the marginal distribution of each one of the edges (v,u),(v,u') is uniform; therefore the probability both are satisfied by  $A_L$  and  $A_R$  is at last  $1-2\eta$ . Sample x,y as in the process, and look at  $\phi_{(v,u)}(x),\phi_{(v,u')}(y)$ . Note that  $y_{A_R(v)}\neq x_{A_R(v)}$  with probability  $\frac{1}{2}+\frac{1}{2}\rho$ , and if that happens, since both edges (v,u) and (v,u') are satisfied, we get that

$$f(u,z) = z_{A_L(u)} = z_{\phi_{v,u}(A_L(u))} = x_{A_R(v)} \neq y_{A_R(v)} = z'_{\phi_{v,u'}(A_L(u'))} = f(u',z').$$

We conclude that the weight of edges crossing the cut is at least  $\frac{1}{2} + \frac{1}{2}\rho - 2\eta$ .

#### 2.5 Soundness

In this part, we show that if the UG instance  $\Psi$  had no good satisfying assignments then the graph G does not have a large cut. We prove it in a counter-positive way: assuming we have a large cut in the graph, we will construct a good assignment for  $\Psi$ .

Let  $f: L \times \{-1,1\}^{\Sigma_L} \to \{-1,1\}$  be a function corresponding to a large cut, that is a cut of size at least  $\frac{1}{\pi} \text{Arccos}(\rho) + \delta$ . The fractional size of the cut is exactly

$$\Pr_{\substack{v,u,u'\\x,y,z,z'}} \left[ f(u',z') \neq f(u,z) \right].$$

Let  $\nu$  be a vector from  $\{-1,1\}^{\sigma}$  such each coordinate is -1 with probability  $\frac{1}{2}(1-\rho)$ . Then the previous probability is the same as

$$\Pr_{\substack{v,u,u'\\x,\nu}} \left[ f(u,\phi_{(v,u)}x) \neq f(u',\nu \cdot \phi_{(v,u')}x) \right].$$

Define for  $u \in U$ ,  $v \in V$ 

$$g_v(x) = \underset{u:(u,v) \in E}{\mathbb{E}} \left[ f(u,\phi_{(v,u)}x) \right], \qquad g_u(x) = f(u,x).$$

Intuitively, v asks his neighbours what side it should be on, and takes the average of the suggestions. Then

$$\begin{split} \Pr_{\substack{u,v,v'\\x,\nu}} \left[ f(u,\phi_{(v,u)}x) \neq f(u',\nu \cdot \phi_{(v,u')}x) \right] &= \frac{1}{2} \left( 1 - \mathop{\mathbb{E}}_{\substack{v,u,u'\\x,\nu}} \left[ f(u,\phi_{(v,u)}x) f(u',\nu \cdot \phi_{(v,u')}x) \right] \right) \\ &= \frac{1}{2} \left( 1 - \mathop{\mathbb{E}}_{\substack{v\\x,\nu}} \left[ \mathop{\mathbb{E}}_{u} \left[ f(u,\phi_{(v,u)}x) \right] \mathop{\mathbb{E}}_{u'} \left[ f(u',\phi_{(v,u')}(\nu \cdot x)) \right] \right] \right) \\ &= \frac{1}{2} (1 - \mathop{\mathbb{E}}_{\substack{v\\x,\nu}} \left[ \operatorname{Stab}_{-\rho}[g_v] \right] \right). \end{split}$$

We conclude that since the fractional size of the cut is at least  $1 - \frac{1}{\pi} Arccos(\rho) + \delta$ , it holds that

$$\mathop{\mathbb{E}}_{v}\left[\mathsf{Stab}_{-\rho}[g_{v}]\right] < \frac{2}{\pi}\mathsf{Arccos}(\rho) - 1 - 2\delta.$$

We say v is good if  $\mathsf{Stab}_{-\rho}[g_v] \leqslant \frac{1}{\pi}\mathsf{Arccos}(\rho) - \delta$ . Note that by an averaging argument, it follows that at least  $\delta$  fraction of the  $v \in L$  are good, and we denote the set of these by  $L_{\mathsf{good}}$ . We fix  $d, \tau$  corresponding to  $\rho, \delta$  as in Theorem 1.10 and apply it to get that there is i such that  $I_i^{\leq d}[g_v] \geqslant \delta$  for each  $v \in L_{\mathsf{good}}$ . Define

$$\operatorname{List}_{\xi}(v) = \left\{ i \mid I_i^{\leqslant d}[g_v] \geqslant \xi \right\}.$$

Since the sum of the d degree influence is at most d,  $|\operatorname{List}(v)| \leq d/\xi$ ; the important point is that this quantity only depends on  $\rho, \varepsilon$  (and not on  $|\Sigma_L|$ ). We finish by showing that if v is good and  $i \in \operatorname{List}_{\tau}(v)$ , then a non-negligible fraction of his neighbours u have  $\phi_{(v,u)}(i) \in \operatorname{List}_{\tau/2}(u)$ . To see that we first prove a simple connection between the Fourier coefficients of  $g_v$ 's and  $g_u$ 's:

Claim 2.4. For all  $\alpha \in \mathbb{F}_2^{\Sigma_R}$  we have  $\widehat{g_v}(\alpha) = \mathbb{E}_{u:(u,v)\in E}\left[\widehat{g_u}(\phi_{(v,u)}\alpha)\right]$ .

Proof.

$$\widehat{g_v}(\alpha) = \underset{x}{\mathbb{E}} \left[ g_v(x) \chi_{\alpha}(x) \right] = \underset{x}{\mathbb{E}} \left[ \underset{u}{\mathbb{E}} \left[ g_u(\phi_{(u,v)}x) \right] \chi_{\alpha}(x) \right] = \underset{u}{\mathbb{E}} \left[ \underset{y}{\mathbb{E}} \left[ g_u(y) \chi_{\alpha}(\phi_{(u,v)}^{-1}y) \right] \right]$$

$$= \underset{u}{\mathbb{E}} \left[ \underset{y}{\mathbb{E}} \left[ g_u(y) \chi_{\phi_{(u,v)}\alpha}(y) \right] \right]$$

$$= \underset{u}{\mathbb{E}} \left[ \widehat{g_u}(\phi_{(u,v)}\alpha) \right]$$

The second equality is by the definition of  $g_v$ , the third equality is since  $\chi_{\alpha}(\phi x) = \chi_{\phi^{-1}\alpha}(x)$  for a permutation  $\phi$ .

**Lemma 2.5.** Suppose  $v \in L_{good}$ , and let  $i \in List_{\tau}(v)$ . Then

$$\Pr_{u:(u,v)\in E}\left[\phi_{v,u}(i)\in \mathsf{List}_{\tau/2}(u)\right]\geqslant \frac{\tau}{2}.$$

Proof. By definition and Claim 2.4 we get that

$$\tau \leqslant I_i^{\leqslant d}[g_v] = \sum_{\alpha: |\alpha| \leqslant d, \alpha_i = 1} \widehat{g_v}^2(\alpha) = \sum_{\alpha: |\alpha| \leqslant d, \alpha_i = 1} \mathbb{E}_{u:(u,v) \in E} \left[\widehat{g_u}(\phi_{(v,u)}\alpha)\right]^2,$$

and so by Jensen's inequality we conclude that

$$\tau \leqslant \sum_{\alpha: |\alpha| \leqslant d, \alpha_i = 1} \mathbb{E}_{u:(u,v) \in E} \left[ \widehat{g_u}(\phi_{(v,u)}\alpha)^2 \right] = \mathbb{E}_{u:(u,v) \in E} \left[ \sum_{\alpha: |\alpha| \leqslant d, \alpha_i = 1} \widehat{g_u}(\phi_{(v,u)}\alpha)^2 \right]$$

$$= \mathbb{E}_{u:(u,v) \in E} \left[ \sum_{\beta: |\alpha| \leqslant d, \beta_{\phi_{v,u}(i)} = 1} \widehat{g_u}(\beta)^2 \right]$$

$$= \mathbb{E}_{u:(u,v) \in E} \left[ I_{\phi_{v,u}(i)}^{\leqslant d} [g_u] \right].$$

As  $I_{\phi_{v,u}(i)}^{\leqslant d}[g_u] \leqslant 1$  always, it follows that with probability at least  $\tau/2$  over the choice of u we have that  $I_{\phi_{v,u}(i)}^{\leqslant d}[g_u] \geqslant \tau/2$ .

#### Randomized assignment to the Unique-Games instance

Now we finish the proof. For each  $v \in L_{\mathsf{good}}$  assign a label  $i \in \mathsf{List}_\tau(v)$  randomly, and for each  $u \in R$  assign a label from  $\mathsf{List}_{\tau/2}(u)$  randomly. We now lower the probability a randomly chosen edge from  $\Psi$  is satisfied.

Choose (u,v) randomly. With probability at least  $\delta$ , the vertex v is good and we choose some label  $i \in \mathsf{List}_\tau(v)$  for it. We condition on v and i. By Lemma 2.5, it follows that with probability at least  $\tau/2$  over the choice of u we have that the label  $\phi_{v,u}(i)$  is in  $\mathsf{List}_{\tau/2}(u)$ , and as that list contains at most  $d/(\tau/2)$  elements it follows that we have assigned the label  $j = \phi_{v,u}(i)$  to u with probability at least  $\frac{\tau/2}{d}$ .

We conclude that, in expectation over the choice of the assignment, the probability that a random edge is satisfied is at least

$$\delta \cdot \frac{\tau}{2} \cdot \frac{\tau/2}{d} = \delta'(\delta, \rho) > 0$$

hence this is smaller than the soundness of the original Unique-games instance provided that  $\eta < \delta'$ . Hence, we conclude that if the original Unique-games instance was at most  $\eta$  satisfiable for sufficiently small  $\eta$ , then the graph G' we produce has no cut of size  $\frac{1}{2}\left(1-\frac{1}{\pi}\mathrm{Arccos}(\rho)\right)+\delta$ . This completes the proof of Lemma 2.3.

**Remark 2.6.** We stress here an important point, which is that the performance of the randomized strategy we found for the Unique-games may depend on various parameters we have used in the reduction (such as the noise rate  $\rho$ ). Most importantly though, it does not depend on the alphabet size of the Unique-games instance, so if we take the soundness of the Unique-games instance to be small enough (which naturally would mean its alphabet size is also large) we would reach a contradiction. This is very typical to hardness of approximation result that use list-decoding arguments such as above (namely, an argument that is able to produce a short list of candidate labels for a vertex and then chooses one randomly), highlighting the importance of "dimension-free" result in Fourier analysis (such as the Majority is Stablest theorem).

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.
