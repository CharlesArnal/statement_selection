# 18.218 Topics in Combinatorics Spring 2021 – Lecture 1

#### Dor Minzer

In this course, we will mostly be studying Boolean functions over the hypercube, i.e.  $f: \{0,1\}^n \to \{0,1\}$ . Our primary (but not only) tool will be, what is often called, discrete Fourier analysis. Here and throughout, we will think of the Boolean hypercube as being equipped with some probability measure, which for the majority of the time will just be the uniform distribution.

Having said that, the theory we will present often generalizes to other measures on the Boolean hypercube, such as the p-biased measure. Further the theory often extends to finite product spaces, i.e. spaces of the form  $(\Omega = \Omega_1 \times \ldots \times \Omega_n, \mu = \mu_1 \times \ldots \mu_n)$ , and in recent years beyond that (we may discuss this towards the end of the course).

## 1 Course overview

Since this is the first time this course is ran, the exact material we cover is yet to be determined. The plan is to touch the following topics.

- 1. **Fundamentals of discrete Fourier analysis.** We will begin the course by presenting basic definitions and notions, such as the Fourier decomposition and influences of variables. Throughout the course, we will present basic tools and results in the area, such as the hypercontractive inequality, the KKL theorem, Junta theorems by Friedgut and Bourgain, sharp thresholds and the invariance principle.
- 2. **Applications of Fourier analysis in various areas in TCS.** We will discuss several applications of Fourier analysis in areas such as property testing and learning theory.
- 3. Applications of Fourier analysis in Hardness of Approximation. We will briefly discuss a prominent outstanding conjecture in theoretical computer science known as the Unique-Games Conjecture. We will use some basic results from Fourier analysis to show several consequences of this conjecture, such as the (conditional) optimality of the Goemans-Williamson algorithm for Max-Cut, and (conditional) hardness of the Vertex-Cover problem.
- 4. **Applications of Fourier analysis in Extremal Combinatorics.** Extremal Combinatorics is an area, which roughly speaking asks how large a collection of specific objects can be if it satisfies a certain constraint. For example, how large can a collection of subsets of [n] be provided any two intersect non-trivially? We will see how results in analysis play an important role in giving detailed answers to some of these questions.
- 5. Advanced Topics. Towards the end of the course we will discuss more advanced topics, which are advances in the area achieved only recently. These includes the resolution of the sensitivity conjecture, an extension of the hypercontractive inequality referred to in the literature as "global hypercontractivity", and the Fourier entropy conjecture.

Without further ado, let's get down to business.

## 2 The basic set-up

## 2.1 The Fourier basis

We will think of the domain  $\{0,1\}^n$  as the additive group modulo 2. Often times, it will be notationally convenient for us to turn this "addition" operation into a product, by the identification  $b \to (-1)^b$  from  $\{0,1\}$  to  $\{1,-1\}$ , and thus we will think of functions  $f: \{-1,1\}^n \to \{-1,1\}$ .

We note that the collection of functions  $f: \{-1,1\}^n \to \mathbb{R}$  forms a linear space over  $\mathbb{R}$ , and we next introduce an inner product operation over it. This inner product is simply the  $L^2$  inner product: for any  $f,g: \{-1,1\}^n \to \mathbb{R}$  we define

$$\langle f, g \rangle = \underset{x}{\mathbb{E}} [f(x)g(x)].$$

Here and throughout, unless stated otherwise, the distribution over x is uniform over  $\{-1,1\}^n$ .

Now that we have an inner product, is makes sense to come up with an orthonormal basis with respect to it, which is often a useful tool from linear algebra that helps us understand vector spaces better. In this particular case there is a very nice basis, given by the characters of the additive group. Formally, for each  $S \subseteq [n]$  we define a function  $\chi_S \colon \{-1,1\}^n \to \{-1,1\}$  as

$$\chi_S(x) = \prod_{i \in S} x_i.$$

**Claim 2.1.** The collection  $\{\chi_S\}_{S\subseteq[n]}$  forms an orthonormal set (In particular, it is a linearly independent set).

*Proof.* We start with two simple observations. Let  $S, T \subseteq [n]$  be any two subsets.

1.  $\chi_S(x)\chi_T(x) = \chi_{S\Delta T}(x)$ , where  $\Delta = (S \setminus T) \cup (T \setminus S)$  is the symmetric difference between S and T. Indeed,

$$\chi_S(x)\chi_T(x) = \prod_{i \in S \setminus T} x_i \prod_{i \in S \cap T} x_i \prod_{i \in T \setminus S} x_i \prod_{i \in S \cap T} x_i = \prod_{i \in S \setminus T \cup T \setminus S} x_i \left(\prod_{i \in S \cap T} x_i\right)^2 = \chi_{S\Delta T}(x).$$

2. If  $S \subseteq [n]$  is non-empty, then  $\mathbb{E}_x[\chi_S(x)] = 0$ . Indeed, fix  $i \in S$ , then writing  $S = Q \cup \{i\}$  and  $x = (y, x_i)$  we have

$$\mathbb{E}_{x}\left[\chi_{S}(x)\right] = \mathbb{E}_{y,x_{i}}\left[\chi_{Q}(y)x_{i}\right] = \frac{1}{2}\mathbb{E}\left[\chi_{Q}(y) - \chi_{Q}(y)\right] = 0.$$

The proof is now concluded by noting that if  $S \neq T$ , then  $\langle \chi_S, \chi_T \rangle = \mathbb{E}_x \left[ \chi_S(x) \chi_T(x) \right] = \mathbb{E}_x \left[ \chi_{S\Delta T}(x) \right] = 0$ , and if S = T then this is 1.

Now from dimension considerations, it follows that the collection  $\{\chi_S\}_{S\subseteq[n]}$  is in fact a basis for the space of real-valued functions over  $\{-1,1\}^n$ , and thus any function  $f:\{-1,1\}^n\to\mathbb{R}$  can be written as a linear combination of it. The standard notation for this is

$$f(x) = \sum_{S \subseteq [n]} \widehat{f}(S) \chi_S(x),$$

where  $\widehat{f}(S)$  are called the Fourier coefficients of f. Moreover, since the basis we used is orthonormal, there is a simple formula for each Fourier coefficient, namely  $\widehat{f}(S) = \langle f, \chi_S \rangle$ .

**Claim 2.2.** The following holds for any  $f, g: \{-1, 1\}^n \to \mathbb{R}$ :

- 1. Plancherel's equality:  $\langle f, g \rangle = \sum_{S \subseteq [n]} \widehat{f}(S) \widehat{g}(S)$ .
- 2. Parseval's equality:  $||f||_2^2 = \sum_{S \subset [n]} \widehat{f}(S)^2$ .

*Proof.* For the first item, we use the bi-linearity of the inner product

$$\langle f, g \rangle = \left\langle \sum_{S \subseteq [n]} \widehat{f}(S) \chi_S, \sum_{T \subseteq [n]} \widehat{g}(T) \chi_T \right\rangle = \sum_{S, T \subseteq [n]} \widehat{f}(S) \widehat{g}(T) \left\langle \chi_S, \chi_T \right\rangle = \sum_{S, T \subseteq [n]} \widehat{f}(S) \widehat{g}(T) \mathbf{1}_{S = T}$$
$$= \sum_{S \subseteq [n]} \widehat{f}(S) \widehat{g}(S).$$

The second item is just an instantiation of the first one with f = g, using  $||f||_2^2 = \langle f, f \rangle$ .

Next, we define the mean and the variance of a Boolean function. To do that, we think of f(x) as a random variable, which is sampled by taking  $x \in_R \{-1,1\}^n$ , and then evaluating f(x). The mean of f is the mean of this random variable, and it denoted by

$$\mathbb{E}[f] = \mathbb{E}[f(x)] = \widehat{f}(\emptyset).$$

The variance of f, denoted by var(f), is the variance of this random variable, i.e.

$$\mathrm{var}(f) = \mathop{\mathbb{E}}_{x} \left[ (f(x) - \mathop{\mathbb{E}}\left[f\right])^{2} \right].$$

Claim 2.3. 
$$\operatorname{var}(f) = \sum\limits_{S \neq \emptyset} \widehat{f}(S)^2$$
.

*Proof.* Consider the function  $g(x) = f(x) - \mathbb{E}[f]$ , and note that for any  $S \neq \emptyset$ ,  $\widehat{g}(S) = \widehat{f}(S)$ , and  $\widehat{g}(\emptyset) = 0$ . Thus, by Parseval

$$\operatorname{var}(f) = \|g\|_2^2 = \sum_{S \neq \emptyset} \widehat{f}(S)^2.$$

#### 2.2 Property testing

We mention some applications of the material we have seen so far that we may see in the subsequent lectures.

### 2.2.1 Linearity testing

A function  $f: \{-1,1\}^n \to \{-1,1\}$  is said to be linear if for any  $x,y \in \{-1,1\}^n$  it holds that f(x)f(y) = f(xy), where  $(xy)_i = x_iy_i$ . We have already seen a good collection of linear functions, namely the Fourier characters (check that!). Are there any "inherently different linear functions"?

Another related question is the following. Suppose  $f: \{-1,1\}^n \to \{-1,1\}$  is approximately satisfies the definition of a linear function, i.e. f(x)f(y) = f(xy) holds for  $1-\varepsilon$  fraction of the pairs x,y. Does that tell us anything about the structure of the function f? You are encouraged to think of this question at home.

Next time, we will discuss a more challenging version of this question, and see how the power of Fourier analysis gives a very elegant solution to this problem.

## 2.2.2 Sparse functions

A function  $f: \{-1,1\}^n \to \mathbb{R}$  is said to be t-Fourier sparse if the support size of its Fourier spectrum has size at most t. A function  $g: \{-1,1\}^n \to \{-1,1\}$  is said to be  $(t,\varepsilon)$ -Fourier sparse if there is a t-Fourier sparse function f such that  $||f-g||_2 \le \varepsilon$ . How can one test whether a function is Fourier sparse? Can one *learn* such functions (i.e. find an approximator) for such functions efficiently, given query access to them?

### 2.2.3 Junta testing

An important subclass of sparse functions is the class of juntas. A function  $f: \{-1,1\}^n \to \mathbb{R}$  is said to be a t-junta if there is  $T \subseteq [n]$  of size at most t, and  $g: \{-1,1\}^T \to \mathbb{R}$ , such that  $f(x) = g(x_T)$ . Can one test juntas more efficiently? Learn?

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.218 Topics in Combinatorics Spring 2021 – Lecture 2

## Dor Minzer

## 1 The BLR lineairty test

Recall that a function  $f: \{-1,1\}^n \to \{-1,1\}$  is called linear if for every  $x,y \in \{-1,1\}^n$  it holds that f(xy) = f(x)f(y) where  $(xy)_i = x_iy_i$ . How does test, given a query access to a function f, if f is a linear function or is far from any linear function?

One idea that makes sense is to consider the following problem. Suppose that f(xy) = f(x)f(y) holds for  $\frac{1}{2} + \delta$  fraction of the pairs  $x, y \in \{-1, 1\}^n$ ; what can we say about f? Does it have to be close, in some way, to a linear function? This question makes sense both for large  $\delta$ , i.e.  $\delta = \frac{1}{2} - \varepsilon$ , as well as for small  $\delta > 0$ .

To answer this question, it is convenient to consider the convolution operation that is defined as follows. Given  $f, g: \{-1, 1\}^n \to \mathbb{R}$ , we define  $f * g: \{-1, 1\}^n \to \mathbb{R}$  by:

$$(f * g)(x) = \mathop{\mathbb{E}}_{y} [f(y)g(xy)].$$

The most significant property of convolutions is the effect they have in the Fourier domain, as given in the following claim.

**Claim 1.1.** For all  $S \subseteq [n]$  it holds that  $\widehat{f * g}(S) = \widehat{f}(S)\widehat{g}(S)$ .

Proof. By definition,

$$\widehat{f * g}(S) = \underset{x}{\mathbb{E}} [(f * g)(x)\chi_S(x)] = \underset{x,y}{\mathbb{E}} [f(y)g(xy)\chi_S(x)] = \underset{x,y}{\mathbb{E}} [f(y)\chi_S(y)g(xy)\chi_S(xy)]$$
$$= \underset{y,z}{\mathbb{E}} [f(y)\chi_S(y)g(z)\chi_S(z)],$$

and as y, z are independent, the last expectation is equal to  $\widehat{f}(S)\widehat{g}(S)$ .

Armed with the above claim, we are ready to analyze the linearity test proposed above.

**Theorem 1.2.** Suppose  $f: \{-1,1\}^n \to \{-1,1\}$  is a function such that  $\Pr_{x,y} [f(x)f(y) = f(xy)] \geqslant \frac{1}{2} + \delta$ . Then there exists  $S \subseteq [n]$  such that  $\widehat{f}(S) \geqslant 2\delta$ .

*Proof.* Note that whenever the test passes, the value of f(x)f(y)f(xy) is 1, and otherwise the value is -1, so

$$\mathbb{E}_{x,y}[f(x)f(y)f(xy)] = \Pr_{x,y}[f(x)f(y) = f(xy)] - \Pr_{x,y}[f(x)f(y) \neq f(xy)] = 2\Pr_{x,y}[f(x)f(y) = f(xy)] - 1$$

$$\geq 2\delta.$$

Next, we relate the left hand side to the Fourier coefficients of f. By definition of the convolution,

$$\underset{x,y}{\mathbb{E}}\left[f(x)f(y)f(xy)\right] = \underset{x}{\mathbb{E}}\left[f(x)\underset{y}{\mathbb{E}}\left[f(y)f(xy)\right]\right] = \underset{x}{\mathbb{E}}\left[f(x)(f*f)(x)\right] = \langle f, f*f\rangle.$$

Next, using Plancherel and Claim 1.1, we have

$$\langle f, f * f \rangle = \sum_{S} \widehat{f}(S) \widehat{f * f}(S) = \sum_{S} \widehat{f}(S)^{3} \leqslant \max_{S} \widehat{f}(S) \sum_{S} \widehat{f}(S)^{2} \leqslant \max_{S} \widehat{f}(S) \|f\|_{2}^{2} = \max_{S} \widehat{f}(S).$$

Combining the two inequalities yields the result.

Recalling that  $\widehat{f}(S) = \langle f, \chi_S \rangle = 2 \Pr_x [f(x) = \chi_S(x)] - 1$ , we get that a function that passes the linearity test with probability  $1/2 + \delta$  must have correlation with a Fourier character. This very nice result exemplifies the power of the basic machinery we have set up so far; proving it without appealing to Fourier analysis is highly challenging.

Note that when  $\delta = \frac{1}{2} - \varepsilon$ , we even get that  $\Pr_x[f(x) = \chi_S(x)] \ge 1 - 2\varepsilon$ , so in this case f is *close* to a linear function. This is one of the earliest and basic results in the field of property testing, and later on in the course we will use it in the context of hardness of approximation.

**Remark 1.3.** Those of you that are familiar with Roth's theorem regarding the appearance of 3-term arithmetic progression in dense subsets of [N] may notice that similarity between the argument. The case here is much simpler since we are working with a group.

## 2 Random restrictions

Another basic and useful tool we will want to add to our toolbox is the notion of restrictions and random restrictions.

**Definition 2.1.** Suppose we have a function  $f: \{-1,1\}^n \to \mathbb{R}$ , a set of coordinates  $J \subseteq [n]$  and an assignment to them  $z \in \{-1,1\}^{\bar{J}}$ . The restricted function  $f_{\bar{J}\to z}: \{-1,1\}^J \to \mathbb{R}$  is defined by

$$f_{\bar{J}\to z}(y) = f(x_{\bar{J}} = z, x_J = y).$$

**Definition 2.2.** Given  $f: \{-1,1\}^n \to \mathbb{R}$  and  $J \subseteq [n]$ , a random restriction of f on J is a function  $f_{\bar{J}\to z}$  wherein  $z \in \{-1,1\}^{\bar{J}}$  is sampled uniformly at random.

Restrictions and random restrictions are a very powerful tool we will see some uses for throughout the course. In this lecture, we will focus on seeing some basic properties of it and intuition to where it is useful in. In the next lecture we will see a very cool application of them in the problem of learning Fourier sparse functions.

For now, we will begin by investigating several basic and useful properties of it. First, we give a formula for the Fourier coefficients of the restricted function.

**Claim 2.3.** Let  $f: \{-1,1\}^n \to \mathbb{R}$ ,  $J \subseteq [n]$ ,  $z \in \{-1,1\}^{\overline{J}}$  and  $S \subseteq J$ . We have

$$\widehat{f_{\bar{J}\to z}}(S) = \sum_{T\subseteq \bar{J}} \widehat{f}(S\cup T)\chi_T(z).$$

*Proof.* We write f according to its Fourier transform, decomposing a character into its J and  $\bar{J}$  parts

$$f(x) = \sum_{S \subset J, T \subset \bar{J}} \widehat{f}(S \cup T) \chi_{S \cup T}(x) = \sum_{S \subset J, T \subset \bar{J}} \widehat{f}(S \cup T) \chi_{S}(x_{J}) \chi_{T}(x_{\bar{J}}).$$

Plugging in the value y to  $x_J$  and z to  $x_{\bar{I}}$ , we get that

$$f_{\bar{J}\to z}(y) = f(y,z) = \sum_{S\subseteq J} \left( \sum_{T\subseteq \bar{J}} \widehat{f}(S\cup T) \chi_T(z) \right) \chi_S(y).$$

The claim now follows from the uniqueness of the Fourier decomposition.

Using the last claim, we have the following corollary.

**Claim 2.4.** Let  $f: \{-1,1\}^n \to \mathbb{R}$ ,  $J \subseteq [n]$  and  $S \subseteq J$ . We have

$$\mathbb{E}_{z}\left[\widehat{f_{\bar{J}\to z}}(S)^{2}\right] = \sum_{T\subseteq \bar{J}}\widehat{f}(S\cup T)^{2}.$$

*Proof.* Defining  $g(z) = \widehat{f_{\bar{J} \to z}}(S)$ , the left hand side is  $||g||_2^2$ , and the claim follows from the last claim and Parseval.

In some applications, it is useful to consider p-random restrictions, which are random restrictions in which the set J of live variables is also chosen randomly.

**Definition 2.5.** Given a function  $f: \{-1,1\}^n \to \mathbb{R}$  and a parameter  $p \in [0,1]$ , a p-random restriction is sampled by: taking  $J \subseteq [n]$  randomly by including each  $i \in [n]$  in J with probability p, and then taking  $z \in \{-1,1\}^{\overline{J}}$ .

What is the effect of a random restriction on a function? Let us consider a few examples.

- 1. Monomials: suppose  $f(x) = \chi_S(x) = \prod_{i \in S} x_i$ . Then if we take (J,z) a p-random restriction, we expect the restricted function  $f_{J \to z}$  to be a (signed) monomial of degree  $\approx p|S|$ . That is, random restriction "reduce" the degree of monomials; we will later see a more general statement along these lines.
- 2. An OR function, i.e. function of the form  $\bigvee_{i \in I} x_i$ . Under random restriction (J, z), the function either trivializes to 1, if there is a variable  $I_i$  in  $\bar{J}$  receiving the value 1, and otherwise the function reduces to an OR on roughly  $p|I_i|$  variables.
- 3. CNF formulas: i.e. a function  $f: \{0,1\}^n \to \{0,1\}$  of the form  $f(x) = \bigwedge_{i=1}^m \bigvee_{j \in I_i} x_j$ . Analyzing the effect of random restrictions on such functions is significantly more difficult (the Håstad switching lemma). For now it will be enough for us to understand that intuitively, random restrictions significantly simplify them: if there is a term that becomes completely 0, the function trivializes to 1; terms that become 1 disappear, and the rest considerably shrink in width.

We will now establish more rigorously several more properties that align and express some of the above intuition. We will try to capture the sense in which random restrictions reduce degrees, and for that we define the Fourier weight of a function on degrees.

**Definition 2.6.** Let  $f: \{-1,1\}^n \to \mathbb{R}$  be a function, and  $d \in \mathbb{N}$ . The level d Fourier weight of a function f is defined as

$$W^{=d}[f] = \sum_{|S|=d} \widehat{f}(S)^2.$$

We also define  $W^{\leqslant d}[f] = \sum\limits_{i \leqslant d} W^{=i}[f]$  and  $W^{\geqslant d}[f] = \sum\limits_{i \geqslant d} W^{=i}[f]$ .

**Claim 2.7.** Let  $f: \{-1,1\}^n \to \mathbb{R}$ ,  $d \in \mathbb{N}$ , and let (J,z) be a p-random restriction. Then

$$\underset{J,z}{\mathbb{E}}\left[W^{=d}[f_{\bar{J}\to z}]\right] = \sum_{Q}\widehat{f}(Q)^{2}\Pr\left[\operatorname{Bin}(\left|Q\right|,p) = d\right].$$

Proof. Expanding,

$$\underset{J,z}{\mathbb{E}}\left[W^{=d}[f_{\bar{J}\to z}]\right] = \underset{J,z}{\mathbb{E}}\left[\sum_{S\subseteq J,|S|=d}\widehat{f_{\bar{J}\to z}}(S)^2\right] = \underset{J}{\mathbb{E}}\left[\sum_{|S|=d}1_{S\subseteq J}\underset{z}{\mathbb{E}}\left[\widehat{f_{\bar{J}\to z}}(S)^2\right]\right].$$

Using Claim 2.4 we calculate the innermost expectation and hence get that

$$\mathbb{E}_{J,z} \left[ W^{=d}[f_{\bar{J} \to z}] \right] = \mathbb{E}_{J} \left[ \sum_{|S|=d} 1_{S \subseteq J} \sum_{T \subseteq \bar{J}} \widehat{f}(S \cup T)^{2} \right] = \sum_{Q} \mathbb{E}_{J} \left[ 1_{|Q \cap J| = d} \right] \widehat{f}(Q)^{2} \\
= \sum_{Q} \widehat{f}(Q)^{2} \Pr\left[ \operatorname{Bin}(|Q|, p) = d \right]. \square$$

There are two immediate corollaries one may derive from the above claim. The first one is that if f has most of its Fourier mass below level d, then  $f_{\bar{J}\to z}$  has most of its Fourier mass below level  $\approx pd$ .

**Corollary 2.8.** Suppose that  $f: \{-1,1\}^n \to \{-1,1\}$  satisfies  $W_{\geqslant d}[f] \leqslant \varepsilon$ , and let (J,z) be a p-random restriction. Then

$$\mathop{\mathbb{E}}_{I,z}\left[W^{\geqslant 2pd}[f_{\bar{J}\to z}]\right]\leqslant \varepsilon + \exp(-\Theta(pd)).$$

*Proof.* Summing the previous claim, we have that

$$\underset{J\!,z}{\mathbb{E}}\left[W^{\geqslant 2pd}[f_{\bar{J}\to z}]\right] = \sum_{Q} \widehat{f}(Q)^2 \Pr\left[\operatorname{Bin}(\left|Q\right|,p)\geqslant 2pd\right] = \sum_{k\geqslant 0} W^{=k}[f] \Pr\left[\operatorname{Bin}(k,p)\geqslant 2pd\right].$$

We break the last sum into two. For  $k \ge d$ , we bound it by  $W^{\ge d}[f]$ , which by the premise of the statement is at most  $\varepsilon$ . For k < d, we have that

$$\Pr[\mathsf{Bin}(k,p) \geqslant 2pd] \leqslant \Pr[\mathsf{Bin}(d,p) \geqslant 2pd] \leqslant \exp(-\Theta(pd)),$$

so the total contribution from these summands is at most  $\sum\limits_{k\geqslant 0}W^{=k}[f]\exp(-\Theta(pd))=\|f\|_2^2\exp(-\Theta(pd))=\exp(-\Theta(pd)).$ 

The second corollary asserts that if f has sizable mass around level d, then  $f_{\bar{J}\to z}$  has sizable weight around level pd.

**Definition 2.9.** We define the weight around level d to be  $W^{\approx d}[f] = \sum_{d \leqslant k \leqslant 2d} W^{=k}[f]$ .

**Corollary 2.10.** Let  $d \in \mathbb{N}$  and  $p \in [0,1]$  be such that  $pd \geqslant 10$ . Suppose that  $f : \{-1,1\}^n \to \{-1,1\}$  satisfies  $W_{\geqslant d}[f] \leqslant \varepsilon$ , and let (J,z) be a p-random restriction. Then

$$\underset{J,z}{\mathbb{E}}\left[W^{\approx pd}[f_{\bar{J}\to z}]\right]\geqslant \Omega(W^{\approx d}[f]).$$

*Proof.* The proof is similar to the proof of the last statement and is left to the reader.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 3

### Dor Minzer

In this lecture, we will present a learning algorithm for the class of Boolean functions that are close to sparse functions.

## 1 What is PAC learning?

In the PAC learning model (probably approximately correct), one is required to learn a function g from a certain concept class  $\mathcal{C} \subseteq \{f \colon \{-1,1\}^n \to \{-1,1\}\}$ . The input of the learner is a sequence of random input-output tuples,  $(x_i, f(x_i))$  for  $i = 1, \ldots, q$ , and the learner is supposed to product a hypothesis function  $h \colon \{-1,1\}^n \to \{-1,1\}$  such that h is likely to be close to g, say  $\|f-g\|_2 \leqslant \varepsilon$  with probability  $\geqslant 1-\delta$  (the probability here is over the randomness of the samples and the learner). The learner is called proper if  $h \in \mathcal{C}$  (i.e. the hypothesis itself is from the concept class), and otherwise it is called improper.

The advantage of PAC learning is that it is something that is potentially applicable in practice. In real life we often face the problem of getting random samples (say, occurrences of a virus) without the ability to produce something ourselves, and we wish to extract information using these samples. In theory, however, PAC learning model turns out to be fairly weak and does not allow for efficient learning algorithm for many problems. One thing it does allow to do is estimate Fourier coefficients.

For that, we introduce the basic and powerful concentration inequality known as Chernoff-Hoeffding bound.

**Fact 1.1.** Suppose  $Y_1, \ldots, Y_n$  are independent random variables such that  $|Y_i| \le 1$  almost surely. Then for every  $\varepsilon > 0$ ,

$$\Pr\left[\sum_{i=1}^{n} Y_i - \sum_{i=1}^{n} \mathbb{E}\left[Y_i\right] \geqslant \varepsilon n\right] \leqslant 2e^{-\frac{\varepsilon^2}{2+\varepsilon}n}.$$

**Claim 1.2.** For all  $\varepsilon, \delta > 0$ , there is  $q = O\left(\frac{\log(1/\delta)}{\varepsilon^2}\right)$  and an algorithm performing the following task. Given a sequence of random input-output pairs of  $f: \{-1,1\}^n \to [-1,1]$  and a character  $S \subseteq [n]$ , and algorithm produces an estimate  $a_S$  of  $\widehat{f}(S)$  such that

$$\Pr\left[|\widehat{f}(S) - a_S| \geqslant \varepsilon\right] \leqslant \delta.$$

*Proof.* By definition,  $\widehat{f}(S) = \mathbb{E}_x \left[ f(x) \chi_S(x) \right]$ . Thus, given the sequence  $(x_i, f(x_i))_{i=1,\dots,q}$  of input-output pairs, our estimator would be  $a_S = \frac{1}{q} \sum_i Y_i = \frac{1}{q} \sum_{i=1}^q f(x_i) \chi_S(x_i)$ . The Chernoff bound applied on  $Y_i$  (which are independent, bounded and have mean  $\widehat{f}(S)$  gives the claim.

Thus, for example, one may come up with a PAC learning algorithm for functions that are concentrated on degrees up to k, which has  $\mathsf{poly}(n^k, 1/\varepsilon, \log(1/\delta))$  queries (check that!). This running time is not very impressive however, so one is often led to consider stronger learning algorithms.

## 2 Learning using membership queries

The membership query model is a vast strengthening of the PAC learning model (and in so is less "realistic"). Here, one again wishes to learn a function f from a concept class C. The difference is that the learner is allowed to choose any point  $x \in \{-1,1\}^n$ , and upon doing so it gets the value f(x).

As before, there are proper and improper learners, and the main complexity measures of a learner are again the precision parameter  $\varepsilon$ , the confidence parameter  $\delta$  and the query complexity as well as running time of the algorithm (which often times are the same) and are denoted by q and t respectively.

It turns out that using membership queries, one may approximate significantly more complex expressions involving Fourier coefficients. An important example is given by the following claim.

**Claim 2.1.** For all  $\varepsilon, \delta > 0$ , there is  $q = O\left(\frac{\log(1/\delta)}{\varepsilon^2}\right)$  and an algorithm performing the following task. Given membership queries to  $f: \{-1,1\}^n \to [-1,1]$ , and sets  $T \subseteq J \subseteq [n]$ , the algorithm outputs a number  $b_{T,J}$  such that

$$\Pr\left[ \ b_{T,J} - \sum_{S: S \cap J = T} \widehat{f}(S)^2 \ \geqslant \varepsilon \right] \leqslant \delta.$$

*Proof.* We recall from the last lecture that

$$\sum_{S:S\cap J=T} \widehat{f}(S)^2 = \mathbb{E}_{z\in\{-1,1\}^{\bar{J}}} \left[ \widehat{f_{\bar{J}\to z}}(T)^2 \right] = \mathbb{E}_{z\in\{-1,1\}^{\bar{J}}} \left[ \mathbb{E}_{x\in\{-1,1\}^{\bar{J}}} \left[ f(z,x)\chi_T(x) \right]^2 \right]$$

$$= \mathbb{E}_{\substack{z\in\{-1,1\}^{\bar{J}}\\ x,y\in\{-1,1\}^{\bar{J}}}} \left[ f(z,x)\chi_T(x)f(z,y)\chi_T(y) \right].$$

Thus, we now have an algorithm: we sample  $z^i \in \{-1,1\}^{\bar{J}}$ ,  $x^i,y^i \in \{-1,1\}^J$  for  $i=1,\ldots,q$  independently, calculate  $A_i=f(z^i,x^i)\chi_T(x^i)f(z^i,y^i)\chi_T(y^i)$ , and output  $\frac{1}{q}\sum_{i=1}^q A_i$ . The result now follows from Chernoff's bound.

# 3 Learning sparse functions using membership queries

Recall that  $g \colon \{-1,1\}^n \to \mathbb{R}$  is said to be t-sparse if its Fourier spectrum is supported on at most t characters, and  $f \colon \{-1,1\}^n \to \{-1,1\}$  is said to be  $(t,\varepsilon)$  sparse if there is a t-sparse function g such that  $\|f-g\|_2^2 \leqslant \varepsilon$ . Our main goal is to prove the following result.

**Theorem 3.1.** For all  $t, \varepsilon, \delta > 0$  there exists an algorithm whose runtime is  $poly(n, t, 1/\varepsilon, 1/\delta)$  such that the following holds. Given an oracle access to a  $(t, \varepsilon)$ -sparse function  $f: \{-1, 1\}^n \to \{-1, 1\}$ , the algorithm produces an hypothesis function  $H: \{-1, 1\}^n \to \{-1, 1\}$  such that  $||f - H||_2^2 \le 4\varepsilon + \delta$ .

*Proof.* The proof has several steps.

Heavy coefficients are what matters. Let  $\xi = \frac{\delta}{8t}$ , and let g be the t-sparse function close to f. Let  $\mathcal{S}$  be the set of characters such that  $\widehat{f}(S) \geqslant \sqrt{\xi}$ . Then

$$\sum_{S \notin \mathcal{S}} \widehat{f}(S)^2 = \sum_{S \notin \mathcal{S}} (\widehat{f}(S) - \widehat{g}(S))^2 \mathbf{1}_{\widehat{g}(S) = 0} + \widehat{f}(S)^2 \mathbf{1}_{\widehat{g}(S) \neq 0} \leqslant \|f - g\|_2^2 + t\xi^2 \leqslant \varepsilon + \frac{\delta}{8},$$

so all but  $\varepsilon + \frac{\delta}{8}$  of the mass of f lies in  $\mathcal{S}$ . Our goal will be to find a set L containing  $\mathcal{S}$ , and then approximate  $\widehat{f}(S)$  for each  $S \in L$  within a small error, say by a number  $a_S$ . Once we do that our hypothesis function will be  $h(x) = \sum_S a_S \chi_S(x)$ , and if we want a Boolean function we will take H(x) = sign(h(x)).

Note that  $|S| \le 1/\xi^2$ ; our set L may be slightly larger, but its size will be of the same order of magnitude

**Locating the heavy coefficients.** Our algorithm will work in steps. At each step k, we will keep a set of live subsets of [k], which are subsets  $A \subseteq [k]$  such that we suspect

$$\sum_{S:S\cap[k]=A}\widehat{f}(S)^2$$

to be larger than  $\xi^2$ . Note that:

- at each step, we expect there to be at most  $O(1/\xi^2)$  such subsets A, since all of these sums together sum up to  $\sum_{S} \widehat{f}(S)^2 = \|f\|_2^2 = 1$ ;
- if there is a coefficient S in S such that  $S \cap [k] = A$ , then we expect A to be alive.

Thus, we design the following algorithm. It will use an estimator to the above sum as a black-box. Throughout the algorithm, we maintain k, starting with k=0 as well as a list L of live subsets of [k], starting with  $L=\{\emptyset\}$ 

- 1. For each  $A \in L$ , using the algorithm from Claim 2.1:
  - (a) Estimate  $\sum_{S:S\cap[k+1]=A}\widehat{f}(S)^2$  within precision  $\xi/10$  and certainty  $\frac{\delta\xi^2}{n}$ , and if it is larger than  $\xi/2$ , add A to L'.
  - (b) Estimate  $\sum_{S:S\cap[k+1]=A\cup\{k+1\}}\widehat{f}(S)^2$  within precision  $\xi/2$  and certainty  $\frac{\delta\xi^2}{n}$ , and i it is larger than  $\xi/10$ , add  $A\cup\{k+1\}$  to L'.
- 2. Set  $L \leftarrow L'$ ; if k = n, halt, otherwise  $k \leftarrow k + 1$  and go to step 2.

We first argue that with probability 1-o(1), this algorithm terminates with  $L\supseteq \mathcal{S}$  such that  $|L|=O(1/\xi^2)$ . Indeed, by induction on k starting with k=0, for each  $S\in \mathcal{S}$  the probability that  $S\cap [k]\not\in L$  is at most  $\frac{\delta \xi^2}{n}$  (since the sum corresponding to  $A=S\cap [k]$  is at least  $\widehat{f}(S)^2\geqslant \xi^2$ , and the parameters of the approximator). Thus, by the union bound the probability that  $S\cap [k]$  will not be in L for some k is at most  $\delta \xi^2$ , by a union bound over  $\mathcal{S}$  the probability that there is  $S\in \mathcal{S}$  and k such that  $S\cap [k]\not\in L$  is at most  $\delta$ . Thus, with probability  $1-\delta$  we have  $\mathcal{S}\subseteq L$ .

By similar arguments, with probability  $1 - O(\delta)$  we have  $|L| \leq O(1/\xi^2)$  at each point of the algorithm, so the running time is at most  $O(n/\xi^2)$  times the running time of the approximator, hence  $\operatorname{poly}(n,t,1/\varepsilon,1/\delta)$  in total.

Finishing the proof. Assume that the algorithm terminated with  $L \supseteq \mathcal{S}$  with size  $R \leqslant O(1/\xi^2)$ . By the algorithm from Claim 1.2, we may estimate  $\widehat{f}(S)$  for each  $S \in L$  with in precision  $\frac{\delta}{8R}$  and probability of error at most  $\delta/R$ . Thus, by the union bound we get numbers  $(a_S)_{S \in L}$  such that  $a_S - \widehat{f}(S) \leqslant \sqrt{\frac{\delta}{8R}}$  for

all  $S \in L$  with probability at least  $1 - \delta$ . Define the function  $h(x) = \sum_{S \subseteq [n]} a_S \chi_S(x)$ , and then  $H(x) = \operatorname{sign}(h(x))$ . Then

$$||f - H||_2^2 \leqslant 4||f - h||_2^2 = 4\left(\sum_{S \in L} (\widehat{f}(S) - \widehat{h}(S))^2 + \sum_{S \notin L} \widehat{f}(S)^2\right) \leqslant 4|L|\frac{\delta}{8R} + 4\sum_{S \notin S} \widehat{f}(S)^2$$
$$\leqslant \frac{\delta}{2} + 4\left(\varepsilon + \frac{\delta}{8}\right) = 4\varepsilon + \delta.$$

The first inequality holds since  $|f(x) - H(x)| \le 2|f(x) - h(x)|$  for all x, since if  $f(x) \ne H(x)$ , then this difference is 2 in absolute value and f(x), h(x) have different signs so the second different is at least 1 in absolute value.

**Remark 3.2.** This algorithm has its origin from the field of cryptography, where it is known as the Goldreich-Levin hardcore bit. This algorithm has several interesting extensions to other settings.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 4

#### Dor Minzer

In this lecture, we will define influences of Boolean functions, and give several important interpretations of them.

# 1 Motivation: Boolean functions as voting rules

Suppose a Boolean function  $f: \{0,1\}^n \to \{0,1\}$  is thought of as an aggregation rule for a certain vote. Namely, we have n voters that are supposed to decide between two options, 0 and 1. The input to the function is the vector of opinions x of the voters, wherein  $x_i$  denotes the opinion of the ith voter. The output of the function, f(x), then stands for the outcome of the vote.

In light of this view, a few natural functions come to mind, as well as the names we associate them with.

- 1. Dictatorship, i.e. a function  $f: \{0,1\}^n \to \{0,1\}$  of the form  $f(x) = x_1$ . Here, only the vote of the first participant counts.
- 2. Majority, i.e. the function  $f: \{0,1\}^n \to \{0,1\}$  defined as  $f(x) = 1_{x_1+\ldots+x_n>n/2}$ .
- 3. Juntas. Here, we have a small set of participants,  $J \subseteq [n]$ , and some  $g \colon \{0,1\}^J \to \{0,1\}$ , and our function f is defined as  $f(x) = g(x_J)$ . Here, only the votes of the participants from the set J count. In this context, J is thought of as a small set, hence the name "junta" makes sense.

Equipped with this intuition, one may try to define parameters of Boolean functions in order to decide which type of voting rules are more "fair" <sup>1</sup>, or more modestly to understand their features in a more precise sense.

For the following discussion, we will assume the distribution of the vote of each player is distributed uniformly and independently of the others (which is of course, not realistic, but nevermind), so that the distribution of x is uniform over  $\{-1,1\}^n$ . How much did the vote of participant i "mattered"?

**Definition 1.1.** For a function  $f: \{-1,1\}^n \to \{0,1\}$  and a coordinate  $i \in [n]$ , the influence of i is defined as

$$I_i[f] = \Pr_{x \in \{-1,1\}^n} [f(x) \neq f(x^{\oplus i})].$$

Here,  $x^{\oplus}$  is the vector x in which the *i*th coordinate has been flipped.

Let's examine influences in the above examples. For dictatorship, one clearly has  $I_1[f] = 1$ , whereas  $I_i[f] = 0$  for all  $i \neq 1$ , so influences capture well the intuition we intended. Analyzing the majority function is more challenging, but the symmetry clearly implies that all influences are the same, and a direct calculation shows that they are all of the order  $1/\sqrt{n}$ . For the junta example, one easily sees that  $I_j[f] = 0$  for all  $j \notin J$ , so the intuition is again captured well.

<sup>&</sup>lt;sup>1</sup>In this course, we will not attempt to give an answer to the (difficult) question of what qualifies as "fair".

**Definition 1.2.** For a function  $f: \{-1,1\}^n \to \{0,1\}$ , the total influence of f is defined as

$$I[f] = \sum_{i=1}^{n} I_i[f].$$

The total influence of the function is one of the most important parameters associated with a Boolean function, and in this lecture we will see some of its basic interpretations and properties.

# 2 Generalizing the notion of influences

The notion of influences may be generalized to arbitrary real valued functions in the following way.

**Definition 2.1** (Discrete derivatives). Given a function  $f: \{-1,1\}^n \to \mathbb{R}$  and  $i \in [n]$ , the discrete derivative of f along i is a function  $\partial_i f: \{-1,1\}^{n-1} \to \mathbb{R}$  defined as

$$\partial_i f(y) = \frac{1}{2} (f(x_i = 1, x_{-i} = y) - f(x_i = -1, x_{-i} = y)).$$

**Definition 2.2.** Given a function  $f: \{-1,1\}^n \to \mathbb{R}$  and  $i \in [n]$ , the  $L^2$  influence of i on f is defined as  $I_i[f] = \|\partial_i f\|_2^2$ . The total  $L^2$  influence of f is  $I[f] = \sum_{i=1}^n I_i[f]$ .

It is instructive to check that the two definitions of influences coincide for  $\{0,1\}$  valued functions up to a factor of 4.

In the rest of this lecture, we will develop Fourier analytic formulas for derivatives, influences and derive the basic isoperimetric inequality for Boolean functions (also known as Poincaré's inequality). We will then spend some time dwelling on these and give more interpretations to the total influence of a function.

#### 3 A combinatorial view of the total influence

The total influence has the following important combinatorial interpretation. Consider the graph whose vertices are  $\{-1,1\}^n$ , and two vertices are connected by an edge if they differ in exactly one coordinate. Thus, a Boolean function  $f: \{-1,1\}^n \to \{1,-1\}$  can be identified with the subset of vertices  $F = \{x \in \{-1,1\}^n \mid f(x) = -1\}$ .

For  $x \in \{-1,1\}^n$ , let  $s_f(x)$  be the number of edges adjacent to x that cross the bi-partition  $(F,\bar{F})$ , i.e. the number of  $i \in [n]$  such that  $f(x) \neq f(x \cdot e_i)$ . The quantity  $s_f(x)$  often goes by the name of "the sensitivity of f at x" in the literature.

**Claim 3.1.** If  $f: \{-1,1\}^n \to \{-1,1\}$ , then  $I[f] = \mathbb{E}_x[s_f(x)]$ .

*Proof.* For  $x \in \{-1, 1\}^n$  and  $i \in [n]$ , denote by  $Z_{i,x}$  the random variable which is 1 if and only if  $f(x) \neq f(x^{\oplus i})$ . Then  $s_f(x) = \sum_{i=1}^n Z_{i,x}$ , and so by linearity of expectation

$$\mathbb{E}_{x}[s_{f}(x)] = \mathbb{E}_{x}\left[\sum_{i=1}^{n} Z_{i,x}\right] = \sum_{i=1}^{n} \mathbb{E}_{x}[Z_{i,x}].$$

The proof is now concluded by noting that  $\mathbb{E}_x[Z_{i,x}] = I_i[f]$ .

Thus, the total influence of f also clearly deserves the name average sensitivity.

#### 4 Sharp thresholds and the total influence

Let  $f: \{0,1\}^n \to \{0,1\}$  be a monotone function, i.e. if  $x_i \leqslant y_i$  for all i, then  $f(x) \leqslant f(y)$ . For example, one can think of  $n = \binom{N}{2}$  and as the input as specifying the adjacency matrix of some graph on N vertices. In this case, the function f could be any monotone graph property, such as (1) being connected, (2) containing a clique of size  $\log N$ , (3) containing at least  $\log n$  triangles etc. For such properties, it is often known that they exhibit a sharp threshold.

It turns out that understanding the total influence of function is often useful to shed further light on such questions. Towards this end, we define the p-biased distribution over  $\{0,1\}^n$ , denoted by  $\mu_p^{\otimes n}$ , as: for each  $i \in [n]$ , sample  $x_i = 1$  with probability p, and otherwise set  $x_i = 0$ . The quantity we wish to study is thus  $\mu_p(f) = \mathbb{E}_{x \sim \mu_p^{\otimes n}}[f(x)]$ , and in particular the way this quantity varies when we increase p. Towards this end, the p-biased analogs of influences as well as the total influence can be defined in the natural way:

$$I_i[f; \mu_p^{\otimes n}] = \underset{x \sim \mu_p^{\otimes n}}{\mathbb{E}} \left[ |\partial_i f(x)|^2 \right], \qquad I[f; \mu_p^{\otimes n}] = \sum_{i=1}^n I_i[f; \mu_p^{\otimes n}].$$

We have the following basic result, asserting that large total influence implies a sharp threshold.

**Lemma 4.1** (Russo-Margulis). Let  $f: \{0,1\}^n \to \{0,1\}$  be a monotone function. Then

$$\frac{d}{dp}\mu_p(f) = I[f; \mu_p^{\otimes n}].$$

*Proof.* Take  $\varepsilon$  to be very small, and let us sample (x,y) in a coupled way so that marginally  $x \sim \mu_p^{\otimes n}$ ,  $y \sim \mu_{p+\varepsilon}^{\otimes n}$  and  $x \leqslant y$  always. This can be done by sampling  $x \sim \mu_p^{\otimes n}$ , and then for each i, if  $x_i = 1$  take  $y_i = 1$ , and if  $x_i = 0$  take  $y_i = 1$  with probability  $\varepsilon/(1-p)$ .

Ther

$$\mu_{p+\varepsilon}(f) - \mu_p(f) = \mathbb{E}_{(x,y)}[f(x) - f(y)] = \mathbb{E}_{(x,y)}[(f(x) - f(y))1_{x \neq y}].$$

Note that the probability that x and y differ in more than a single coordinate is at most  $n^2 \varepsilon^2$ , so

$$\mu_{p+\varepsilon}(f) - \mu_p(f) - \sum_{i=1}^n \mathbb{E}_{(x,y)} \left[ (f(x) - f(y)) \mathbb{1}_{x \text{ and } y \text{ differ only at } i} \right] \leqslant n^2 \varepsilon^2$$

Observe that

$$\underset{(x,y)}{\mathbb{E}}\left[(f(x)-f(y))1_{x \text{ and } y \text{ differ only at } i}\right] = \left(\varepsilon - \Pr\left[x \text{ and } y \text{ differ in at least two coordinates}\right]\right)I_i[f;\mu_p^{\otimes n}],$$

so we get

$$\mu_{p+\varepsilon}(f) - \mu_p(f) - \sum_{i=1}^n \varepsilon I_i[f; \mu_p^{\otimes n}] \leqslant n^2 \varepsilon^2 + n^3 \varepsilon^2.$$

Dividing by  $\varepsilon$  and sending it to 0 gives the result.

**Remark 4.2.** There are arguably simpler proofs in the literature, but we give this one since we think it nicely highlights the intuition behind.

<sup>&</sup>lt;sup>2</sup>That is, looking at the Erdos Reyni graph model, there is a critical edge density p such that below it the property holds with probability o(1), whereas above it the property holds with probability 1 - o(1).

# 5 Fourier analytic formulas for derivatives and influences

**Claim 5.1.** For a function  $f: \{-1,1\}^n \to \mathbb{R}$  and  $i \in [n]$ , we have that

$$\partial_i f(y) = \sum_{S \ni i} \widehat{f}(S) \chi_{S \setminus \{i\}}(y)$$

Proof. By definition,

$$\partial_i f(y) = \frac{1}{2} (f(x_i = 1, y) - f(x_i = -1, y)) = \frac{1}{2} \sum_{S} \widehat{f}(S) (\chi_S(x_i = 1, y) - \chi_S(x_i = -1, y)).$$

Note that if  $i \notin S$ , then  $\chi_S(x_i = 1, y) = \chi_S(x_i = -1, y)$  and these terms cancel. Otherwise, if  $i \in S$ , then  $\chi_S(x_i = 1, y) = \chi_{S \setminus \{i\}}(y)$  and  $\chi_S(x_i = -1, y) = -\chi_{S \setminus \{i\}}(y)$ . Therefore, we get that

$$\partial_i f(y) = \frac{1}{2} \sum_S \widehat{f}(S)(\chi_S(x_i = 1, y) - \chi_S(x_i = -1, y)) = \sum_S \widehat{f}(S)\chi_S(y).$$

In particular, we see that if f has degree at most d, then  $\partial_i f$  has degree at most d-1.

Corollary 5.2. 
$$I_i[f] = \sum_{S \ni i} \widehat{f}(S)^2$$
.

*Proof.* As  $I_i[f] = \|\partial_i f\|_2^2$ , the corollary follows from the last claim and Parseval.

Corollary 5.3. 
$$I[f] = \sum\limits_{S} |S| \, \widehat{f}(S)^2$$
.

Proof. By definition and Corollary 5.2,

$$I[f] = \sum_{i=1}^{n} I_i[f] = \sum_{i=1}^{n} \sum_{S \ni i} \widehat{f}(S)^2 = \sum_{S} |S| \, \widehat{f}(S)^2.$$

Though nearly trivial, the last statement gives us an important interpretation of the total influence of a function. Note that the degree of a character  $\chi_S$  is just |S|, and we can think of the square of the coefficients  $\widehat{f}(S)^2$  as a distribution over characters if f is  $\pm 1$  valued. Thus, the above formula asserts that I[f] can be thought of, in a sense, as the average degree of f, according to these weights. This relaxation of the notion is degree is a very important one, and in the upcoming lectures we will be interested in characterizing functions with low average degree (which will later play important roles in several applications).

An immediate implication of the previous corollary is the so-called Poincaré inequality.

**Corollary 5.4** (Poincaré inequality). For any  $f: \{-1,1\}^n \to \mathbb{R}$  we have that  $I[f] \geqslant \mathsf{var}(f)$ .

*Proof.* This is immediate by the Fourier analytic formulas for var(f) and I[f].

Poincaré's inequality holds for general real-valued functions, and an interesting question is if it can be improved for Boolean functions. It is a nice exercise to check for which Boolean functions one has the equality I[f] = var(f), and later on in the course we will see several improvements of this result.

One immediate consequence of Poincaré inequality, is that if  $f: \{-1,1\}^n \to \{-1,1\}$  is balanced, i.e. if  $\mathbb{E}[f] = 0$ , then there is i such that  $I_i[f] \geqslant \frac{1}{n}$ . Is there such function f such that  $I_i[f] = \frac{1}{n}$ ? This would be desirable in the sense of voting, since intuitively we would like to minimize the individual influence of each one of the participants.

A landmark result in the area, which we will prove in a couple of lectures, asserts that this is impossible. In fact, there is always a coordinate whose influence beats 1/n substantially.

**Theorem 5.5** (KKL theorem). There is an absolute constant c>0, such that for any  $f:\{-1,1\}^n\{-1,1\}$ , there is  $i\in[n]$  such that  $I_i[f]\geqslant c\frac{\log n}{n}\mathrm{var}(f)$ .

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 5

#### Dor Minzer

In this lecture, we will discuss one of the most important tools in analysis of Boolean functions, known as the hypercontractive inequality. In essence, the inequality tells us useful information about the behaviour of the values of low-degree real-valued functions on the hypercube.

**Definition 0.1.** For any  $p \ge 1$  we define the  $L^p$  norm of  $f: \{-1,1\}^n \to \mathbb{R}$  as

$$||f||_p = \left( \underset{x \sim \{-1,1\}^n}{\mathbb{E}} [|f(x)|^p] \right)^{1/p}.$$

# 1 Motivation – degree 1 functions

To begin the discussion, consider the case of degree 1 functions. That is, suppose we have a function  $f: \{-1,1\}^n \to \mathbb{R}$  of the form  $f(x) = \sum_{i=1}^n a_i x_i$ , where we normalize the coefficients  $a_i$  so that  $\sum_{i=1}^n a_i^2 = 1$ . What can we say about the distribution of f(x)?

Well, by Parseval we clearly have that  $\mathbb{E}_x\left[|f(x)|^2\right]=1$ , but because f has degree 1 we are able to say much more. Roughly speaking, if each one of the coefficients  $a_i$  is small individually, i.e.  $|a_i|\leqslant \varepsilon$  for each i, then the distribution of f(x) is similar to that of a standard Gaussian random variable N(0,1). In particular, we are able to conclude that the moments of f(x) are similar to those of a Gaussian random variable, i.e.  $\mathbb{E}\left[|f(x)|^{2m}\right]\approx (2m-1)!!$ 

If, on the other hand some of the coefficients are large, then we can partition f into H+L, where H is the part of f with large coefficients (which in particular depends only on a few coordinates), and L which is the part of f with low coefficients (which then intuitively behaves like a Gaussian). Using this information, one again may prove moment bounds on f. In particular, a direct computation shows:

**Lemma 1.1.** If 
$$f: \{-1,1\} \to \mathbb{R}$$
 has degree 1, then  $||f||_4 \leqslant \sqrt{3}||f||_2$ . More generally, for any  $q \geqslant 2$ ,  $||f||_q \leqslant \sqrt{q-1}||f||_2$ .

This inequality is good enough for many purposes – for example, it is good enough in order to show that the value of |f(x)| is relatively concentrated around  $||f||_2$ .

# 2 The hypercontractive inequality

The case that f is a higher degree function, even 2, is significantly more complex to understand. In particular, f(x) need not behave like a Gaussian, even if all its coefficients are small in magnitude. Thus, our understanding of the distribution of f(x) is significantly weaker. Yet, we can prove moment bounds for it (and get as a corollary tail bounds and such).

### 2.1 Low-degree function formulation

**Theorem 2.1.** If  $f: \{-1,1\} \to \mathbb{R}$  has degree d, and  $q \ge 2$  then  $||f||_q \le \sqrt{q-1}^d ||f||_2$ .

*Proof.* We will prove the statement for q=4; a similar argument works for all even q (which by itself is good enough for all applications that we'll see). To prove the statement for other q's, one needs a different argument.

The proof proceeds by induction on d and n. The proof for d=0 is trivial, so assume  $d\geqslant 1$ . We may take  $i\in [n]$ , and then write  $x=(y,x_n)$  and  $f(x)=g(y)+x_nh(y)$ , where  $g(y)=\sum\limits_{S\not\ni i}\widehat{f}(S)\chi_S(y)$ , and  $h(y)=\partial_i f(y)$ . Then

$$\mathbb{E}_{x}\left[f(x)^{4}\right] = \mathbb{E}_{y,x_{n}}\left[g(y)^{4} + \binom{4}{1}g(y)^{3}x_{n}h(y) + \binom{4}{2}g(y)^{2}x_{n}^{2}h(y)^{2} + \binom{4}{3}g(y)x_{n}^{3}h(y)^{3} + x_{n}^{4}h(y)^{4}\right].$$

Note that  $x_n^2 = 1$ , and  $x_n = x_n^3$  have expectation 0, so

$$||f||_4^4 = ||g||_4^4 + 6\mathbb{E}_y \left[g(y)^2 h(y)^2\right] + ||h||_4^4.$$

By Cauchy-Schwarz,  $\mathbb{E}_y\left[g(y)^2h(y)^2\right]\leqslant \|g\|_4^2\|h\|_4^2$ , and by the inductive hypothesis  $\|g\|_4\leqslant\sqrt{3}^d\|g\|_2$  and  $\|h\|_4\leqslant\sqrt{3}^{d-1}\|h\|_2$ . Plugging that in we get that

$$\|f\|_4^4 \leqslant 9^d \|g\|_2^4 + 6 \cdot 3^d \|g\|_2^2 \cdot 3^{d-1} \|h\|_2^2 + 9^{d-1} \|h\|_2^4 \leqslant 9^d (\|g\|_2^4 + 2\|g\|_2^2 \|h\|_2^2 + \|h\|_2^4).$$

To finish the proof, note that  $||f||_2^2 = ||g||_2^2 + ||h||_2^2$ , and the right hand side about is just  $9^d$  times the square of  $||f||_2^2$ .

### 2.2 Noise operator formulation

The hypercontractive inequality has yet another useful and equivalent formulation. To state it, we need to introduce the noise operator,  $T_{\rho}$ .

**Definition 2.2.** Let  $x \in \{-1,1\}^n$ , and let  $\rho \in [0,1]$ . The distribution of  $\rho$ -correlated inputs with x, denoted as  $y \sim T_{\rho}x$ , is defined as: for each  $i \in [n]$  independently, set  $y_i = x_i$  with probability  $\rho$ , and otherwise resample  $y_i$  according to the uniform distribution over  $\{-1,1\}$ .

Intuitively, one may think of  $y \sim T_{\rho}x$  as a point obtained after performing a random walk of length  $(1-\rho)n/2$  from x. With this definition in place, we can define the averaging operator  $T_{\rho}$  acting on functions, i.e.  $T_{\rho}: L^2(\{-1,1\}^n) \to L^2(\{-1,1\}^n)$ , as follows: given  $f: \{-1,1\}^n \to \mathbb{R}$ , define

$$T_{\rho}f(x) = \underset{y \sim T_{\rho}x}{\mathbb{E}} [f(y)].$$

The source of the name the "hypercontractive inequality" really lies in this operator. First, one may easily show that for each  $\rho \in [0,1]$ , the operator  $T_{\rho}$  is a contraction – it can only shrink norms. That is, for all  $q \ge 1$ ,  $\|T_{\rho}f\|_q \le \|f\|_q$ . It turns out that in fact a much stronger result holds

**Theorem 2.3** (The hypercontractive inequality). For all  $f: \{-1,1\} \to \mathbb{R}$ ,  $1 \le p \le q$  and  $0 \le \rho \le \sqrt{\frac{p-1}{q-1}}$  it holds that  $\|T_{\rho}f\|_q \le \|f\|_p$ .

We will not include here the proof, and defer the interested reader to Ryan's book. It is a good exercise however to work out the case that q=4 and p=2, and see how to adapt the proof from the previous section to this case. For that, the following claim is useful, showing the effect of  $T_{\rho}$  on the Fourier transform.

**Claim 2.4.** For all  $f: \{-1,1\} \to \mathbb{R}$  and  $\rho \in [0,1]$  we have that

$$T_{\rho}f(x) = \sum_{S \subseteq [n]} \rho^{|S|} \widehat{f}(S) \chi_S(x).$$

*Proof.* Note that as the operator  $T_{\rho}$  is linear, it is enough to show that for each character  $\chi_S$ , it holds that  $(T_{\rho}\chi_S)(x) = \rho^{|S|}\chi_S(x)$ . Indeed, note that

$$(\mathbf{T}_{\rho}\chi_{S})(x) = \underset{y \sim \mathbf{T}_{\rho}x}{\mathbb{E}} \left[\chi_{S}(y)\right] = \underset{y \sim \mathbf{T}_{\rho}x}{\mathbb{E}} \left[\prod_{i \in S} y_{i}\right] = \prod_{i \in S} \underset{y_{i} \sim \mathbf{T}_{\rho}x_{i}}{\mathbb{E}} \left[y_{i}\right],$$

where the last transition is by independence. With probability  $\rho$ , we have  $y_i = x_i$ , and otherwise we resample  $y_i$  uniformly in  $\{-1,1\}$ , in which case the contribution to the expectation is 0 therefore,  $\mathbb{E}_{y_i \sim T_\rho x_i}[y_i] = \rho x_i$ , and plugging it above finishes the proof.

# 3 Hypercontractivity – basic applications

We begin by showing a few simple yet instructive applications of the hypercontractive inequality. In the next lecture we will see more substantial ones.

### 3.1 Small Set Expansion

**Definition 3.1** (Noisy hypercube). For  $\rho \in [0,1]$ , the  $\rho$ -noisy hypercube graph is the graph on the vertex set  $\{-1,1\}^n$ , whose edges are sampled according to the  $T_\rho$  process. Namely, the distribution over the neighbours of a given vertex  $x \in \{-1,1\}^n$  is given by  $T_\rho x$ .

**Definition 3.2** (Edge expansion). Let G = (V, E, w) be a weighted regular graph, and let  $S \subseteq V$  be a vertex set. The expansion of S is defined as

$$\Phi_G(S) = \Pr_{x \in S, y \sim_w N(x)} [y \notin S].$$

Expander graphs, that play important role in discrete mathematics, are graphs G in which  $\Phi_G(S) \geqslant c$  for all subsets S containing at most half of the vertices of G, where c is some absolute constant. Intuitively, the larger c is the better the expansion and mixing of the graph is; however, since this is a requirement for all  $|S| \leqslant |V|/2$ , it is easily seen that one cannot hope to get c that is close to 1.

For this purpose, one sometimes considers the notion of small set expansion. Here, the point is that one may require that the expansion of sets much smaller than n/2 have expansion close to 1.

**Definition 3.3.** A graph G = (V, E, w) is called an  $(\varepsilon, \delta)$ -small set expander if for any  $S \subseteq V$  of size at most  $\delta n$ , it holds that  $\Phi_G(S) \geqslant 1 - \varepsilon$ .

Informally, when we say a graph is a small set expander, what we really mean is that we (often implicitly) have in mind a sequence of graphs  $(G_n)_{n\in\mathbb{N}}$ , such that for every  $\varepsilon>0$  there is  $\delta>0$  such that for large enough n,  $G_n$  is an  $(\varepsilon,\delta)$ -small set expander.

**Claim 3.4.** For  $\rho = \frac{1}{\sqrt{3}}$ , the noisy hypercube graph is a small-set expander.

*Proof.* Fix  $\delta > 0$ , and let  $S \subseteq \{-1,1\}^n$  be a set of vertices of size at most  $\delta 2^n$ . Let  $f = 1_S$  be the indicator set of S. Note that

$$\langle 1_S, T_\rho 1_S \rangle = \Pr_{\substack{x \sim \{-1,1\}^n \\ y \sim T_\rho x}} [x \in S, y \in S],$$

so

$$\frac{1}{\mu(S)}\langle 1_S, T_\rho 1_S \rangle = \Pr_{\substack{x \sim S \\ y \sim T_\rho x}} [y \in S] = 1 - \Phi_G(S).$$

Thus, so show that  $\Phi_G(S)$  is close to 1, we must upper bound the left hand side. For that, we use a useful Hölder-inequality trick:

$$\frac{1}{\mu(S)}\langle 1_S, T_\rho 1_S \rangle \leqslant \frac{1}{\mu(S)} \|1_S\|_{4/3} \|T_\rho 1_S\|_4 = \frac{1}{\mu(S)} \mu(S)^{3/4} \|T_\rho 1_S\|_4 \leqslant \frac{1}{\mu(S)} \mu(S)^{3/4} \|1_S\|_2 = \mu(S)^{1/4},$$

which is at most  $\delta^{1/4}$ . In the penultimate inequality we used hypercontractivity.

**Remark 3.5.** There is nothing special about  $\rho = 1/\sqrt{3}$ , and the noisy hypercube is a small-set expander for any  $\rho$  bounded away from 1. The proof is an easy adaptation of the proof above, and is left to the reader.

## 3.2 A concentration inequality for low-degree functions

One simple application of the hypercontractive inequality is a concentration bound for low-degree functions, which is somewhat similar to Chernoff's inequality for linear functions, and can be seen as a generalization of it for higher degrees.

**Theorem 3.6.** Suppose  $f: \{-1,1\}^n \to \mathbb{R}$  is a function of degree at most d, and let  $t \geqslant 2^d$ . Then

$$\Pr_{x}[|f(x)| \ge t||f||_2] \le e^{-\frac{t^{2/d}}{2}}.$$

*Proof.* Let  $q \ge 2$  be a parameter to be chosen later. We have

$$\Pr_{x}[|f(x)| \ge t||f||_{2}] = \Pr_{x}[|f(x)|^{q} \ge t^{q}||f||_{2}^{q}] \le \frac{\mathbb{E}_{x}[|f(x)|^{q}]}{t^{q}||f||_{2}^{q}} = \frac{||f||_{q}^{q}}{t^{q}||f||_{2}^{q}}.$$

where we used Markov's inequality. By hypercontractivity,  $\|f\|_q \leqslant \sqrt{q-1}^d \|f\|_2$ , so we get that

$$\Pr_{x}[|f(x)| \geqslant t||f||_{2}] \leqslant \frac{\sqrt{q-1}^{dq}||f||_{2}^{q}}{t^{q}||f||_{2}^{q}} = e^{\frac{d}{2}q\log(q-1)-q\log t}.$$

Optimizing, we set  $q = \frac{t^{2/d}}{2}$  and get that

$$\Pr_{x}[|f(x)| \ge t||f||_2] \le e^{-\frac{t^{2/d}}{2}}.$$

**Remark 3.7.** The exponent  $t^{2/d}$  is tight.

### 3.3 An anti-concentration for low-degree functions

On the other hand, one may ask if the value of f(x) is non-trivial with non-trivial probability (as opposed to being 0 almost always, and very rarely huge). The following inequality asserts that this is not the case.

**Theorem 3.8.** Suppose  $f: \{-1,1\}^n \to \mathbb{R}$  is a function of degree at most d, and let  $0 < \theta < 1$ . Then

$$\Pr_{x} [|f(x)| \ge \theta ||f||_2] \ge \frac{(1 - \theta^2)^2}{9^d}.$$

Proof. By definition,

$$||f||_2^2 = \mathbb{E}_x \left[ f(x)^2 \right] = \mathbb{E}_x \left[ f(x)^2 1_{|f(x)| \ge \theta ||f||_2} \right] + \mathbb{E}_x \left[ f(x)^2 1_{|f(x)| \le \theta ||f||_2} \right].$$

We upper bound each expectation on the right hand side separately. For the first one, we use Cauchy-Schwarz:

$$\mathbb{E}_{x}\left[f(x)^{2}1_{|f(x)| \geqslant \theta ||f||_{2}}\right] \leqslant \mathbb{E}_{x}\left[f(x)^{4}\right]^{1/2} \mathbb{E}_{x}\left[1_{|f(x)| \geqslant \theta ||f||_{2}}^{2}\right]^{1/2} = ||f||_{4}^{2} \sqrt{\Pr\left[|f(x)| \geqslant \theta ||f||_{2}\right]}.$$

Using hypercontractivity now we get that  $||f||_4 \leqslant \sqrt{3}^d ||f||_2$ , so the second expectation is at most

$$3^{d} ||f||_{2}^{2} \sqrt{\Pr[|f(x)| \geqslant \theta ||f||_{2}]}.$$

For the second expectation, clearly

$$\mathbb{E}_{x} \left[ f(x)^{2} 1_{|f(x)| \ge \theta ||f||_{2}} \right] \le \theta^{2} ||f||_{2}^{2}.$$

Plugging the two estimates above, we get

$$||f||_2^2 \le 3^d ||f||_2^2 \sqrt{\Pr[|f(x)| \ge \theta ||f||_2]} + \theta^2 ||f||_2^2$$

and rearranging yield that  $\Pr[|f(x)| \ge \theta ||f||_2] \ge \frac{(1-\theta^2)^2}{9^d}$ .

### 3.4 The 1-norm trick

Theorem 2.1 tells us that for low-degree functions f, the q-norm of f is comparable to the 2-norm of f. This raises the question of whether one can more generally relate the q-norm of f to the p-norm of f for any  $q > p \geqslant 1$  in this case. If  $p \geqslant 2$ , then  $||f||_2 \leqslant ||f||_p$ , so one gets that for free. It turns out that one can get a result for any  $p \geqslant 1$  using a simple trick.

**Lemma 3.9.** Let  $f: \{-1,1\}^n \to \mathbb{R}$  be a function of degree at most d. Then  $||f||_2 \leqslant 3^d ||f||_1$ .

*Proof.* Note that by Hölder's inequality

$$||f||_{2}^{2} = \mathbb{E}_{x} \left[ |f(x)|^{4/3} |f(x)|^{2/3} \right] \leqslant \mathbb{E}_{x} \left[ |f(x)|^{4} \right]^{1/3} \mathbb{E}_{x} \left[ |f(x)|^{2/3} = ||f||_{4}^{4/3} ||f||_{1}^{2/3}.$$

By Theorem 2.1,  $||f||_4 \leqslant \sqrt{3}^d ||f||_2$ , and plugging that in gives that  $||f||_2^2 \leqslant \sqrt{3}^{4d/3} ||f||_2^{4/3} ||f||_1^{2/3}$ . Rearranging finishes the proof.

#### 3.5 Next lecture

In the next lecture we will show more applications of the hypercontractive inequality.

**Degree** 1 functions that are close to Boolean. Recall that in the HW assignment, you have proved that degree 1 functions that are Boolean can only be dictatorships (or anti-dictatorships). What can one say if a degree 1 function  $f(x) = \sum_{i=1}^{a_i x_i}$  is nearly Boolean, i.e. close to a Boolean function in  $L^2$  distance?

**The Fourier spectrum of small sets.** What can one say regarding the Fourier spectrum of small-sets? Can their indicator function be a low-degree polynomial (or "close" to one)? We will study this question; you are encouraged to think of how would such statement align with the small-set expansion property we have seen in this lecture.

The KKL theorem and the Friedgut Junta theorem. Moving on from low-degree functions, one may ask about the structure of functions that have small average degree, i.e.  $I[f] \le K$  for K thought of as small. What can one prove about such functions? How does it all relate to the study of low-degree functions?

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 6

#### Dor Minzer

In this lecture, we will present more advanced applications of the hypercontractive inequality.

### 1 The FKN theorem

Recall that in the homework assignment, you have seen that degree 1 Boolean functions must be a dictatorship or an anti-dictatorship. The following theorem is a stability-version of that statement, showing that Boolean functions that are close to being degree 1 are close to dictatorships or anti-dictatorships.

**Theorem 1.1.** Suppose a function  $f: \{-1,1\}^n \to \{-1,1\}$  is  $\varepsilon$ -close to a degree 1 function in  $\ell_2^2$ , i.e.  $\|f-f^{=1}\|_2^2 \leqslant \varepsilon$ . Then, there exists  $b_i \in \{-1,1\}$  and  $i \in [n]$  such that  $\|f-b_ix_i\|_2 = O(\varepsilon)$ .

*Proof.* Let  $\ell(x) = f^{-1}(x) = \sum_{i=1}^{n} a_i x_i$ . Expanding, we see that

$$\ell(x)^2 = \sum_{i=1}^n a_i^2 + 2\sum_{i < i} a_i a_j x_i x_j.$$

Therefore,  $\operatorname{var}(\ell^2) = 4\sum_{i < j} a_i^2 a_j^2 = 2\left(\left(\sum_{i=1}^n a_i^2\right)^2 - \sum_{i=1}^n a_i^4\right)$ . We will argue that the variance of  $\ell^2$  is small, and  $\sum_{i=1}^n a_i^2 \approx 1$ , from which the proof will quickly be concluded.

**Bounding** 
$$\sum\limits_{i=1}^n a_i^2$$
. Note that  $\sum\limits_{i=1}^n a_i^2 = \mathbb{E}\left[\ell^2\right] = \mathbb{E}\left[f^2\right] - \mathbb{E}\left[(f-\ell)^2\right] \geqslant 1 - \varepsilon$ .

**Bounding**  $\operatorname{var}(\ell^2)$ . Letting  $h(x) = \ell^2(x) - \mathbb{E}\left[\ell^2\right] = \sum_{i \neq j} a_i a_j x_i x_j$ , we have  $\operatorname{var}(\ell^2) = \|h\|_2^2$ , and our goal is to bound the 2-norm of h. By the 1-norm trick, as h is a degree 2 function  $\|h\|_2 \leqslant 9\|h\|_1$ , and computing

$$||h||_1 \leqslant ||\ell^2 - f^2||_1 + \left|\mathbb{E}\left[\ell^2\right] - 1\right| \leqslant ||\ell - f||_2 ||\ell + f||_2 + \varepsilon \leqslant \sqrt{\varepsilon} 2 + \varepsilon \leqslant 3\sqrt{\varepsilon}.$$

Thus,  $||h||_2 \leqslant 27\sqrt{\varepsilon}$ .

**Finishing the proof.** Staring now at  $var(\ell^2) = \left(\sum_{i=1}^n a_i^2\right)^2 - \sum_{i=1}^n a_i^4$ , we get that

$$(27\sqrt{\varepsilon})^2 \geqslant (1-\varepsilon)^2 - \sum_{i=1}^n a_i^4,$$

so 
$$\sum_{i=1}^{n} a_i^4 \geqslant 1 - O(\varepsilon)$$
. Thus,

$$\max_{i} a_i^2 \sum_{i=1}^n a_i^2 \geqslant 1 - O(\varepsilon),$$

and as  $\sum_{i=1}^{n} a_i^2 \leqslant 1$ , we get  $\max_i a_i^2 \geqslant 1 - O(\varepsilon)$ . This shows that there is  $i^*$  such that  $|a_{i^*}| \geqslant 1 - O(\varepsilon)$ .

Assume without loss of generality that  $a_{i^*} \ge 1 - O(\varepsilon)$ ; we thus get

$$1 - O(\varepsilon) \leqslant a_{i_{\star}} = \widehat{f}(\{i_{\star}\}) = 2\Pr_{x} \left[ f(x) = x_{i_{\star}} \right] - 1,$$

and so 
$$\Pr_x [f(x) = x_{i_{\star}}] \geqslant 1 - O(\varepsilon)$$
.

**Remark 1.2.** An interesting question which is not fully understood asks for extensions of this theorem to degree d functions. Namely, what can one say about a degree d function that is close to Boolean? The question however is more delicate, as the precise notion of closeness depends on d, and we will not elaborate on this further for now.

## 2 The Fourier spectrum of small-sets

Suppose  $S \subseteq \{-1,1\}^n$  is a small set, i.e.  $|S| = \delta 2^n$  for a small  $\delta$ . What can we say about the Fourier spectrum of  $1_S$ ?

Claim 2.1.  $deg(1_S) \geqslant \Omega(\log(1/\delta))$ .

*Proof.* Let d be the degree of  $1_S$ . Then

$$\delta = \|1_S\|_2^2 = \langle 1_S, 1_S \rangle \leqslant \|1_S\|_{4/3} \|1_S\|_4 \leqslant \|1_S\|_{4/3} \sqrt{3}^d \|1_S\|_2 = \sqrt{3}^d \delta^{5/4},$$

so 
$$\sqrt{3}^d \geqslant \delta^{-1/4}$$
, hence  $d \geqslant \frac{1}{4 \log \sqrt{3}} \log(1/\delta)$ .

While this proof is very simple, there is an even simpler argument to prove this statement based on the Schwarz-Zippel argument (which says that a degree d function on the Boolean cube must be non-zero on at least  $2^{-d}$  fraction of the points). However, one can adapt the above argument to say something much stronger: not only is the degree of  $1_S$  must be  $\Omega(\log(1/\delta))$ , but in fact most of its Fourier mass lies on such levels.

For technical reasons, we will prove the following slightly more general statement.

**Lemma 2.2.** Let  $f: \{-1,1\}^n \to \{-1,0,1\}$  be a function such that  $0 < \Pr_x [f(x) \neq 0] \leqslant \delta$ . Then

$$\sum_{|S| \leqslant \frac{1}{20} \log(1/\delta)} \widehat{f}(S)^2 \leqslant \delta^{24/20}.$$

*Proof.* Let  $d=\frac{1}{20}\log(1/\delta)$ . Introducing the notation  $f^{\leqslant d}(x)=\sum\limits_{|S|\leqslant d}\widehat{f}(S)\chi_S(x)$ , our quantity of interest to bound is  $\|f^{\leqslant d}\|_2^2=\sum\limits_{|S|\leqslant d}\widehat{f}(S)^2$ . We do that as follows:

$$\|f^{\leqslant d}\|_2^2 = \langle f^{\leqslant d}, f^{\leqslant d} \rangle = \langle f^{\leqslant d}, f \rangle \leqslant \|f^{\leqslant d}\|_4 \|f\|_{4/3} \leqslant \sqrt{3}^d \|f^{\leqslant d}\|_2 \|f\|_{4/3} \leqslant \sqrt{3}^d \|f\|_2 \|f\|_{4/3}.$$

By the premise  $\|f\|_2 \leqslant \delta^{1/2}$  and  $\|f\|_{4/3} \leqslant \delta^{3/4}$ . We thus get  $\|f^{\leqslant d}\|_2^2 \leqslant e^d \delta^{5/4} \leqslant \delta^{-1/20} \delta^{5/4} \leqslant \delta^{24/20}$ .  $\square$ 

Note that as the overall Fourier mass of f is  $\delta$ , and  $\delta^{24/20} \ll \delta$  for small  $\delta$ , the lemma says that a (signed) indicator of a small set has almost all of its mass on the high-degrees.

**Remark 2.3.** With a bit more effort, one may even show a bound of the form  $\delta^2 \log^d(1/\delta)$ , and for some applications this quantitative difference is important; see homework assignment.

### 3 The KKL theorem

What can we say about Boolean functions that have small average degree, i.e.  $I[f] \leq K \text{var}(f)$ ?

**Theorem 3.1.** Let  $f: \{-1,1\}^n \to \{-1,1\}$  be such that  $I[f] \leqslant K \text{var}(f)$ . Then there exists  $i \in [n]$  such that

$$I_i[f] \geqslant e^{-O(K)}$$
.

**Proof overview.** Before giving the proof, we will give the rough intuition. First, as  $I[f] \leq K \text{var}(f)$  and I[f] is the average degree, a Markov-inequality type bound shows that all but little bit of the Fourier mass of f lies on degrees O(K), and hence it makes sense to consider the low-degree part of f. We will decompose this low-degree part according to the contribution of different coordinates to it (via the derivatives), and then upper bound each one of these contributions separately using the tools we have developed so far. Since the total Fourier mass we have is roughly var(f), the contribution of at least one of these coordinates is meaningful, and that will be the influential coordinate we are looking for.

*Proof.* Suppose towards contradiction that  $I_i[f] \leqslant e^{-C \cdot K} =: \delta$  for all  $i \in [n]$ , where C is an absolute constant to be determined later. Fix i, and consider the function  $g = \partial_i f(x)$ ; note that g is -1, 0, 1 valued, and the probability it is non-zero is  $I_i[f] \leqslant \delta$ , so by Lemma 2.2 we have

$$\sum_{S:|S| \leqslant \frac{1}{20} \log(1/\delta)} \widehat{g}(S)^2 \leqslant I_i[f]^{24/20}.$$

Let us translate this now into information about the Fourier spectrum of f. If  $i \in S$ ,  $\widehat{g}(S) = \widehat{f}(S)$  and otherwise it is 0, so we get that

$$\sum_{\substack{S:|S|\leqslant \frac{1}{20}\log(1/\delta)\\i\in S}} \widehat{f}(S)^2 \leqslant I_i[f]^{24/20}.$$

Summing this over i, we get that

$$\sum_{S: 0 < |S| \leqslant \frac{1}{20} \log(1/\delta)} |S| \, \widehat{f}(S)^2 \leqslant \sum_{i=1}^n I_i[f]^{24/20} \leqslant \delta^{1/5} I[f] \leqslant \delta^{1/5} K \mathrm{var}(f) \leqslant e^{-CK} K \mathrm{var}(f).$$

Therefore,

$$\sum_{S:|S|\leqslant \frac{C}{20}K}\widehat{f}(S)^2\leqslant \delta^{1/5}K\mathrm{var}(f),$$

and on the other hand

$$\sum_{S:|S|>\frac{C}{20}K}\widehat{f}(S)^2\leqslant \frac{\sum\limits_{S:|S|>\frac{C}{20}K}|S|\,\widehat{f}(S)^2}{\frac{C}{20}K}\leqslant \frac{I[f]}{\frac{C}{20}K}\leqslant \frac{20}{C}\mathrm{var}(f).$$

Combining the two inequalities, we get that

$$\sum_{S:0<|S|} \widehat{f}(S)^2 \leqslant \frac{20}{C} \mathrm{var}(f) + e^{-CK} K \mathrm{var}(f) < \mathrm{var}(f),$$

where the last inequality holds for appropriate C (C = 40 will do), and contradiction.

As an immediate corollary, we get a more standard formulation of the KKL theorem.

**Corollary 3.2.** For any 
$$f: \{-1,1\}^n \to \{-1,1\}$$
, there is  $i \in [n]$  such that  $I_i[f] \geqslant \Omega\left(\frac{\log n}{n} \mathsf{var}(f)\right)$ .

*Proof.* Let C>0 be the implicit constant from Theorem 3.1, i.e. absolute C such that  $\max_i I_i[f]\geqslant e^{-C\frac{I[f]}{\text{var}(f)}}$ . If  $I[f]\leqslant \frac{1}{2C}\text{var}(f)\log n$ , we get from Theorem 3.1 that

$$\max_{i} I_{i}[f] \geqslant e^{-\log n/2} = \frac{1}{\sqrt{n}} \geqslant \frac{\log n}{n} \mathsf{var}(f).$$

Otherwise,  $I[f] \geqslant \frac{1}{2C} \text{var}(f) \log n$ , and so

$$\max_{i} I_{i}[f] \geqslant \frac{I[f]}{n} \geqslant \frac{1}{2C} \frac{\log n}{n} \mathsf{var}(f).$$

# 4 Tightness of the KKL theorem

The following example, called the "Tribes" function, shows that the KKL theorem as well as Friedgut's theorem are tight.

**Claim 4.1.** There exists  $f: \{0,1\}^n \to \{0,1\}$  with  $var(f) \geqslant \Omega(1)$  and  $I_i[f] = O(\log n/n)$  for all  $i \in [n]$ .

*Proof.* Take  $k, \ell \in \mathbb{N}$  such that  $\ell k \leq n$ , and take  $I_1, \ldots, I_k \subseteq [n]$  disjoint each of size  $\ell$ . Define the function  $f(x) = \bigvee_{j=1}^k \bigwedge_{i \in I_j} x_i$ . Note that

$$\mathbb{E}[f] = \Pr_{x} [f(x) = 1] = 1 - \Pr_{x} [f(x) = 0] = 1 - \prod_{j=1}^{k} \Pr \left[ \bigwedge_{i \in I_{j}} x_{i} = 0 \right] = 1 - (1 - 2^{-\ell})^{k},$$

so if we take  $k = 2^{\ell}$  we will have that  $\mathbb{E}[f]$  is bounded away from 0 and 1, and hence  $\text{var}(f) \geqslant \Omega(1)$ .

Indeed, we choose  $k=2^{\ell}$ , and then the constraint on  $\ell,k$  turns into  $\ell 2^{\ell} \leqslant n$ , and it is enough to choose  $\ell=|\log n - \log\log n|$ .

We finish the proof by computing the influences of f. Fix i, and assume without loss of generality  $i \in I_1$ . Note that i is influential on x if and only if  $\bigwedge_{q \in I_i} x_q = 0$  for all j > 1, and  $\bigwedge_{q \in I_1 \setminus \{i\}} x_q = 1$ , so

$$\Pr_{x}[f(x) \neq f(x \oplus e_{i})] = \Pr_{x}\left[\bigwedge_{q \in I_{1} \setminus \{i\}} x_{q} = 1\right] \prod_{j=2}^{k} \Pr_{x}\left[\bigwedge_{q \in I_{j}} x_{q} = 0\right] = 2^{\ell-1} (1 - 2^{-\ell})^{k-1} = \Theta(\log n/n).$$

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 7

#### Dor Minzer

Today we will talk about several strengthenings of the KKL-theorem, by Talagrand and Friedgut. We will then discuss isoperimetric inequalities over the hypercube in a broader term, and in particular several results of Talagrand, as well as a conjecture by him which was recently resolved by Eldan and Gross.

Recall that one version of the KKL theorem makes the following assertion.

**Theorem 0.1.** Let  $f: \{-1,1\}^n \to \{-1,1\}$  be a function such that  $I[f] \leqslant K \cdot \text{var}(f)$ . Then there is an  $i \in [n]$  such that  $I_i[f] \geqslant e^{-O(K)}$ .

Can one prove stronger structural results for functions with low total influence? What are the sort of examples you can come up with?

## 1 Talagrand's version of the KKL theorem

The first result we will prove today seeks a strengthening of the KKL theorem, which reads as follows.

**Theorem 1.1** (Talagrand). There exists an absolute constant C > 0, such that for any  $f : \{-1, 1\}^n \to \{-1, 1\}$  it holds that

$$C\sum_{i=1}^{n} \frac{I_i[f]}{\log(1/I_i[f])} \geqslant \operatorname{var}(f).$$

Exercise: show that this is indeed a strengthening of the KKL theorem.

The nice feature of this theorem is that it seems to tall us much more information about the function f than the KKL theorem itself. Namely, in some sense it tells that "on average" the influences have magnitude at least  $e^{-O(K)}$  (as opposed to the largest one being of that magnitude), as i's such that  $I_i[f] \leq e^{-M \cdot K}$  contribute at most  $\operatorname{var}(f)/M$  to the left hand side.

*Proof.* If there is i such that  $I_i[f] \ge 1/10$  there is nothing to prove, so assume otherwise. Write

$$\mathrm{var}(f) = \sum_{S \neq \emptyset} \widehat{f}(S)^2 = \sum_{i=1}^n \sum_{S \ni i} \frac{1}{|S|} \widehat{f}(S)^2 = \sum_{i=1}^n \|g_i\|_2^2,$$

where  $g_i(x) = \sum_{S \ni i} \frac{1}{\sqrt{|S|}} \widehat{f}(S) \chi_S(x)$ . To bound the 2-norm of  $g_i$ , we set  $d_i = \frac{1}{20} \log(1/I_i[f])$  and bound

$$||g_i||_2^2 = \sum_{\substack{S \ni i \\ |S| \leqslant d_i}} \frac{1}{|S|} \widehat{f}(S)^2 + \sum_{\substack{S \ni i \\ |S| > d_i}} \frac{1}{|S|} \widehat{f}(S)^2 \leqslant \sum_{\substack{S \ni i \\ |S| \leqslant d_i}} \widehat{f}(S)^2 + \frac{1}{d_i} \sum_{\substack{S \ni i \\ |S| > d_i}} \widehat{f}(S)^2.$$

For the first sum, we consider the function  $\partial_i f(x)$ , note it is 1, -1, 0 valued and non-zero on  $I_i[f]$  fraction of the inputs, so by Claim 2 in the last lecture the first sum is at most  $I_i[f]^{24/20} = I_i[f]^{6/5}$ . As for the second sum, it is clearly bounded by  $I_i[f]$ , so overall we get that

$$||g_i||_2^2 \le I_i[f]^{6/5} + \frac{I_i[f]}{d_i} \le 40 \frac{I_i[f]}{\log(1/I_i[f])},$$

and the proof is concluded.

## 2 The Friedgut junta theorem

One can hope to strengthen Theorem 0.1 to be a sort of (at least morally speaking) "if and only if" statement. The issue is that the structure Theorem 0.1, while very interesting, is still rather poor and leaves much to be desired. Luckily, for roughly the same effort, one may prove a much stronger statement.

**Theorem 2.1.** Let  $f: \{-1,1\}^n \to \{-1,1\}$ . Then for every  $\varepsilon > 0$ , there exists  $J \subseteq [n]$  of size at most  $2^{O\left(\frac{I[f]}{\operatorname{evar}(f)}\right)}$  and a J-junta  $g: \{-1,1\}^n \to \{-1,1\}$  such that  $\|f-g\|_2 \leqslant \varepsilon$ .

*Proof.* Let C>0 be an absolute constant to be determined later, let  $\delta=2^{-C\frac{I[f]}{\text{evar}(f)}}$  and take

$$J = \{i \mid I_i[f] \geqslant \delta\}.$$

Let  $G(x) = \sum_{\substack{S \subseteq J \\ |S| \leqslant \frac{2I[f]}{2}}} \widehat{f}(S)\chi_S(x)$  and g(x) = sign(G(x)). Clearly, g is a J-junta (why?) and we next bound the

 $|S| \leqslant \frac{2I[J]}{\varepsilon}$  size of J and the  $L^2$  distance between it and f.

**Bounding the size of** J. We have  $I[f] \geqslant |J| 2^{-C \frac{I[f]}{\varepsilon \text{var}(f)}}$ , so  $|J| \leqslant 2^{(C+1) \frac{I[f]}{\varepsilon \text{var}(f)}}$ .

**Bounding the distance between** f and g. We have that  $||f - g||_2 \le 2||f - G||_2$ , and we bound the latter norm.

$$||f - G||_2^2 = \sum_{\substack{S \subseteq J \\ \text{or } |S| > \frac{2I[f]}{\varepsilon}}} \widehat{f}(S)^2 \leqslant \sum_{S \subseteq J, |S| \leqslant \frac{2I[f]}{\varepsilon}} \widehat{f}(S)^2 + \sum_{|S| \geqslant \frac{2I[f]}{\varepsilon}} \widehat{f}(S)^2, \tag{1}$$

and we bound each sum separately. For the second one, we have

$$\sum_{\substack{S|\geqslant \frac{2I[f]}{\varepsilon}}} \widehat{f}(S)^2 \leqslant \frac{\sum_{\substack{|S|\geqslant \frac{2I[f]}{\varepsilon}}} |S| \, \widehat{f}(S)^2}{2I[f]/\varepsilon} \leqslant \frac{I[f]}{2I[f]/\varepsilon} = \frac{\varepsilon}{2}.$$
 (2)

For the first one, we denote  $d = \frac{2I[f]}{\varepsilon}$ . Fix  $i \notin J$ , and  $g = \partial_i f$ . As before, we get that

$$\sum_{|S| \leqslant d, i \in S} \widehat{f}(S)^2 = \sum_{|S| \leqslant d} \widehat{g}(S)^2 \leqslant \sum_{|S| \leqslant \frac{1}{20} \log(1/\delta)} \widehat{g}(S)^2 \leqslant I_i[f]^{24/20}.$$

Here we used the fact that C is large enough so that  $d \leq \log(1/\delta)/20$ . Summing over  $i \notin J$  we get that

$$\sum_{|S| \leqslant d, S \not\subseteq J} \widehat{f}(S)^2 \leqslant \sum_{|S| \leqslant d} \left| S \cap \overline{J} \right| \widehat{f}(S)^2 \leqslant \sum_{i \not\in J} I_i[f]^{24/20} \leqslant \delta^{1/5} I[f] \leqslant \frac{\varepsilon}{2}.$$
(3)

Plugging (2), (3) into (1) finishes the proof.

# 3 Isoperimetric inequalities over the hypercube

The most basic isoperimetric inequality (as well as the weakest) we have seen in this class is Poincare's inequality, stating that  $I[f] \geqslant \text{var}(f)$ . In general, this inequality is tight, but one may want to prover that stronger bounds hold for special classes of functions. One way to go about this goal is to inspect the equality cases, and

see if one can prove stronger versions of it for functions that are "far" from the equality cases. For this purpose, we quickly recall the proof of Poincare's inequality we have seen earlier:

$$I[f] = \sum_{S} |S| \, \widehat{f}(S)^2 \geqslant \sum_{|S| \neq 0} \widehat{f}(S)^2 = \operatorname{var}(f).$$

We see that the equality cases are precisely those functions that have all of their mass on the empty character and the first level. Thus, among Boolean functions  $f: \{-1,1\}^n \to \{-1,1\}$ , the only equality cases are constant functions and dictatorships. In particular, ignoring constant functions, equality cases are achieved by balanced functions, which raises the question of whether there is an improvement of the inequality of highly unbalanced functions. Indeed, such strengthening exists:

**Theorem 3.1** (The edge isoperimetric inequality). For all  $f: \{-1,1\}^n \to \{-1,1\}$  it holds that

$$I[f] \geqslant \Pr[f(x) = -1] \log \left(\frac{1}{\Pr[f(x) = -1]}\right).$$

### 3.1 Other notions of boundary

Recalling the interpretation of I[f] as the edge boundary of the set  $S = \{x \mid f(x) = -1\}$  in the hypercube graph, one may ask about different notions of boundaries. One notion that makes sense is the *vertex-boundary* of a set:  $V - boundary(S) = \{x \mid s_f(x) > 0\}$ . What can one say about it?

How small can it be (majority example; thm: this is best one can do, Kruskal-Katona). Note that in this case however, the edge boundary is much larger than promised by the Poincare inequality. Can it be the case that both the vertex boundary, and the edge boundary be simultaneously small?

**Theorem 3.2** (Margulis). *For all*  $f: \{-1,1\}^n \to \{-1,1\}$ ,

$$\mu(V - \mathsf{boundary}(S))I[f] \geqslant \Omega(\mathsf{var}(f)^2).$$

Thus, this theorem tells us that indeed if the vertex boundary is exceptionally small (e.g. in the majority example, it is  $O(1/\sqrt{n})$ ), it is necessarily the case that the edge boundary must be exceptionally high.

Shortly after establishing this result, Michel Talagrand had been looking into strengthening of this result. He came up with a quantity, that posteriori makes a lot of sense, but wasn't considered by earlier authors. Note that by Cauchy-Schwarz one has that

$$\underset{x}{\mathbb{E}}\left[\sqrt{s_f(x)}\right] = \underset{x}{\mathbb{E}}\left[\sqrt{s_f(x)}1_{s_f(x)>0}\right] \leqslant \sqrt{\underset{x}{\mathbb{E}}\left[s_f(x)\right]}\sqrt{\underset{x}{\Pr}\left[s_f(x)>0\right]} = \sqrt{I[f]\mu(\mathsf{V}-\mathsf{boundary}(S))}.$$

Thus, if it was the case that  $\mathbb{E}_x\left[\sqrt{s_f(x)}\right] \geqslant \Omega(\mathsf{var}(f))$  for all Boolean f's, then one immediately gets Marguli's theorem as a corollary. Indeed, this is Talagrand's theorem.

**Theorem 3.3.** For all  $f: \{-1,1\}^n \to \{-1,1\}$ ,

$$\mathop{\mathbb{E}}_{x}\left[\sqrt{s_f(x)}\right]\geqslant \Omega(\mathsf{var}(f)).$$

Talagrand's proof is a cute inductive proof, which we'll not see (but you are encouraged to look into it, it's really nice).

Talagrand then goes on and seeks a version of Theorem 3.3 which is stronger than the edge isoperimetric inequality (at least up to a constant factor). Indeed, Talagrand is able to prove:

**Theorem 3.4.** For all  $f: \{-1, 1\}^n \to \{-1, 1\}$ ,

$$\mathbb{E}_{x}\left[\sqrt{s_{f}(x)}\right] \geqslant \Omega\left(\operatorname{var}(f)\sqrt{\log\left(\frac{1}{\operatorname{var}(f)}\right)}\right).$$

The proof of this result, once again, is inductive (though much less nice than the previous one).

### 3.2 KKL enters the picture

Recalling equality cases for Poincare's inequality, another way to think of functions "far from equality cases" is as the class of functions that have all individual influences being small. This is, in fact, a larger class than the class of highly unbalanced functions, and one may hope to improve Poincare's inequality for this class. Here, it is interesting to note that we have in fact already seen this improvement, which is nothing but the KKL theorem, stated as:

$$I[f] \geqslant c \min_{i} \log \left(\frac{1}{I_{i}[f]}\right) \mathsf{var}(f)$$

for some absolute constant c > 0. Thus, one gains a large factor provided all influences of f are small.

### 3.3 Mixing everything together

With the same motivation as behind Theorem 3.4, Talagrand seeked to prove an isoperimetric inequality that captures both Theorem 3.3 (and thereby Margulis inequality) and the KKL theorem. He was only partly successful; define a parameter  $M(f) = \sum_{i=1}^{n} I_i[f]^2$ . Talagrand showed that:

**Theorem 3.5.** There exists  $0 < \alpha < 1/2$  such that for all  $f: \{-1,1\}^n \to \{-1,1\}$ ,

$$\underset{x}{\mathbb{E}}\left[\sqrt{s_f(x)}\right] \geqslant \Omega\left(\operatorname{var}(f)\log^{1/2-\alpha}\left(\frac{1}{\operatorname{var}(f)}\right)\log^{\alpha}\left(\frac{1}{M(f)}\right)\right).$$

This result goes some of the way towards a result that encapsulates together Theorem 3.3 and the KKL theorem. For example it is an exercise to show that Theorem 3.5 implies that

$$\max_{i} I_{i}[f] \geqslant e^{-O\left(\left(\frac{I[f]}{\mathsf{var}(f)}\right)^{1/2\alpha}\right)},$$

which for  $\alpha=1/2$  would be KKL, but for  $\alpha<1/2$  is weaker. Talagrand then went on to conjecture that Theorem 3.4 holds for  $\alpha=1/2$ , a conjecture that has only been resolved positively in 2020 by Eldan and Gross. For that, Eldan and Gross use tools from stochastic calculus, which have recently showed up in simultaneously a bunch of places in analysis of TCS (this is a potential topic for a final project).

We will not give the proofs of Theorems 3.3, 3.4, 3.5 today. Later on in the course we will see a recent simpler, unified proof for all of these results that only uses elementary tools.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lectures 8 - 10

#### Dor Minzer

In this lecture, we will introduce the notion of noise stability. We will asymptotically calculate the noise stability of majority, as well as use it to prove Arrow's impossibility theorem from social choice theory.

### 1 Noise stability and noise sensitivity

Consider the voting scheme interpretation we had for Boolean functions, wherein n-voters cast their votes  $x=(x_1,\ldots,x_n)$ , and a function  $f:\{-1,1\}^n\to\{-1,1\}$  is used to aggregate their votes to a final decision. It is often the case that the votes that we get are not the actual votes, but rather a noisy version of them  $y=(y_1,\ldots,y_n)$  (due to errors in the communication channel for example), wherein  $y_i=x_i$  for  $1-\varepsilon$  fraction of the voters, but  $y_i$  may be different for an  $\varepsilon$  fraction of the voter. We would like this noise to be unlikely to affect the final decision, i.e. we would like that f(x)=f(y) with as high probability as possible. What functions satisfy this? Towards this end, we define the notions of noise stability.

**Definition 1.1** (Noise Stability). Let  $f: \{-1,1\}^n \to \mathbb{R}$ , and  $\rho \in [0,1]$ . The stability of f with parameter  $\rho$  is defined as  $\mathsf{Stab}_{\rho}(f) = \langle f, \mathsf{T}_{\rho} f \rangle$ .

For  $\pm 1$  valued functions, we get that

$$\begin{split} \mathsf{Stab}_{\rho}(f) &= \mathop{\mathbb{E}}_{(x,y)\;\rho\;\text{correlated}} \left[ f(x)f(y) \right] = \mathop{\Pr}_{(x,y)\;\rho\;\text{correlated}} \left[ f(x) = f(y) \right] - \mathop{\Pr}_{(x,y)\;\rho\;\text{correlated}} \left[ f(x) \neq f(y) \right] \\ &= 2 \mathop{\Pr}_{(x,y)\;\rho\;\text{correlated}} \left[ f(x) = f(y) \right] - 1, \end{split}$$

so indeed functions with high noise stability are precisely functions for which the noise is the least likely to make change. Let us think for a moment that  $\rho = 1 - \varepsilon$ , and that f is a balanced Boolean function. Among this class of functions, what is the most stable function there is?

Intuitively, the more coordinates f depends on the more likely it is to change its value due to noise. I.e., one may expect that among all balanced Boolean functions, dictators would maximize noise stability, and this is indeed the case. We will establish this fact soon.

How about functions that very much do not look like dictatorships? It turns out that then, majority is the best there is.

**Theorem 1.2.** For all  $\rho > 0$ ,  $\delta > 0$  there is  $\tau > 0$  such that if  $f: \{-1,1\}^n \to \{-1,1\}$  is balanced, and  $I_i[f] \leqslant \tau$  for all  $i \in [n]$ , then

$$\mathsf{Stab}_{\varrho}(f) \leqslant \mathsf{Stab}_{\varrho}(\mathsf{Majority}) + \delta.$$

We will prove this theorem in a few lectures, and see one application for it (which was in fact the original motivation for the formulation of this result) in hardness of approximation. In this lecture and the next one, we shall focus our attention on several more basic applications of stability.

In particular, today we will compute the noise stability of majority asymptotically, which will give us some geometric intuition about the problem and exhibit the relation to Gaussian space that we will elaborate on later on in the course. We will then give an unrelated early application of noise stability in social choice theory, which is Kalai's proof of Arrow's impossibility theorem.

To get started, let's get a Fourier analytic formula for the noise stability of a function.

**Claim 1.3.** Let 
$$f: \{-1,1\}^n \to \mathbb{R}$$
,  $\rho \in [0,1]$ . Then  $\operatorname{\mathsf{Stab}}_{\rho}(f) = \sum_{S} \rho^{|S|} \widehat{f}(S)^2$ .

*Proof.* Plancherel.

Now that we have a Fourier analytic expression for stability and noise sensitivity, we can note that dictators indeed maximize the stability among all balanced functions. Indeed, it follows that  $\mathsf{Stab}_{\rho}(f) \leqslant \rho$ , and equality is achieved if and only if f is degree 1 (in which case f must be a dictatorship).

#### 1.1 The noise stability of Majority

Let  $f(x_1, \ldots, x_n) = \text{Majority}(x_1, \ldots, x_n) = \text{sign}\left(\frac{x_1 + \ldots + x_n}{\sqrt{n}}\right)$ ,  $\rho \in [0, 1]$ . Throughout, we let x, y be sampled according to the  $\rho$ -correlated distribution over  $\{-1, 1\}^n$ , and our goal is to compute  $\mathbb{E}_{x,y}[f(x)f(y)]$ . We shall be somewhat imprecise, as our main goal is to deliver geometric intuition.

**Moving to Gaussians.** Consider the distributions of  $X = \frac{x_1 + \ldots + x_n}{\sqrt{n}}$  and  $Y = \frac{y_1 + \ldots + y_n}{\sqrt{n}}$ . By the central limit theorem, X and Y each convergence in distribution to a standard random variable N(0,1), say  $X \to G_1$ ,  $Y \to G_2$ . By the multi-dimensional version of the CLT, since the covariance of X, Y is

$$\mathbb{E}[XY] = \mathbb{E}\left[\frac{1}{n}\sum_{i=1}^{n}x_{i}y_{i} + \frac{1}{n}\sum_{i\neq j}x_{i}y_{j}\right] = \rho,$$

the covariance of  $G_1, G_2$  is also  $\rho$ . Hence, we get that

$$\lim_{n \to \infty} \underset{x,y}{\mathbb{E}} \left[ f(x) f(y) \right] = \underset{G_1,G_2}{\mathbb{E}} \left[ \operatorname{sign}(G_1) \operatorname{sign}(G_2) \right]$$

The computation in Gaussian space. There is a neat what to compute the last expectation which we next present. How can we generate standard Gaussians  $G_1, G_2$  whose covariance is  $\rho$ ? Well, one way to do so it to take a multi-dimensional standard Gaussian, say  $h \sim N(0, I)$  in  $\mathbb{R}^2$ , take  $u, v \in \mathbb{R}^2$  unit vectors whose inner product is  $\rho$ , and define  $G_1 = \langle u, h \rangle$ ,  $G_2 = \langle v, h \rangle$ . Indeed, it is a standard fact that  $G_1, G_2$  are distributed as Gaussians in this case, and

$$\mathbb{E}\left[G_1G_2\right] = \sum_{i=1}^n u_i v_i h_i^2 + \sum_{i \neq j} u_i v_j h_i h_j = \langle u, v \rangle = \rho.$$

Thus,

$$\underset{G_1,G_2}{\mathbb{E}}\left[\mathsf{sign}(G_1)\mathsf{sign}(G_2)\right] = 1 - 2\Pr\left[\mathsf{sign}(G_1) \neq \mathsf{sign}(G_2)\right] = 1 - 2\Pr_h\left[\mathsf{sign}(\langle u,h\rangle) \neq \mathsf{sign}(\langle v,h\rangle)\right].$$

Let us think of this geometrically now. Consider the normal lines to u and v, call them  $\ell_u$ ,  $\ell_v$ . Note that  $\ell_u$  divides the plane into vectors that give positive inner product with u, and vectors that give negative inner product with u, and the same goes for v. Thus, the region between these lines is precisely the region of vectors that give different signs in these inner products. As the angle between  $\ell_u$  and  $\ell_v$  is the same, the probability a random Gaussian vector falls in this region is  $\frac{2 < \langle u, v \rangle}{2\pi} = \frac{\arccos(\langle u, v \rangle)}{\pi} = \frac{\arccos(\rho_v)}{\pi}$ . Thus, we get that

$$\mathop{\mathbb{E}}_{G_1,G_2}[\mathsf{sign}(G_1)\mathsf{sign}(G_2)] = 1 - \frac{2}{\pi}\mathsf{arccos}(\rho).$$

We thus get:

**Theorem 1.4** (Sheppards Formula).  $\operatorname{Stab}_{\rho}(\operatorname{Majority}_n) = 1 - \frac{2}{\pi}\operatorname{arccos}(\rho) + o(1)$ .

Exercise to think about: does this formula tell you anything about the Fourier weight distribution of Majority? What is  $W^{\geqslant k}[\mathsf{Majroity}]$  asymptotically in k?

### 2 Arrow's impossibility theorem

#### **2.1** Set up

Suppose we have elections between 3 candidates, A, B and C. Each one of n voters must declare their ranking among the 3 candidates. We would like to interpret it as a collection of bits, and thus encode the vote of a participant i as  $x_i, y_i, z_i \in \{-1, 1\}$ , where  $x_i = 1$  if A > B in their eyes (i.e. if they prefer A over B), and otherwise  $x_i = -1$ ;  $y_i = 1$  if B > C, and otherwise  $y_i = -1$ ;  $z_i = 1$  if C > A, and otherwise  $z_i = -1$ . We note that then a vote of a participant is a vector from

$$\{(1,1,-1),(1,-1,1),(-1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)\},$$

as the votes (1,1,1), (-1,-1,-1) do not represent a valid ranking. In other words, these are all of the assignments in the support of NAE<sub>3</sub>:  $\{-1,1\}^3 \to \{0,1\}$  defined as NAE<sub>3</sub> $(a,b,c) = 1 - 1_{a=b=c}$ .

Given the vectors  $x=(x_1,\ldots,x_n),\ y=(y_1,\ldots,y_n),\ z=(z_1,\ldots,z_n)$  that encode the preferences of the votes, we wish to use a function  $f\colon\{-1,1\}^n\to\{-1,1\}$  in order to determine the overall ranking between the 3 candidates. To do that, we will compute f(x) to determine the preference between A and B, and similarly compute f(y) and f(z) to determine the preference between B and C, A and C respectively. We thus get  $(f(x),f(y),f(z))\in\{-1,1\}^3$ , and for that to represent a valid ranking we must have that  $\mathsf{NAE}_3(f(x),f(y),f(z))=1$ . In this case, we say that the elections have a *Condorcet winner*.

Condorcet himself noted that the majority function does not always yield a Condorcet winner, which raises the question of whether there is a voting rule f that avoids such paradoxes.

**Theorem 2.1.** [Arrow's impossibility theorem] Suppose  $f: \{-1,1\}^n \to \{-1,1\}$  is an unanimous voting rule, i.e. such that  $f(\vec{1}) = 1$ ,  $f(-\vec{1}) = -1$ . If in 3-candidate election f always has a Condorcet winner, then f is a dictatorship.

#### 2.2 Preliminary facts

To prove Theorem 2.1, we first need the Fourier expansion of NAE<sub>3</sub>.

**Claim 2.2.** NAE<sub>3</sub>
$$(a, b, c) = \frac{3}{4} - \frac{1}{4}(ab + bc + ac)$$
.

Proof.

$$\begin{split} \mathsf{NAE}_3(a,b,c) &= 1 - \mathsf{Eq}(a,b,c) \\ &= 1 - \frac{(1-a)(1-b)(1-c)}{8} - \frac{(1+a)(1+b)(1+c)}{8} \\ &= 1 - \frac{1-a-b-c+ab+ac+bc-abc}{8} - \frac{1+a+b+c+ab+ac+bc+abc}{8} \\ &= \frac{3}{4} - \frac{1}{4}(ab+bc+ac). \end{split}$$

We also need to extend the definition of  $\rho$ -correlated inputs to negative  $\rho$ 's.

**Definition 2.3.** Let  $-1 \le \rho < 0$ . The distribution of  $\rho$ -correlated inputs is defined as the joint distribution of  $(a,b) \in \{-1,1\}^2$  such that marginally each one of a and b is distributed uniformly, and  $\mathbb{E}[ab] = \rho$ .

An alternative way to define this distribution, more along the lines of our definition of  $\rho \geqslant 0$ , is to say that given a, the distribution of  $\rho$ -correlated inputs with a is the distribution that sampled a  $-\rho$ -correlated input with -a, i.e. with probability  $-\rho$  we take b=-a, and otherwise we resample  $b \in \{-1,1\}$ . It is easy to check that the two definitions coincide.

Just as in the case of  $\rho > 0$ , we can define the averaging operator  $T_{\rho}$  according to the  $\rho$ -correlated distribution, and the stability  $\mathsf{Stab}_{\rho} = \mathbb{E}_{(x,y) \; \rho\text{-correlated}} \left[ f(x) f(y) \right] = \langle f, T_{\rho} f \rangle$ .

#### 2.3 Proof of Theorem 2.1

Let us sample  $(x_i, y_i, z_i) \sim \mathsf{NAE}_3^{-1}(1)$  for each  $i = 1, \ldots, n$  independently. By assumption, we always have that  $\mathsf{NAE}_3(f(x), f(y), f(z)) = 1$ , and we next compute the expectation of it in a different way. Using Claim 2.2,

$$\mathbb{E}_{x,y,z} \left[ \mathsf{NAE}_{3}(f(x), f(y), f(z)) \right] = \mathbb{E}_{x,y,z} \left[ \frac{3}{4} - \frac{1}{4} (f(x)f(y) + f(y)f(z) + f(x)f(z)) \right]$$

$$= \frac{3}{4} - \frac{3}{4} \mathbb{E}_{x,y,z} [f(x)f(y)],$$

where in the last equality we used symmetry. We now inspect the joint distribution of x, y. Clearly,  $(x_i, y_i)$  are independently picked for each i, and inspecting the marginal of each one of  $x_i, y_i$ , we see that they are uniformly distributed. Also,

$$\mathbb{E}[x_i y_i] = \frac{1}{6}(2-4) = -\frac{1}{3},$$

so  $(x_i,y_i)$  is  $\rho$ -correlated with  $\rho=-\frac{1}{3}$ . Thus,  $\mathbb{E}_{x,y,z}\left[f(x)f(y)\right]=\mathsf{Stab}_{-1/3}(f)$ , and we get the identity

$$1 = \mathop{\mathbb{E}}_{x,y,z}[\mathsf{NAE}_3(f(x),f(y),f(z))] = \frac{3}{4} - \frac{3}{4}\mathsf{Stab}_{-1/3}(f).$$

Rearranging, we get that  $\mathsf{Stab}_{-1/3}(f) = -\frac{1}{3}$ . We now use Claim 1.3 to extract from this information about the Fourier spectrum of f. Note that

$$-\frac{1}{3} = \mathsf{Stab}_{-1/3}(f) = \sum_{k=0}^{n} \left(-\frac{1}{3}\right)^{k} W^{=k}[f],$$

and that trivially

$$\sum_{k=0}^{n} \left( -\frac{1}{3} \right)^{k} W^{=k}[f] \geqslant -\frac{1}{3} \sum_{k=0}^{n} W^{=k}[f] = -\frac{1}{3} \|f\|_{2}^{2} = -\frac{1}{3}.$$

Furthermore, unless all of the Fourier weight of f likes on the first level (the only level which is multiplied by (-1/3) and not something larger), this inequality is strict. Thus, we conclude that  $W^{=1}[f] = 1$ , and by the homework exercise f is either a dictatorship or an anti-dictatorship. The unanimity now implies it is a dictatorship, finishing the proof.

#### 2.4 Robust Arrow's theorem

The proof we have just seen is not the original proof of Arrow, and was given by Gil Kalai in 2002. It has the added benefit that it is able to establish a more robust version of the result, that reads as follows.

**Theorem 2.4.** Suppose  $f: \{-1,1\}^n \to \{-1,1\}$  is a voting rule such that the probability of reaching a Condorcet paradox when sampling the votes x, y, z as  $(x_i, y_i, z_i) \sim \mathsf{NAE}_3^{-1}(1)$  for each i independently is at most  $\varepsilon$ . Then, f is  $\varepsilon$ -close to a dictatorship or an anti-dictatorship.

*Proof.* Running Kalai's argument, we get that

$$1-\varepsilon\leqslant\frac{3}{4}-\frac{3}{4}\mathrm{Stab}_{-1/3}(f),$$

and rearranging  $\operatorname{Stab}_{-1/3}(f) + \frac{1}{3} \leqslant \varepsilon$ . Note that

$$\mathsf{Stab}_{-1/3}(f) + \frac{1}{3} = \sum_{k=0}^{\infty} \left( \frac{1}{3} + \left( -\frac{1}{3} \right)^k \right) W^{=k}[f] \geqslant \sum_{k \neq 1} \left( \frac{1}{3} - \frac{1}{27} \right) W^{=k}[f] = \frac{8}{27} \|f - f^{=1}\|_2^2,$$

so we get  $||f - f^{=1}||_2^2 \leqslant \frac{27}{8}\varepsilon$ . The result now follows from the FKN theorem.

### 3 Noise sensitivity

Today we will focus on a notion called noise sensitivity. We will give a characterization of noise sensitive monotone functions due to Bejamini Kalai and Schramm, and en route introduce basic results and techniques such as the level d inequalities and decoupling.

**Definition 3.1** (Noise Sensitivity). Let  $f: \{-1,1\}^n \to \mathbb{R}$ , and  $\varepsilon > 0$ . The noise sensitivity of f with parameter  $\rho$  is defined as  $\mathsf{NS}_{\varepsilon}(f) = \frac{1}{2} - \frac{1}{2}\mathsf{Stab}_{1-2\varepsilon}(f)$ .

For  $\pm 1$  valued functions, we get that  $\mathsf{NS}_{\varepsilon}(f) = \Pr_{\substack{1-2\varepsilon \text{ correlated} \\ 1-2\varepsilon \text{ correlated}}} [f(x) \neq f(y)]$ . Note that if we sample x,y independently, the probability that  $f(x) \neq f(y)$  is  $2\Pr_x[f(x) = -1]\Pr_y[f(y) = 1] = \frac{1}{2}\mathsf{var}(f)$ . Informally, we say that f is noise sensitive if f(x), f(y) behave independently when x,y are sampled in  $(1-2\varepsilon)$ -correlated manner. I.e., we say f is  $(\varepsilon,\xi)$  noise sensitive if  $|\mathsf{NS}_{\varepsilon}(f) - \frac{1}{2}\mathsf{var}(f)| \leqslant \xi$ .

The main question that will concern us today is to characterize functions that are noise sensitive. To gain some intuition into this question, we first give Fourier analytic formula for noise sensitivity.

Claim 3.2. Let 
$$f: \{-1,1\}^n \to \mathbb{R}$$
. Then  $NS_{\varepsilon}(f) = \frac{1}{2} \sum_{S} (1 - (1-2\varepsilon)^{|S|}) \widehat{f}(S)^2$ .

*Proof.* Plug in Claim 1.3 into the definition of  $NS_{\varepsilon}$ .

Note that

$$\frac{1}{2}\mathrm{var}(f) - \mathsf{NS}_{\varepsilon}(f) = \frac{1}{2}\sum_{S \neq \emptyset}((1-2\varepsilon)^{|S|})\widehat{f}(S)^2 = \frac{1}{2}\sum_{k=1}^n(1-2\varepsilon)^kW^{=k}[f].$$

Thus, this quantity is always non-negative. Also, we see that a function f is noise sensitive if and only if almost all of its Fourier weight lies on high levels; for example, if all but  $\delta$  of the Fourier mass lies above level  $T \gg 1/\varepsilon \log(1/\delta)$ , then the above difference is at most  $\delta + (1-2\varepsilon)^T \leq 2\delta$ .

Our question is therefore: which Boolean functions have only negligible weight on the low levels? For general functions, this question is too difficult to answer and one can only give a sufficient condition. For the class of monotone functions, this answer is also a necessary condition.

#### 4 The BKS theorem

To answer this question, we define the parameter  $M(f) = \sum_{i=1}^n I_i[f]^2$ . Before we state the theorem, we make some sense of this parameter. If f is monotone, as you have seen in the homework problem,  $\widehat{f}(\{i\}) = I_i[f]$ , and so  $M(f) = W^{-1}[f]$ . In general however, one only has that  $W^{-1}[f] \leq M(f)$ , and M(f) itself may be very large – for example, it is as large as n for  $f = \prod_{i=1}^n x_i$ .

Nevertheless, it turns out that when M(f) is small, it immediately provides bounds on the weight of the function f on all of the low-levels, as follows.

**Theorem 4.1.** There exists an absolute constant C > 0, such that for all  $k \in \mathbb{N}$ ,

$$W^{=k}[f] \leqslant \left(\frac{C}{k}\right)^k M(f) \log\left(\frac{k}{M(f)}\right)^{k-1}.$$

Most of our effort today will be devoted into proving this theorem. We first show several consequences of it, and in particular use it to show a criteria for noise sensitivity. For  $k \leq \log(1/M(f))$  we get that

$$W^{=k}[f] \leqslant M(f) \left(\frac{C}{k}\right)^k \left(2\log\left(\frac{1}{M(f)}\right)\right)^k \leqslant M(f) \left(\frac{C\log(\frac{1}{M(f)})}{k}\right)^k$$

Inspecting the last expression as a function of k, we see that it is increasing up to  $k = \frac{C}{2} \log(1/M(f))$ , hence for  $k \leq aC \log(1/M(f))$  for small a we get that

$$W^{=k}[f] \leq M(f)a^{-aC\log(1/M(f))} = M(f)e^{a\log(1/a)C\log(1/M(f))},$$

so for small enough absolute constant a we get that  $W^{=k}[f] \leqslant \sqrt{M(f)}$ . We conclude:

**Corollary 4.2.** There exists an absolute constant c > 0, such that for all  $k \le c \log(1/M(f))$  we have that

$$W^{=k}[f] \leqslant \sqrt{M(f)}.$$

**Corollary 4.3.** There exists an absolute constant  $\alpha > 0$  such that for all  $\varepsilon > 0$  and  $f: \{-1,1\}^n \to \{-1,1\}$ ,

$$\left|\frac{1}{2}\mathsf{var}(f) - \mathsf{NS}_{\varepsilon}(f)\right| \leqslant M(f)^{\alpha\varepsilon}.$$

*Proof.* Let c > 0 be from the previous corollary, and let  $T = c \log(1/M(f))$  As seen earlier, the left hand side is equal to

$$\frac{1}{2} \sum_{k=1}^{n} (1 - 2\varepsilon)^{k} W^{=k}[f] \leqslant \frac{1}{2} (W^{\leqslant T}[f - \mathbb{E}[f]] + (1 - 2\varepsilon)^{T}).$$

For the first term, by the previous corollary, we have  $W_{\leqslant T}[f-\mathbb{E}[f]]\leqslant T\sqrt{M(f)}\leqslant M(f)^{\alpha}$  for sufficiently small  $\alpha>0$ . For the second term,  $(1-2\varepsilon)^T\leqslant e^{-2\varepsilon T}=e^{-2\varepsilon c\log(1/M(f))}=M(f)^{2\varepsilon c}\leqslant M(f)^{\varepsilon\alpha}$ . Plugging these two bounds finishes the proof.

Thus, we see that if  $M(f) \leq \xi^{1/(\alpha \varepsilon)}$ , then f is  $(\varepsilon, \xi)$  noise sensitive. For monotone functions, we have a two sided connection.

**Theorem 4.4.** There exists  $\alpha > 0$  such that for all monotone  $f: \{-1,1\}^n \to \{-1,1\}$ 

$$(1-\varepsilon)M(f)\leqslant \left|\frac{1}{2}\mathsf{var}(f)-\mathsf{NS}_{\varepsilon}(f)\right|\leqslant M(f)^{\alpha\varepsilon}.$$

Thus, f is  $(\varepsilon, o(1))$  noise sensitive if and only if M(f) = o(1).

The rest of this lecture is devoted to the proof of Theorem 4.1. For technical reasons, we will prove the following quantitatively weaker statement:

**Theorem 4.5.** There exists an absolute constant C > 0, such that for all  $k \in \mathbb{N}$ ,

$$W^{=k}[f] \leqslant C^k M(f) \log \left(\frac{1}{M(f)}\right)^{k-1}.$$

The proof of this theorem is already fairly technical as is, and getting Theorem 4.1 requires additional effort.

## 5 A first attempt

Inspired by the proof of the KKL theorem and the Friedgut junta theorem, one may hope to divide the level k weight of f according to the contribution of each  $i \in [n]$ , use hypercontractivity and then make a conclusion. This approach almost works, and we will present it anyway since it is illuminating.

#### 5.1 The level k inequalities

Recall that in earlier lectures, we have seen that if  $g: \{-1,1\}^n \to \{-1,0,1\}$  is non-zero with probability at most  $\delta$ , then most of its weight lies above level  $\log(1/\delta)$ . The precise bounds we got there are that  $W^{\leq \log(1/\delta)/20} \leq \delta^{24/20}$ . Below, we improve that for constant levels showing that  $W^{\leq k}[f] \leq \delta^2 \text{polylog}(1/\delta)$ .

**Lemma 5.1.** [Level k inequality] Suppose  $g: \{-1,1\}^n \to \{-1,0,1\}$  is non-zero with probability  $\delta$ , and let  $k \in \mathbb{N}$ . Then

$$W^{\leqslant k}[g] \leqslant \delta^2 (e \log(2/\delta))^k$$
.

*Proof.* Let  $q \in \mathbb{N}$  to be determined later. Note that

$$W^{\leqslant k}[g] = \langle g^{\leqslant k}, g \rangle \leqslant \|g^{\leqslant k}\|_q \|g\|_{q/(q-1)}.$$

By hypercontractivity,

$$||g^{\leqslant k}||_q \leqslant \sqrt{q-1}^k ||g^{\leqslant k}||_2 = \sqrt{q-1}^k \sqrt{W^{\leqslant k}[g]},$$

so rearranging  $W^{\leq k}[g] \leq (q-1)^k \|g\|_{q/(q-1)}^2$ . Also,  $\|g\|_{q/(q-1)} = \delta^{(q-1)/q}$ , so we get the bound

$$W^{\leqslant k}[q] \leqslant (q-1)^k \delta^{2\frac{q-1}{q}}.$$

Choosing  $q = \log(4/\delta)$ , we get

$$W^{\leqslant k}[g] \leqslant (\log(2/\delta))^k \delta^{2 - \frac{1}{\log(4/\delta)}} = (e\log(2/\delta))^k \delta^2$$

**Remark 5.2.** We note the level 0 weight of g is  $\delta^2$ . Lemma 5.1 thus tells us that the level 1 weight of g can only jump multiplicatively by a logarithmic factor, and that this extends to all  $k \in \mathbb{N}$ . As we will see below, this improvement will be essential in our mock BKS theorem, but we remark that there are several other applications of the level k inequality that we will not show in this course in which this improvement is essential.

Armed with Lemms 5.1, we may now attempt to prove the BKS theorem. Note that

$$W^{=k}[f] = \sum_{|S|=k} \widehat{f}(S)^2 = \frac{1}{k} \sum_{i=1}^n \sum_{|S|=k, i \in S} \widehat{f}(S)^2 = \frac{1}{k} \sum_{i=1}^n W^{=k-1}[\partial_i f].$$

The function  $\partial_i f$  gets the valued 0, -1, 1 and is non-zero with probability  $I_i[f]$ . Hence, by Lemma 5.1 we have that  $W^{=k-1}[\partial_i f] \leq 10^k I_i[f]^2 \log^{k-1}(1/I_i[f])$ . Plugging this into the inequality above gives that

$$W^{=k}[f] \le \frac{10^k}{k} \sum_{i=1}^n I_i[f]^2 \log^{k-1}(1/I_i[f]).$$

This is very similar to the bound we want, which is  $C^k \sum_{i=1}^n I_i[f]^2 \log^{k-1}(1/M(f))$ . Alas, it is weaker, and it is not clear how to improve it.

### 6 Proof of Theorem 4.5

In a sense, the main deficiency in the above argument is that the level k inequality has been applied to each one of the derivatives by themselves. This sort of argument assumes that in the worst case, the level k inequality is tight for each one of the derivatives, which cannot be the case.

To utilize this point, the proof of the theorem uses a useful idea (not only in the context of Boolean functions) called decoupling. Let  $k \ge 2$ , and consider the level k weight of f. It would be useful if we could partition [n] into two sets, I and J such that each  $S \subseteq [n]$  of size k in the support of  $\widehat{f}$  would have one variable from I, and k-1 variables from J. This would then be useful, as randomly restricting the coordinates of J, we would reduce the level k weight of the function to the level k weight of the restricted function, which is directly related to influences of the restricted function.

We first need to find such partition I, J of [n]. The condition we are looking for is too strong, and we have to settle for a more modest one:

**Claim 6.1.** There is a partition (I, J) of [n] such that

$$\sum_{\substack{|S|=k\\|S\cap I|=1}} \widehat{f}(S)^2 \geqslant \frac{1}{e} W^{=k}[f].$$

*Proof.* Choose the partition (I, J) randomly by including each  $i \in [n]$  in I with probability 1/k, and otherwise in J.

$$\mathbb{E}_{I,J} \left[ \sum_{\substack{|S|=k\\|S\cap I|=1}} \widehat{f}(S)^2 \right] = \mathbb{E}_{I,J} \left[ \sum_{|S|=k} \widehat{f}(S)^2 1_{|S\cap I|=1} \right] = \sum_{|S|=k} \widehat{f}(S)^2 \mathbb{E}_{I,J} \left[ 1_{|S\cap I|=1} \right].$$

Note that

$$\mathbb{E}_{I,J}\left[1_{|S\cap I|=1}\right] = \Pr\left[|S\cap I| = 1\right] = \binom{k}{1}\frac{1}{k}\left(1 - \frac{1}{k}\right)^{k-1} = \left(1 - \frac{1}{k}\right)^{k-1} \geqslant \frac{1}{e},$$

so the expectation is at least  $\frac{1}{e}W^{=k}[f]$ , and in particular there is a partition (I,J) as desired.

Fix (I, J) as in the claim. For the rest of the proof, we write as input x in the hypercube as x = (y, z), where y is the I-part of x and z is the J-part of x. We now partition the sum on the left hand side of the claim according to which coordinate in I is involved, and for that for each  $i \in I$  we define  $f_i : \{-1, 1\}^J \to \mathbb{R}$  by

$$f_i'(z) = \sum_{T \subseteq J, |T| = k-1} \widehat{f}(T \cup \{i\}) \chi_T(z).$$

Thus,

$$\langle y_i f_i', f \rangle = \sum_{|T|=k-1, T \subset J} \widehat{f}(T \cup \{i\})^2 = ||f_i'||_2^2.$$

It is convenient to normalize  $f'_i$  so that it has 2-norm 1,  $f_i = f'_i / ||f'_i||_2$ , in which case we get

$$\langle y_i f_i, f \rangle^2 = \sum_{|T|=k-1, T \subseteq J} \widehat{f}(T \cup \{i\})^2.$$

Thus,

$$\sum_{\substack{|S|=k\\|S\cap I|=1}} \widehat{f}(S)^2 = \sum_{i\in I} \langle y_i f_i, f \rangle^2,$$

and our goal is to bound each one of the inner products on the right hand side. Write

$$\langle f_i, y_i f \rangle^2 = \underset{y, z}{\mathbb{E}} \left[ f_i(z) y_i f(y, z) \right]^2 = \underset{z}{\mathbb{E}} \left[ f_i(z) \underset{y}{\mathbb{E}} \left[ y_i f(y, z) \right] \right]^2$$
 (1)

The idea is now to use the fact that  $f_i$  is a low-degree function, and hence it behaves as if it is a bounded function. If indeed it was bounded, say by T = O(1), we would be able to say that

$$\langle f_i, y_i f \rangle^2 \leqslant T^2 \mathbb{E} \left[ \left| \mathbb{E} \left[ y_i f(y, z) \right] \right| \right]^2 \leqslant T^2 \mathbb{E} \left[ \left| \mathbb{E} \left[ y_i f(y, z) \right] \right| \right]^2 = T^2 \mathbb{E} \left[ 1_{f(y, z) \neq f(y, z + e_i)} \right]^2 = T^2 I_i[f]^2,$$

which is the sort of bound we are after (summing over i gets  $\leq T^2M(f)$ ).

The situation is of course not as simple, and  $f_i$  is not really a bounded function. To get around this issue, we introduce a threshold parameter T to be determined later and analyze separately cases where  $|f_i(z)| \ge T$  and cases where  $|f_i(z)| \le T$ . First, write

$$(1) \leqslant \underset{z}{\mathbb{E}} \left[ |f_{i}(z)| \left( 1_{|f_{i}(z)| < T} + 1_{|f_{i}(z)| \geqslant T} \right) \left| \underset{y}{\mathbb{E}} \left[ y_{i} f(y, z) \right] \right| \right]^{2}$$

$$\leqslant 2 \underbrace{\underset{z}{\mathbb{E}} \left[ |f_{i}(z)| 1_{|f_{i}(z)| < T} \left| \underset{y}{\mathbb{E}} \left[ y_{i} f(y, z) \right] \right| \right]^{2}}_{(I)} + 2 \underbrace{\underset{z}{\mathbb{E}} \left[ |f_{i}(z)| 1_{|f_{i}(z)| \geqslant T} \left| \underset{y}{\mathbb{E}} \left[ y_{i} f(y, z) \right] \right| \right]^{2}}_{(II)},$$

where we used  $(a+b)^2 \le 2a^2 + 2b^2$ . We may bound the first expression as in the simplistic case by

$$(I) \leqslant 2T^2 \mathbb{E}_z \left[ \left| \mathbb{E}_y \left[ y_i f(y, z) \right] \right| \right]^2 \leqslant 2T^2 I_i[f]^2.$$

As for the second one, using Cauchy-Schwarz we get that

$$(II) \leqslant 2\mathbb{E}_{z} \left[ |f_{i}(z)|^{2} 1_{|f_{i}(z)| \geqslant T} \right] \mathbb{E}_{z} \left[ \left| \mathbb{E}_{y} \left[ y_{i} f(y, z) \right] \right|^{2} \right],$$

and we bound each one of the expectations separately. For the first one, applying Cauchy-Schwarz

$$\underset{z}{\mathbb{E}}\left[\left|f_{i}(z)\right|^{2} 1_{\left|f_{i}(z)\right| \geqslant T}\right] \leqslant \|f_{i}\|_{4}^{2} \sqrt{\Pr\left[\left|f_{i}(z)\right| \geqslant T\right]}.$$

The norm is at most  $3^{k-1} ||f_i||_2^2 = 3^{k-1}$  by hypercontractivity. The probability is at most  $e^{-\frac{1}{2}T^{2/(k-1)}}$  by the tail bound from Lecture 5. For the second expectation, we only note that  $|\mathbb{E}_y[y_i f(y,z)]| = |\widehat{f_{J\to z}}(\{i\})|$ . Therefore,

$$(II) \leqslant 2 \cdot 3^{k-1} e^{-\frac{1}{4}T^{2/(k-1)}} \mathbb{E}_{z} \left[ \left| \widehat{f_{J \to z}}(\{i\}) \right|^{2} \right].$$

Thus,

$$\langle f_i, y_i f \rangle^2 \le 2T^2 I_i[f]^2 + 2 \cdot 3^{k-1} e^{-\frac{1}{4}T^{2/(k-1)}} \mathbb{E}_z \left[ \left| \widehat{f_{J \to z}}(\{i\}) \right|^2 \right],$$

and summing over i gives that

$$\sum_{i \in I} \langle f_i, y_i f \rangle^2 \leqslant 2T^2 M(f) + 2 \cdot 3^{k-1} e^{-\frac{1}{4}T^{2/(k-1)}} \mathbb{E}_z \left[ W^{=1}[f_{J \to z}] \right] \leqslant 2T^2 M(f) + 2 \cdot 3^{k-1} e^{-\frac{1}{4}T^{2/(k-1)}}.$$

We now choose  $T = 100 \log(1/M(f))^{(k-1)/2}$  and get that

$$\sum_{i \in I} \langle f_i, y_i f \rangle^2 \leqslant 2 \cdot 100^2 M(f) \log(1/M(f))^{k-1} + 2 \cdot 3^{k-1} e^{-25 \log(1/M(f))} \leqslant C^k M(f) \log(1/M(f))^{k-1},$$

and we are done by the choice of I.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lectures 11 - 12

#### Dor Minzer

Our goal in this lecture as well as the next lecture will be to demonstrate the power of analytical tools in Extremal Combinatorics. More specifically, we will see an instance of the junta method, a successful method in the area that has been introduced in the early 2000's and has recently risen in popularity.

## 1 Erdős-Ko-Rado type theorem

For  $k \leq n/2$ , a family of subsets  $\mathcal{F} \subseteq {[n] \choose k}$  is said to be intersecting if for any  $A, B \in \mathcal{F}$  we have that  $A \cap B \neq \emptyset$ . Given this definition, one may wonder: (1) How large can an intersecting family  $\mathcal{F}$  be? (2) What is the structure of the extremal families  $\mathcal{F}$ ? How about stability results?

The solution to this particular question is the well know, Erdos-Ko-Rado theorem, which asserts that the size of the largest intersecting family is  $\binom{n}{k-1}$ , and furthermore the extremal families are precisely dictatorships, i.e.  $\{A \mid |A| = k, i \in A\}$  for each  $i \in [n]$ . Can one prove a general structural result about intersecting families? Can they always be approximated by a considerably simpler families? This question is the main question we will consider in this as well as in the next lecture.

Before we dive into that, in order to get a feeling to where the method applies, we give several more examples of closely related problems.

- 1. t-wise intersecting families. Suppose  $k \leq 0.49n$ ; how large can a family  $\mathcal{F} \subseteq \binom{[n]}{k}$  be if for any  $A, B \in \mathcal{F}$  it holds that  $|A \cap B| \geqslant t$ ? Thinking about this problem for several minutes, one comes up with a candidate extremal example such as  $\mathcal{F} = \{A \mid 1, \dots, t \in A\}$ , and with a few more minutes one realizes that a more general class of families is  $\mathcal{F} = \{A \mid |A \cap [t+2r]| \geqslant t+r\}$  for any  $r \in \mathbb{N}$ . These turn out to be the extremal families and the junta method applies here; it is not a coincidence that these families are juntas.
- 2. Forbidden intersections. How large can a family  $\mathcal{F} \subseteq \binom{[n]}{k}$  be if for any  $A, B \in \mathcal{F}$  it holds that  $|A \cap B| \neq t-1$ . Note that any t intersecting family is an immediate candidate, and it turns out that these are also the extremal examples. Both this question and the previous question have analog in different domains, such as larger alphabets  $[m]^n$ ,  $S_n$ , vector spaces and more.
- 3. Suppose  $n \geqslant sk$ . How large can  $\mathcal{F} \subseteq \binom{[n]}{k}$  be if it doesn't contain a matching of size s, i.e.  $A_1, \ldots, A_s \in \mathcal{F}$  that are pairwise disjoint?

The solution to these problems is considerably more difficult and requires additional analytical tools as well as more advanced ideas in the junta method. In the example we show, we will only see the basic ideas and set-up.

Throughout this lecture, we will move back and fourth between the language of families of subsets  $\mathcal{F} \subseteq P([n])$ , and Boolean functions  $f \colon \{0,1\}^n \to \{0,1\}$ , by identifying a subset  $A \subset [n]$  with its indicator vector  $1_A \in \{0,1\}^n$ , and a family of subsets  $\mathcal{F}$  with the function  $f(1_A) = 1_{A \in \mathcal{F}}$ .

### 2 The p-biased cube

Instead of discussing uniform-sized families, it will be much more convenient for us to think of their product measure analogs.  $^1$  That is, instead of thinking about families in  $\binom{[n]}{k}$ , we will think of families of subsets, or equivalently subsets of  $\{0,1\}^n$ , and our measure will be the p-biased measure with p=k/n. This is the measure on  $\{0,1\}^n$  defined as  $\mu_p(x)=p^{|x|}(1-p)^{n-|x|}$ , where |x| is the number of 1's in x. Intuitively, since most of the measure of  $\mu_p$  lies on points whose number of ones is  $pn\pm O(\sqrt{pn})=k\pm\sqrt{k}$  we expect the p-biased measure of the largest intersecting family to be closely related to the size of the largest intersecting family in  $\binom{[n]}{k}$ . This is indeed the case, and hence from now on we will focus on the former problem.

Considering the measure space  $(\{0,1\}^n, \mu_p)$ , one can generalize much of what we've seen so far in the course with one important remark. Roughly speaking, the situation is vastly different depending on the range of p.

- 1. The range in which p is bounded away from 0 and 1, i.e.  $0 < \zeta \leqslant p \leqslant 1 \zeta$  for some absolute constant  $\zeta$ . In this case, almost everything behaves exactly as in the p=1/2 case. In particular, the hypercontractive inequality holds (albeit with slightly worse constants), the KKL theorem and the Friedgut's junta theorem also hold (albeit with constants depending on  $\zeta$ ); we will not repeat the proofs of these results here, and refer the interested reader to the book.
- 2. The range in which p or 1-p decay with n, say  $p=1/\sqrt{n}$ . This is a much more challenging range from the analytical perspective, and almost all of the results we've seen so far in this course completely break. Given time constraints, we will discuss this range later on in the course.

#### 3 The main result

The key result we will prove in this and the next lecture is the following theorem, due to Dinur and Friedgut.

**Theorem 3.1.** For all  $\zeta > 0$ ,  $\varepsilon > 0$  there exists  $J \in \mathbb{N}$  such that the following holds. If  $\mathcal{F} \subseteq \{0,1\}^n$  is an intersecting family, and  $\zeta , then there exists an intersecting <math>J$ -junta  $\mathcal{J} \subseteq \{0,1\}^n$  such that  $\mu_p(\mathcal{F} \setminus \mathcal{J}) \leqslant \varepsilon$ .

In words, the theorem asserts that an intersecting family is nearly contained in a special intersecting family, i.e. a junta. The proof of this theorem incorporates several components, some of which we have already seen, while others we have not:

- 1. First, we will define the notion of "monotonicity" of families/ functions, and argue that one may assume  $\mathcal{F}$  to be monotone increasing.
- 2. Secondly, we will define a certain notion of "pseudo-randomness", and show that any family of subsets may be decomposed into a small number of sub-families that are pseudo-random (+junk sub-families that will be small in measure).
- Thirdly, we will show that pseudo-random families contain intersections of any constant size (we will actually need, and prove, a stronger statement along these lines which deals with two pseudo-random families).

<sup>&</sup>lt;sup>1</sup>There is a standard way to move between these two settings that we will not present here.

#### 3.1 Upwards closure

Given a family  $\mathcal{F} \subseteq P([n])$ , the upwards closure of  $\mathcal{F}$  is defined as

$$\mathcal{F}^{\uparrow} = \{ A \subseteq [n] \mid \exists B \in \mathcal{F}, A \supseteq B \}.$$

**Claim 3.2.** Suppose  $\mathcal{F}$  is an intersecting family. Then  $\mathcal{F}^{\uparrow}$  is also intersecting.

*Proof.* Let  $A, A' \in \mathcal{F}^{\uparrow}$ . Then by definition there are  $B, B' \in \mathcal{F}$  such that  $B \subseteq A, B' \subseteq A'$ . As  $\mathcal{F}$  is intersecting,  $B \cap B'$  is non-empty, and as  $A \cap A' \supseteq B \cap B'$ , we get that  $A \cap A'$  is also non-empty.

Note that if we proved the theorem for  $\mathcal{F}^{\uparrow}$ , then we're done as  $\mu_p(\mathcal{F} \setminus \mathcal{J}) \leqslant \mu_p(\mathcal{F}^{\uparrow} \setminus \mathcal{J})$  for any family  $\mathcal{J}$ . We thus assume that  $\mathcal{F} = \mathcal{F}^{\uparrow}$  henceforth, i.e. that  $\mathcal{F}$  is upwards closed.

#### 3.2 Quasi-randomness

Next, we introduce a notion of quasi-randomness that will be useful for us in this context.

**Definition 3.3.** Let  $r \in \mathbb{N}$ ,  $\varepsilon > 0$  and  $0 . We say a Boolean function <math>f : \{0,1\}^n \to \{0,1\}$  is  $(r,\varepsilon)$  quasi-random with respect to p if for any  $R \subseteq [n]$  of size at most R, and any  $z \in \{0,1\}^R$  it holds that

$$|\mu_p(f_{R\to z}) - \mu_p(f)| \leqslant \varepsilon.$$

In words, a function f is  $(r, \varepsilon)$  quasi-random if any restriction of size at most r can change the average of the function by at most  $\varepsilon$ .

**Remark 3.4.** In the homework assignment you will see a connection between this notion and a function having small Fourier coefficients on the low levels.

**Definition 3.5.** Let  $r \in \mathbb{N}$ ,  $\varepsilon > 0$  and  $0 . We say <math>\mathcal{F}$  is  $(r, \varepsilon)$  quasi-random with respect to p if  $1_{\mathcal{F}}$  is  $(r, \varepsilon)$  quasi-random with respect to p.

We now state and prove a regularity lemma suitable for the notion of quasi-randomness we have just defined.

**Lemma 3.6.** For all  $r \in \mathbb{N}$ ,  $\varepsilon > 0$ ,  $\delta, \zeta > 0$  there exists  $J \in \mathbb{N}$  such that the following holds. If  $\zeta \leqslant p \leqslant 1 - \zeta$ , and  $f \colon \{0,1\}^n \to \{0,1\}$  is any Boolean function, then there exists a set  $T \subseteq [n]$  of size at most J, such that

$$\Pr_{z \sim \mu_n^T} \left[ f_{T \to z} \text{ is not } (r, \varepsilon) \text{ quasi-random} \right] \leqslant \delta.$$

In words, the lemma asserts that for any function f we may find a constant size set of variables T, such that randomly restricting them, the resulting function is quasi-random.

*Proof.* The proof is iterative, and is based on the construction of an appropriate potential function. Starting with  $T = \emptyset$ , we define a potential function  $p : P([n]) \to [0, 1]$  by

$$p(T) = \mathbb{E}_{z \sim \mu_p^T} \left[ (\mu_p(f_{T \to z}) - \mu_p(f))^2 \right].$$

Our goal will show that if we have some  $T \subseteq [n]$  for which the condition fails, i.e. for which many of the restrictions  $f_{T\to z}$  are not quasi-random, then we may find T' which is a bit larger and p(T') is substantially

larger than p(T). Thus, as p(T) is always bounded by 1, the process would terminate in constantly many steps, in which case T necessarily satisfies the condition of the lemma.

Suppose we have T for which the condition fails, and let  $Z = \{z \mid f_{T \to z} \text{ is not } (r, \varepsilon) \text{ quasi-random} \}$ . For each  $z \in Z$ , pick  $R_z \subseteq [n] \setminus T$  of size at most r and  $w \in \{0,1\}^{R_z}$  demonstrating that  $f_{T \to z}$  is not  $(r,\varepsilon)$  quasi-random, and define  $T' = T \cup \bigcup_{z \in Z} R_z$ .

**Bounding the size of** T'. Note that  $|Z| \leq 2^{|T|}$ , and so  $|T'| \leq |T| |Z| r \leq |T| |Z^{|T|} \leq r 2^{2|T|}$ .

Analyzing the potential function. Let us write  $R = \bigcup_{z \in Z} R_z$  and

$$p(T') = \mathbb{E}_{z \sim \mu_p^T} \left[ \mathbb{E}_{z' \sim \mu_p^R} \left[ (\mu_p(f_{T \to z, R \to z'}) - \mu_p(f))^2 \right] \right].$$

First, we note that by Cauchy-Schwarz, for each z

$$\underset{z' \sim \mu_p^R}{\mathbb{E}} \left[ (\mu_p(f_{T \to z, R \to z'}) - \mu_p(f))^2 \right] \geqslant (\underset{z' \sim \mu_p^R}{\mathbb{E}} \left[ \mu_p(f_{T \to z, R \to z'}) - \mu_p(f) \right])^2 = (\mu_p(f_{T \to z}) - \mu_p(f))^2,$$

which immediately shows that  $p(T') \ge p(T)$ . The essence in our argument is to show that for  $z \in Z$ , there is substantial slack in the above inequality, which will give us the desired increase in the potential.

Fix  $z \in Z$ . As before, we may write

$$\mathbb{E}_{z' \sim \mu_p^R} \left[ (\mu_p(f_{T \to z, R \to z'}) - \mu_p(f))^2 \right] = \mathbb{E}_{w \sim \mu_p^{R_z}} \left[ \mathbb{E}_{w' \sim \mu_p^{R \setminus R_z}} \left[ (\mu_p(f_{T \to z, R_z \to w, R \setminus R_z \to w'}) - \mu_p(f))^2 \right] \right] \\
\geqslant \mathbb{E}_{w \sim \mu_p^{R_z}} \left[ \left( \mathbb{E}_{w' \sim \mu_p^{R \setminus R_z}} \left[ \mu_p(f_{T \to z, R_z \to w, R \setminus R_z \to w'}) - \mu_p(f) \right] \right)^2 \right] \\
= \mathbb{E}_{w \sim \mu_p^{R_z}} \left[ (\mu_p(f_{T \to z, R_z \to w}) - \mu_p(f))^2 \right].$$

Consider the random variable  $X_z \colon \{0,1\}^{R_z} \to [-1,1]$ , whose value at w is  $X_z(w) = \mu_p(f_{T \to z, R_z \to w}) - \mu_p(f)$ . Then note that

$$\underset{w \sim \mu_p^{R_z}}{\mathbb{E}} \left[ (\mu_p(f_{T \to z, R_z \to w}) - \mu_p(f))^2 \right] - (\mu_p(f_{T \to z}) - \mu_p(f))^2 = \underset{w}{\mathbb{E}} \left[ X_z(w)^2 \right] - \underset{w}{\mathbb{E}} \left[ X_z(w) \right]^2 = \operatorname{var}(X_z),$$

so it is enough to lower bound the variance of X. By definition,

$$\operatorname{var}(X_z) = \underset{w}{\mathbb{E}} \left[ (X_z(w) - \underset{w}{\mathbb{E}} \left[ X_z(w) \right])^2 \right] = \underset{w}{\mathbb{E}} \left[ (\mu_p(f_{T \to z, R_z \to w}) - \mu_p(f_{T \to z}))^2 \right],$$

and as  $R_z$  is a witness that  $f_{T\to z}$  is not  $(r,\varepsilon)$  quasi-random, there is some  $w^\star \in \{0,1\}^{R_Z}$  such that the inner difference is at least  $\varepsilon^2$  in absolute value. As  $\mu_p(w)^\star \geqslant \zeta^r$  (by assumption on p and the fact that the size of  $R_z$  is at most r), it follows that  $\operatorname{var}(X_z) \geqslant \zeta^r \varepsilon^2$ .

Combining everything, we get that

$$\begin{split} p(T') - p(T) &= \underset{z \sim \mu_p^T}{\mathbb{E}} \left[ \underset{z' \sim \mu_p^R}{\mathbb{E}} \left[ (\mu_p(f_{T \to z, R \to z'}) - \mu_p(f))^2 \right] - (\mu_p(f_{T \to z}) - \mu_p(f))^2 \right] \\ &\geqslant \underset{z \in \mu_p^T}{\mathbb{E}} \left[ 1_{z \in Z} \mathsf{var}(X_z) \right] \geqslant \underset{z \in \mu_p^T}{\mathbb{E}} \left[ 1_{z \in Z} \zeta^r \varepsilon^2 \right] \geqslant \delta \zeta^r \varepsilon^2. \end{split}$$

| Concluding, we get that the process terminates after at most $\frac{1}{\delta c r_F^2}$ steps and finds a set T | whose size |
|-----------------------------------------------------------------------------------------------------------------|------------|
| depends only on $r, \varepsilon, \delta, \zeta$ satisfying the condition of the lemma.                          |            |

In the next lecture, we will use this regularity lemma in order to prove Theorem 3.1.

### Properties of quasi-random families

### Quasi-random families have a sharp threshold

We begin with a neat application of Friedgut's theorem, showing that quasi-random functions have a sharp threshold.

**Lemma 4.1.** For all  $\zeta, \alpha > 0$ , there exists  $r \in \mathbb{N}$ ,  $\varepsilon > 0$  such that the following holds. Suppose  $\zeta$ and  $f:\{0,1\}^n \to \{0,1\}$  is monotone with  $\mu_p(f)\geqslant \alpha$ . If f is  $(r,\varepsilon)$  quasi-random, then  $\mu_{p+\zeta/2}(f)\geqslant 0.9$ .

*Proof.* Suppose towards contradiction that  $\mu_{p+\zeta/2}(f) \leqslant 0.9$ . Then  $\frac{\mu_{p+\zeta/2}(f) - \mu_p(f)}{(p+\zeta/2) - p} \leqslant \frac{2}{\zeta}$ . By Lagrange's mean-value theorem, there is  $p' \in (p, p + \zeta/2)$  such that

$$\frac{d\mu_q(f)}{dq}(p') = \frac{\mu_{p+\zeta/2}(f) - \mu_p(f)}{(p+\zeta/2) - p} \leqslant \frac{2}{\zeta}.$$

By the Russo-Margulis lemma, as f is monotone,  $I[f;\mu_{p'}]=\frac{d\mu_q(f)}{dq}(p')$ , so by Friedgut's junta theorem there is  $J\in\mathbb{N}$  depending only on  $\zeta,\alpha$ , and  $g\colon\{0,1\}^n\to\{0,1\}$  a J-junta such that  $\Pr_{x\sim\mu_{p'}}[f(x)\neq g(x)]\leqslant 0$  $\frac{\alpha}{1000}$ .

We choose the parameters  $r, \varepsilon$  of the quasi-randomness now as r = J and  $\varepsilon = \frac{\alpha}{4}$ .

Let R be the set of variables q depends on. We argue that

$$\Pr_{x \sim \mu_{n'}^R} [g_{R \to x} \equiv 0] > 10^{-2}.$$

Indeed,

$$0.9 \geqslant \mu_{p+\xi}(f) \geqslant \mu_{p'}(f) \geqslant \mu_{p'}(g) - \Pr_{x \sim \mu_{p'}} [f(x) \neq g(x)],$$

so  $\mu_{p'}(g)\leqslant 0.9+\frac{\alpha}{1000}<0.99.$  Choose  $x\sim\mu_{p'}^R$ , and consider the following two events:

$$g_{R\to x} \equiv 0,$$
 
$$\Pr_{w \sim \mu_{n'}^{[n] \setminus R}} \left[ f_{R\to x}(w) \neq g_{R\to x}(w) \right] \leqslant \frac{\alpha}{2}.$$

The first event holds with probability  $> 10^{-2}$  as we have just seen; as for the second event,

$$\mathbb{E}\left[\Pr_{w \sim \mu_{p'}^{[n] \setminus R}} \left[ f_{R \to x}(w) \neq g_{R \to x}(w) \right] \right] = \Pr_{y \sim \mu_{p'}} \left[ f(y) \neq g(y) \right] \leqslant \frac{\alpha}{1000},$$

so by Markov's inequality the second event holds with probability at least  $1 - \frac{2}{10^3}$ .

As the sum of the probabilities of the events exceeds 1, it follows that there is x for which both events hold. In that case, we get that

$$\Pr_{w \sim \mu_{p'}^{[n] \setminus R}} \left[ f_{R \to x}(w) \neq 0 \right] \leqslant \frac{\alpha}{2},$$

which by monotonicity implies that

$$\Pr_{w \sim \mu_p^{[n] \setminus R}} \left[ f_{R \to x}(w) \neq 0 \right] \leqslant \frac{\alpha}{2}$$

and in particular  $\mu(f_{R\to x}) \leqslant \frac{\alpha}{2}$ . The assignment (R,x) now contradicts the  $(r,\varepsilon)$  quasi-randomness of f.

### 4.2 Quasi-random families are not cross intersecting

Armed with Lemma 4.1, we are almost ready to prove Theorem 3.1. But first, we need a simple version of the Erdős-Ko-Rado theorem.

**Claim 4.2.** Suppose  $\mathcal{G}, \mathcal{H} \subseteq P([n])$  are such that  $\mu_{1/2}(\mathcal{G}) + \mu_{1/2}(\mathcal{H}) > 1$ . Then there are disjoint  $F \in \mathcal{F}, G \in \mathcal{G}$ .

*Proof.* Sample  $A \subseteq [n]$  uniformly at random, and write  $\mu_{1/2}(\mathcal{G}) = \mathbb{E}_A [1_{A \in \mathcal{G}}]$ , and  $\mu_{1/2}(\mathcal{H}) = \mathbb{E}_A [1_{\bar{A} \in \mathcal{H}}]$ ; the last identity is true since the distribution of  $\bar{A}$  is uniform among all subsets of [n]. Thus, by the premise

$$1 < \mu_{1/2}(\mathcal{G}) + \mu_{1/2}(\mathcal{H}) = \underset{A}{\mathbb{E}} \left[ 1_{A \in \mathcal{G}} + 1_{\bar{A} \in \mathcal{H}} \right],$$

so with positive probability  $1_{A \in \mathcal{G}} + 1_{\bar{A} \in \mathcal{H}} > 1$ , i.e. there is A such that  $A \in \mathcal{G}$ ,  $\bar{A} \in \mathcal{H}$ , and we take G = A,  $H = \bar{A}$ .

We now combine Lemma 4.1 and Claim 4.2 to show that quasi-random families are not cross intersecting.

**Lemma 4.3.** For all  $\alpha, \zeta > 0$  there exists  $r \in \mathbb{N}$ ,  $\varepsilon > 0$  such that the following holds. Suppose  $\zeta and <math>\mathcal{G}, \mathcal{H} \subseteq P([n])$  are monotone families such that  $\mu_p(\mathcal{G}), \mu_p(\mathcal{H}) \geqslant \alpha$ , and each one of them is  $(r, \varepsilon)$ -quasi-random.

Then there are disjoint  $G \in \mathcal{G}$ ,  $H \in \mathcal{H}$ .

*Proof.* Take  $\xi = \frac{1}{2} - p \geqslant \zeta$ , and find  $(r, \varepsilon)$  from Lemma 4.1. Then we get that

$$\mu_{p+\xi}(\mathcal{G}), \mu_{p+\xi}(\mathcal{H}) \geqslant 0.9,$$

and as  $p + \xi = \frac{1}{2}$ , we conclude from Claim 4.2 that  $\mathcal{F}, \mathcal{G}$  cross contain disjoint sets, as desired.

#### 4.3 Proof of Theorem 3.1

Fix  $\zeta, \varepsilon > 0$  as in the theorem.

As we argued last time, by moving from  $\mathcal F$  to its upwards closure, we may assume  $\mathcal F$  to be upwards closed.

Set  $\alpha = \varepsilon/2$ , and choose  $(r, \varepsilon')$  from Lemma 4.3. We now take J from Lemma 3.6 for  $r, \varepsilon'$ ,  $\delta = \varepsilon/2$  and  $\zeta$ . Applying Lemma 3.6 on  $f = 1_{\mathcal{F}}$ , we find a set  $T \subseteq [n]$  of size at most J, such that

$$\Pr_{z \sim \mu_p^T} \left[ f_{T \to z} \text{ is not } (r, \varepsilon') \text{ quasi-random} \right] \leqslant \delta.$$

Define

$$\mathcal{T} = \left\{ \, A \subseteq T \mid f_{T \to 1_A} \text{ is } (r, \varepsilon') \text{ quasi-random and } \mu_p(f_{T \to 1_A}) \geqslant \varepsilon/2 \right. \enspace ,$$

and define the T-junta  $\mathcal{J} = \{A \subseteq [n] \mid A \cap T \in \mathcal{T}\}$ . To complete the proof, we will show that  $\mu_p(\mathcal{F} \setminus \mathcal{J})$  and that  $\mathcal{J}$  is intersecting.

**Bounding**  $\mu_p(\mathcal{F} \setminus \mathcal{J})$ . Let  $g \colon \{0,1\}^n \to \{0,1\}$  be the function of  $\mathcal{J}$ . Then

$$\mu_p(\mathcal{F} \setminus \mathcal{J}) = \underset{z \sim \{0,1\}^T}{\mathbb{E}} \left[ \mu_p((\mathcal{F} \setminus \mathcal{J})_{T \to z}) \right].$$

By definition of  $\mathcal{J}$ , each z for which  $(\mathcal{F} \setminus \mathcal{J})_{T \to z}$  is non-empty either satisfies that  $f_{T \to z}$  is not  $(r, \varepsilon')$  quasi-random, or that  $\mu_p(f_{T \to z}) < \varepsilon/2$ . Thus,

$$\mu_p(\mathcal{F} \setminus \mathcal{J}) \leqslant \underset{z \sim \{0,1\}^T}{\mathbb{E}} \left[ \mathbf{1}_{f_{T \to z} \text{ is } (r,\varepsilon') \text{ quasi-random}} + \mu_p(f_{T \to z}) \mathbf{1}_{\mu_p(f_{T \to z}) < \varepsilon/2} \right]$$

The expectation of the first indicator is at most  $\delta \leqslant \varepsilon/2$ , and for the second expectation we have that it is at most  $\varepsilon/2$ , hence  $\mu_p(\mathcal{F} \setminus \mathcal{J}) \leqslant \varepsilon$ .

**Showing that**  $\mathcal{J}$  is intersecting. We will show that for any  $A, A' \in \mathcal{T}$ , we have that  $A \cap A' \neq \emptyset$ , which is clearly enough.

Assume towards contradiction otherwise, and take disjoint  $A, A' \in \mathcal{T}$ . Consider the families  $\mathcal{G} = \mathcal{F}_{T \to A}$ ,  $\mathcal{H} = \mathcal{F}_{T \to A'}$ . By definition of  $\mathcal{T}$ , they are both  $(r, \varepsilon')$  quasi-random and have  $\mu_p$ -measure at least  $\alpha$ . Hence by Lemma 4.3 we may find disjoint  $G \in \mathcal{G}$ ,  $H \in \mathcal{H}$ . Thus, we have  $A \cup G \in \mathcal{F}$  and  $A' \cup H \in \mathcal{F}$  which are disjoint, which contradicts the fact that  $\mathcal{F}$  is intersecting.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lectures 13,14

#### Dor Minzer

## 1 Motivation and statement

In this lecture, we will begin discussing the invariance principle, which is a useful tool allowing one to transfer questions from the Boolean hypercube into Gaussian space. This is useful for several reasons: in Gaussian space, one may use several properties that are non-existent in the Boolean hypercube. One example is rotation invariance (i.e., a the Gaussian distribution over  $\mathbb{R}^n$  is invariant under rotations) which is absent from the cube as rotations of Boolean vectors need not be Boolean vectors themselves.

An example of this phenomenon is already apparent in the well-known central-limit theorem. This theorem states that if  $X_1,\ldots,X_n$  are "reasonable" random variables, independently distributed with mean 0 and variance 1, then the distribution of  $(X_1+\ldots+X_n)/\sqrt{n}$  approaches a standard Gaussian random variable N(0,1). This phrasing, while correct, is a bit misleading in a sense. The point here is that if the random variables  $X_1,\ldots,X_n$  are reasonable and normalized, then the limiting distribution of  $(X_1+\ldots+X_n)/\sqrt{n}$  does not really depend on the specific distribution of  $X_1,\ldots,X_n$ , and will be the same. In other words, if we look at the linear function  $f(z_1,\ldots,z_n)=\frac{1}{\sqrt{n}}\sum_{i=1}^n z_i$ , then the asymptotic distribution of  $f(X_1,\ldots,X_n)$  is the same for all reasonable  $X_1,\ldots,X_n$ . For example, we have that

$$f(X_1,\ldots,X_n)\approx f(G_1,\ldots,G_n),$$

where  $X_1, \ldots, X_n$  are reasonable and normalized, and  $G_1, \ldots, G_n$  are standard Gaussians.

The additional fact that  $f(G_1, \ldots, G_n)$  is distributed as a standard Gaussian itself should be thought of as a "miracle" in this context; the way we have stated the statement suggests that perhaps one can prove such result for more general class of functions f. Indeed, the main question the invariance principle investigates, is what classes of functions we can prove such universality of the probability law of  $f(X_1, \ldots, X_n)$  for.

To get some intuition into this question, we consider a few examples.

- $f(z_1,\ldots,z_n)=z_1.$
- $f(z_1,\ldots,z_n) = \prod_{i=1}^{100} z_i$ .
- $f(z_1,\ldots,z_n) = \frac{1}{\sqrt{\binom{n}{3}}} \sum_{|S|=3} \prod_{i \in S} z_i$ .

What goes wrong in the first 3 examples? How can you eliminate them? The issue with the first example is that there is a variable with large influence; this means that in a sense, f looks like a dictatorship, and for such functions it is clear that a uniform bit  $\{-1,1\}$  looks differently from a Gaussian random variable. This is also the issue with the second example. The issue with the third example is that the degree of f is high. The result, that will be the focus of this and next lecture, asserts that if one requires the function to not have influential variables and be of low-degree, then an invariance principle holds. More formally:

**Theorem 1.1.** For all  $d \in \mathbb{N}$ , if  $f(x_1, \ldots, x_n) = \sum_{|S| \leq d} \widehat{f}(S)\chi_S(x)$  is a function of degree at most d, and  $\psi \colon \mathbb{R} \to \mathbb{R}$  is a smooth function with  $\|\psi'''\|_{\infty} \leq C$ , then

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi(f(x)) \right] - \mathbb{E}_{z \sim N(0,I_n)} \left[ \psi(f(z)) \right] \leqslant \frac{C}{2} 2^{3d/2} \sum_{i=1}^n I_i[f]^{3/2}.$$

**Corollary 1.2.** For all  $C, \varepsilon > 0$ ,  $d \in \mathbb{N}$  there is  $\tau > 0$  such that if  $f(x_1, \ldots, x_n) = \sum_{|S| \le d} \widehat{f}(S)\chi_S(x)$  is a function of degree at most  $d, \psi \colon \mathbb{R} \to \mathbb{R}$  is a smooth function with  $\|\psi'''\|_{\infty} \leqslant C$  and  $\operatorname{var}(f) \leqslant C$ , then

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi(f(x)) \right] - \mathbb{E}_{z \sim N(0,I_n)} \left[ \psi(f(z)) \right] \leqslant \varepsilon.$$

*Proof.* Using the last theorem, we have that this difference is bounded by  $\frac{C}{3}2^{3d/2}\tau I[f]\leqslant \frac{C}{3}2^{3d/2}\tau d\text{var}(f)\leqslant C^29^d\sqrt{\tau}$ , so choosing  $\tau=\left(\frac{\varepsilon}{C^29^d}\right)^2$  finishes the proof.

Thus, the theorem asserts that the distributions of f(x) and f(z) look very similar as far as *smooth test* functions are concerned. The above formulation of the invariance principle is the most basic version of it and there are extensions of it:

- 1. to non-smooth functions, such as  $\psi(t) = 1_{t \leq 10}$ . Proving these extensions requires smooth approximation to such functions, and the idea of anti-concentration in Gaussian space.
- 2. There is an extension of this result to functions that are not low-degree, but are close to low-degree functions and Lipshitz functions  $\psi$ .
- 3. The fact that z is distributed according to a standard Gaussian random variable is not very important, and similar statements can be made as long as: (1) the first and second moment of coordinates of x and z match, and (2) one has a hypercontractive inequality for both functions in x, and functions in z.

In this lecture, we will first present prove a variant of Theorem 1.1 in the special case that f is a linear function. This is a basic result in probability theory called the Berry-Essen Theorem, and will help us in order to introduce the replacement method. We will then explain the difference and challenges that will arise when we try to adapt the argument to the setting of Theorem 1.1, and then briefly discuss hypercontractivity in Gaussian space.

# 2 The Berry-Essen Theorem

**Theorem 2.1.** If  $f(x_1, ..., x_n) = \sum_{i=1}^n a_i x_i$ , and  $\psi \colon \mathbb{R} \to \mathbb{R}$  is a smooth function with  $\|\psi'''\|_{\infty} \leqslant C$ , then

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi(f(x)) \right] - \mathbb{E}_{z \sim N(0,I_n)} \left[ \psi(f(z)) \right] \leqslant \frac{C}{2} \sum_{i=1}^n a_i^3.$$

*Proof.* Let  $x \sim \{-1,1\}^n$ ,  $z \sim N(0,I_n)$  be independent, and for each  $0 \leqslant t \leqslant n$  consider the following hybrid distribution:

$$U_t = (x_1, \dots, x_t, z_{t+1}, \dots, z_n);$$
  $U_{-(t+1)} = (x_1, \dots, x_t, z_{t+2}, \dots, z_n).$ 

Note that  $U_0 = z$ ,  $U_n = x$ , so our difference can be written as

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi(f(U_n)) \right] - \mathbb{E}_{z \sim N(0,I_n)} \left[ \psi(f(U_0)) \right] = \sum_{t=0}^{n-1} \mathbb{E}_{x,z} \left[ \psi(f(U_{t+1})) \right] - \mathbb{E}_{x,z} \left[ \psi(f(U_t)) \right] \\
\leqslant \sum_{t=0}^{n-1} \mathbb{E}_{x,z} \left[ \psi(f(U_{t+1})) \right] - \mathbb{E}_{x,z} \left[ \psi(f(U_t)) \right] .$$

Our goal is to bound the summand corresponding to t by  $Ca_t^3$ . Fix t. Since f is linear, we may write  $f(U_{t+1}) = g(U_{-(t+1)}) + a_{t+1}x_{t+1}$  and  $f(U_t) = g(U_{-(t+1)}) + a_{t+1}z_{t+1}$ , where g is a function on n-1 coordinates indexed by  $i=1,\ldots,t,t+2,\ldots,n$ , and defined by  $g(u)=\sum_{i\neq t+1}a_iu_i$ . We may then write the tth-summand in the above sum as

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{-(t+1)}) + a_{t+1} x_{t+1} \right) \right] - \mathbb{E}_{x,z} \left[ \psi \left( g(U_{-(t+1)}) + a_{t+1} z_{t+1} \right) \right] .$$

Fix  $u = U_{-(t+1)}$ , and expand g according to Taylor's theorem around the point g(u). We get

$$\psi(g(u) + w) = \psi(g(u)) + \psi'(g(u))w + \frac{1}{2}\psi''(g(u))w^2 + \frac{1}{3!}\psi'''(\xi)w^3,$$

where  $\xi \in (g(u), g(u) + w)$  is some point. Thus,

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{-(t+1)}) + a_{t+1} x_{t+1} \right) \right] = \\
\mathbb{E}_{x,z} \left[ \psi \left( g(U_{-(t+1)}) + \psi'(g(U_{-(t+1)})) a_{t+1} x_{t+1} + \frac{1}{2} \psi''(U_{-(t+1)}) a_{t+1}^2 x_{t+1}^2 + \frac{1}{6} \psi'''(g(\xi_x(U_{-(t+1)}))) a_{t+1} x_{t+1}^3 \right],$$

where  $\xi_x(U_{-(t+1)})$  is some random variable. Using the fact that  $U_{-(t+1)}$  and  $x_{t+1}$  are independent and that the first and second moment of  $x_{t+1}$  are 0 and 1 respectively, we get that

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{-(t+1)}) + a_{t+1} x_{t+1} \right) \right] \\
= \mathbb{E}_{x,z} \left[ \psi(g(U_{-(t+1)})) + \frac{1}{2} \psi''(\xi(U_{-(t+1)})) a_{t+1}^2 + \frac{1}{6} \psi'''(\xi_x(g(U_{-(t+1)}))) a_{t+1} x_{t+1}^3 \right]$$

Similarly, we have

$$\begin{split} & \underset{x,z}{\mathbb{E}} \left[ \psi \left( g(U_{-(t+1)}) + a_{t+1} z_{t+1} \right) \right] \\ & = \underset{x,z}{\mathbb{E}} \left[ \psi(g(U_{-(t+1)})) + \frac{1}{2} \psi''(\xi(U_{-(t+1)})) a_{t+1}^2 + \frac{1}{6} \psi'''(g(\xi_z(U_{-(t+1)}))) a_{t+1} z_{t+1}^3 \right], \end{split}$$

and taking the difference we get

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{-(t+1)}) + a_{t+1} x_{t+1} \right) \right] - \mathbb{E}_{x,z} \left[ \psi \left( g(U_{-(t+1)}) + a_{t+1} z_{t+1} \right) \right] \\
\leqslant \frac{1}{6} \mathbb{E}_{x,z} \left[ \psi'''(g(\xi_x(U_{-(t+1)}))) a_{t+1}^3 x_{t+1}^3 + \psi'''(g(\xi_z(U_{-(t+1)}))) a_{t+1}^3 z_{t+1}^3 \right] .$$

To finish the proof, we use the triangle inequality and bound each expectation separately. For the first one we have

$$\mathbb{E}_{x,z} \left[ \psi'''(g(\xi_x(U_{-(t+1)}))) a_{t+1}^3 x_{t+1}^3 \right] \leqslant C |a_{t+1}|^3 \mathbb{E}_{x,z} \left[ |x_{t+1}|^3 \right] = C |a_{t+1}|^3$$

as  $|x_{t+1}| \leq 1$ . For the second one we have

$$\mathbb{E}_{x,z} \left[ \psi'''(g(\xi_z(U_{-(t+1)}))) a_{t+1}^3 z_{t+1}^3 \right] \leqslant C |a_{t+1}|^3 \mathbb{E}_{x,z} \left[ |z_{t+1}|^3 \right] = C |a_{t+1}|^3 \frac{4}{\sqrt{2\pi}}.$$

Combining, we get that

$$\mathbb{E}_{x,z} \left[ \psi(f(U_{t+1})) \right] - \mathbb{E}_{x,z} \left[ \psi(f(U_t)) \right] \leq \frac{1}{6} \left( 1 + \frac{4}{\sqrt{2\pi}} \right) C \left| a_{t+1} \right|^3 \leq \frac{C}{2} \left| a_{t+1} \right|^3.$$

Is this error bound even good? Note that in the central-limit theorem setting, we would have  $a_i = \frac{1}{\sqrt{n}}$ , so the error bound we have simplifies to  $\frac{C}{2\sqrt{n}}$ , which is very decent. In general, one can expect a bound on the sum of squares of the  $a_i$ 's, say  $\sum_{i=1}^n a_i^2 \leqslant 1$  (as is often the case in applications), and then we automatically get that the error can be further upper bounded by  $\frac{C}{2} \max_i |a_i|$ .

### 2.1 Generalizing the argument to low-degree polynomials

Can you see how to adapt the above argument to the setting of Theorem 1.1? What did we really do when we wrote  $f(U_{t+1}) = g(U_{-(t+1)}) + a_{t+1}z_{t+1}$ ? What we really did here is check the influence of variable t+1 on the function at the point  $U_{t+1}$ . This can be generalized to low-degree polynomials by considering

$$g(U_{t+1}) = \sum_{S \not\ni t+1} \widehat{f}(S) \chi_S(U_{t+1}), \qquad \partial_{t+1} f(U_{t+1}) = \sum_{S \ni t+1} \widehat{f}(S) \chi_{S \setminus \{t+1\}}(U_{t+1}),$$

and then we can write  $f(U_{t+1}) = g(U_{t+1}) + z_{t+1}\partial_{t+1}f(U_{t+1})$  and  $f(U_t) = g(U_t) + x_{t+1}\partial_{t+1}f(U_t)$ . Noting that both  $g(U_{t+1})$  and  $\partial_{t+1}f(U_{t+1})$  do not depend on the t+1 coordinate, we get that  $g(U_{t+1}) = g(U_t)$ ,  $\partial_{t+1}f(U_{t+1}) = \partial_{t+1}f(U_t)$ . At this point, one may attempt to run the argument from the proof of Theorem 2.1, and everything goes through until the part where we need to bound the third powers of the remainder of Taylor's theorem. We will do that using hypercontractivity, but we should note here that we have a function that takes as input both Gaussian as well as bits, so we should first justify that the hypercontractive inequality holds for such functions.

# 3 Hypercontractivity in Gaussian space

Hypercontractivity can be abstracted and generalized beyond the Boolean hypercube and you can read about such formalization in Ryan O'Donnell's book. Our treatment here would be more specialized to the setting we are in.

Consider the Gaussian real line, i.e.  $(\mathbb{R},\mu)$  where  $\mu(z)=\frac{1}{\sqrt{2\pi}}e^{-z^2/2}$  is the Gaussian density measure. We consider the space of functions  $f\colon\mathbb{R}\to\mathbb{R}$  equipped with the inner product  $\langle f,g\rangle=\int_\infty^\infty f(x)g(x)d\mu$ .

One may to find the analog of the Fourier expansion in this setting, and indeed there is such one. A good orthonormal set in this case is known as Hermite polynomials, given as  $h_0(z) \equiv 1$ , and for  $k \geqslant 1$ 

$$h_k(z) = (-1)^k e^{z^2/2} \frac{d^k}{dz^k} e^{-z^2/2}.$$

The first few Hermite polynomials are  $h_1(z) = z$ ,  $h_2(z) = z^2 - 1$ ,  $h_3(z) = z^3 - 3z$ , and they satisfy a bunch of nice properties we will not discuss further here.

Thus, we get a basis for the space of functions  $f:(\mathbb{R}^n,\mu^{\otimes n})\to\mathbb{R}$  by  $h_{\vec{k}}(z_1,\ldots,z_n)$  where  $\vec{k}=(k_1,\ldots,k_n)$  and  $h_{\vec{k}}(z_1,\ldots,z_k)=\prod_{i=1}^n h_{k_i}(z_i)$ . The Hermite expansion of f is

$$f(z) = \sum_{\vec{k}} \hat{f}(\vec{k}) h_{\vec{k}}(z).$$

Lastly, we need the notion of degrees. The degree of  $h_{\vec{k}}$  is  $k_1 + \ldots + k_n$ , and the degree of f is the maximum degree of  $h_{\vec{k}}$  such that  $\hat{f}(\vec{k}) \neq 0$ .

**Lemma 3.1** (Hypercontractivity for Gaussian space). Suppose  $f:(\mathbb{R}^n,\mu^{\otimes n})\to\mathbb{R}$  is a function of degree at most d, and  $q\geqslant 2$ . Then

$$||f||_q \leqslant \sqrt{q-1}^d ||f||_2.$$

*Proof.* Consider the sequence of functions  $g_r$  for  $r=1,\ldots,\infty$  where we have  $x_{i,j}$  independent  $\pm 1$  bits for  $i=1,\ldots,n$  and  $j=1,\ldots,r$ , defined by

$$g_r(x) = f\left(\frac{\sum\limits_{j=1}^r x_{1,j}}{\sqrt{r}}, \dots, \frac{\sum\limits_{j=1}^r x_{n,j}}{\sqrt{r}}\right).$$

Note that as  $\frac{\sum\limits_{j=1}^{r}x_{1,j}}{\sqrt{r}}$  approach a standard Gaussian random variable, we have that

$$\lim_{r \to \infty} \mathbb{E}_{x} \left[ \left| g_{r}(x) \right|^{\ell} \right] = \int_{-\infty}^{\infty} \left| f(z) \right|^{\ell} d\mu^{\otimes n}$$

for all  $\ell \in \mathbb{N}$ . Note that  $g_r$  has degree at most d, so combining this with hypercontractivity for bits we get that

$$||f||_4^4 = \lim_{r \to \infty} ||g_r||_4^4 \leqslant \lim_{r \to \infty} \sqrt{q-1}^{4d} ||g_r||_2^4 = \sqrt{q-1}^{4d} ||f||_2^4$$

finishing the proof.

In a similar fashion, we may prove a hypercontractive inequality for functions that get as input both  $\pm$  bits and Gaussians. For  $f \colon \{-1,1\}^t \times \mathbb{R}^{n-t} \to \mathbb{R}$ , we consider the natural orthonormal basis indexed by  $(S,\vec{k})$  where  $S \subseteq [t]$ ,  $\vec{k} = (k_{t+1},\ldots,k_n)$  and given as  $\chi_{S,\vec{k}}(x,z) = \chi_S(x)h_{\vec{k}}(z)$ . We define the degree of  $\chi_{S,\vec{k}}$  as  $|S| + k_{t+1} + \ldots + k_n$ , and the degree of f as the maximal degree of  $\chi_{S,\vec{k}}$  supported in its Fourier expansion.

**Lemma 3.2.** Suppose  $f: \{-1,1\}^t \times \mathbb{R}^{n-t} \to \mathbb{R}$  is a function of degree at most d, and  $q \ge 2$ . Then

$$||f||_q \leqslant \sqrt{q-1}^d ||f||_2.$$

## 4 Proof of Theorem 1.1

We are now in the position to prove Theorem 1.1. The proof is almost the same as the proof of Theorem 2.1, and as so we will be more brief and focus on the places where there is a difference.

*Proof.* Let  $x \sim \{-1,1\}^n$ ,  $z \sim N(0,I_n)$  be independent, and for each  $0 \le t \le n$  consider the following hybrid distribution:

$$U_t = (x_1, \dots, x_t, z_{t+1}, \dots, z_n).$$

Note that  $U_0 = z$ ,  $U_n = x$ , so our difference can be bounded as before by

$$\sum_{t=0}^{n-1} \mathbb{E}_{x,z} [\psi(f(U_{t+1}))] - \mathbb{E}_{x,z} [\psi(f(U_t))] .$$

Fix t, and recall the functions

$$g(U_{t+1}) = \sum_{S \not\ni t+1} \widehat{f}(S) \chi_S(U_{t+1}), \qquad \partial_{t+1} f(U_{t+1}) = \sum_{S \ni t+1} \widehat{f}(S) \chi_{S \setminus \{t+1\}}(U_{t+1}),$$

We may write  $f(U_{t+1}) = g(U_{t+1}) + x_{t+1}\partial_{t+1}f(U_{t+1})$  and  $f(U_{t+1}) = g(U_{t+1}) + z_{t+1}\partial_{t+1}f(U_{t+1})$ , and then write the tth-summand in the above sum as

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) + x_{t+1} \partial_{t+1} f(U_{t+1}) \right) \right] - \mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) + z_{t+1} \partial_{t+1} f(U_{t+1}) \right) \right] .$$

We use Taylor's theorem to get that

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) + x_{t+1} \partial_{t+1} f(U_{t+1}) \right) \right] = \mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) \right) + \psi' \left( g(U_{t+1}) \right) x_{t+1} \partial_{t+1} f(U_{t+1}) \right] \\
+ \frac{1}{2} \psi'' \left( g(U_{t+1}) \right) x_{t+1}^2 \partial_{t+1} f(U_{t+1})^2 \\
+ \frac{1}{6} \psi''' \left( g(\xi_x(U_{t+1})) \right) x_{t+1}^3 \partial_{t+1} f(U_{t+1})^3 \right],$$

and

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) + z_{t+1} \partial_{t+1} f(U_{t+1}) \right) \right] = \mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) \right) + \psi' \left( g(U_{t+1}) \right) z_{t+1} \partial_{t+1} f(U_{t+1}) \right] \\
+ \frac{1}{2} \psi'' \left( g(U_{t+1}) \right) z_{t+1}^{2} \partial_{t+1} f(U_{t+1})^{2} \\
+ \frac{1}{6} \psi''' \left( g(\xi_{z}(U_{t+1})) \right) z_{t+1}^{3} \partial_{t+1} f(U_{t+1})^{3} \right].$$

Thus, the first three terms match, and taking the difference we get

$$\mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) + a_{t+1} x_{t+1} \right) \right] - \mathbb{E}_{x,z} \left[ \psi \left( g(U_{t+1}) + a_{t+1} z_{t+1} \right) \right] \\
\leqslant \frac{1}{6} \mathbb{E}_{x,z} \left[ \psi'''(g(\xi_x(U_{t+1}))) x_{t+1}^3 \partial_{t+1} f(U_{t+1})^3 + + \psi'''(g(\xi_z(U_{t+1}))) z_{t+1}^3 \partial_{t+1} f(U_{t+1})^3 \right] .$$

To bound the first expectation, we note that it is at most

$$C \cdot \underset{x,z}{\mathbb{E}} \left[ |\partial_{t+1} f(U_{t+1})|^3 \right] = C \cdot ||\partial_{t+1} f||_3^3 \leqslant C(\sqrt{2}^d ||\partial_{t+1} f||_2)^3 \leqslant C2^{3d/2} I_{t+1}[f]^{3/2}.$$

For the second expectation, we bound it by

$$C \cdot \underset{x,z}{\mathbb{E}} \left[ |z_{t+1}|^3 \left| \partial_{t+1} f(U_{t+1}) \right|^3 \right] = C \frac{4}{\sqrt{2\pi}} \cdot \|\partial_{t+1} f\|_3^3 \leqslant \frac{4C}{\sqrt{2\pi}} 2^{3d/2} I_{t+1}[f]^{3/2},$$

and combining these bounds finishes the proof.

## 5 Extensions of the invariance principle

We shall now see several extensions of the invariance principle. These are by no way extensive.

### 5.1 Invariance principle for non-smooth test functions

In this section, we show that the invariance principle continues to hold for some non-smooth functions. We will consider cutoff functions, i.e.  $\psi_t(y) = 1_{y \geqslant t}$ , and for simplicity we consider the case t = 0.

**Theorem 5.1.** For all  $d \in \mathbb{N}$ ,  $\varepsilon > 0$  there is  $\tau > 0$  such that if  $f(x_1, \ldots, x_n) = \sum_{|S| \leqslant d} \widehat{f}(S)\chi_S(x)$  is a function of degree at most d, and  $\max_i I_i[f] \leqslant \tau$ , then

$$\underset{x \sim \{-1,1\}^n}{\mathbb{E}} \left[ \psi_0(f(x)) \right] - \underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \psi_0(f(z)) \right] \; \leqslant \varepsilon.$$

### 5.1.1 Smooth approximation of $\psi_0$

To prove this statement, we use smooth approximations. Namely, we fix a parameter  $\delta$  and find a function  $\psi_{\delta}$  such that:

- 1.  $\psi_{\delta} \colon \mathbb{R} \to [0,1]$  has continuous third derivative and  $\|\psi_{\delta}'''\|_{\infty} \leqslant O\left(\frac{1}{\delta^3}\right)$ .
- 2.  $\psi_{\delta}(y) = 0$  for  $y \leqslant 0$  and  $\psi_{\delta}(y) = 1$  for  $y \geqslant \delta$ .

This is a standard construction from calculus, and we quickly outline it below. Consider  $h \colon \mathbb{R} \to [0, \infty)$  defined by  $h(y) = \alpha e^{-1/(1-y^2)}$  for  $|y| \leqslant 1$  and h(y) = 0 otherwise, where  $\alpha$  is chosen so that the integral of h is 1; the function h is called a mollifier. Then h is smooth and  $||h'''||_{\infty} = O(1)$ . Consider

$$\psi(y) = (1_{(-\infty,0]} * h)(y).$$

1. If  $y \leq -1$ , then

$$\psi(y) = \int_{-\infty}^{\infty} 1_{(-\infty,0]}(w)h(y-w)dw = \int_{-\infty}^{0} h(y-w)dw = 1.$$

2. If y > 1, then

$$\psi(y) = \int_{-\infty}^{\infty} 1_{(-\infty,0]}(w)h(y-w)dw = \int_{-\infty}^{0} h(y-w)dw = 0.$$

Additionally,  $\psi$  is smooth with  $\|\psi\|_{\infty} = O(1)$ . Take  $\psi_2(y) = \psi_2(1-y)$ , so that  $\psi_2 = 0$  on  $y \leqslant 0$ , and  $\psi_2 = 1$  on  $y \geqslant 2$ . Take  $\psi_{\delta}(y) = \psi_2(\frac{y}{\delta})$  so that  $\psi_{\delta} = 0$  for  $y \leqslant 0$  and  $\psi_3 = 1$  for  $y \geqslant \delta$ . We have by the chain rule that  $\|\psi_{\delta}'''\|_{\infty} \leqslant O(1/\delta^3) \cdot \|\psi\|_{\infty} = O(1/\delta^3)$ .

#### 5.1.2 An anticoncetration bound in Gaussian space

If  $G \sim N(0,1)$ , and  $I \subseteq \mathbb{R}$  is an interval of length  $\varepsilon$ , then one can easily show that  $\Pr[|G| \le \varepsilon] \le O(\varepsilon)$ . The following theorem, due to Carbery and Wright, generalizes this fact to multi-linear polynomials.

**Theorem 5.2.** Suppose  $f(x) = \sum_{0 < |S| \le d} a_S \chi_S$  is a multi-linear polynomial such that  $\sum_S a_S^2 \le 1$ , and  $I \subseteq \mathbb{R}$  is an interval of length at most  $\varepsilon$ . Then

$$\Pr_{z \sim N(0,1)} [|f(z)| \leqslant \varepsilon] \leqslant O(d\varepsilon^{1/d}).$$

#### 5.1.3 Proof of Theorem 5.1

We prove that

$$\underset{x \sim \{-1,1\}^n}{\mathbb{E}} \left[ \psi_0(f(x)) \right] - \underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \psi_0(f(z)) \right] \leqslant \varepsilon,$$

and the proof of the other inequality is analogous. Let  $\delta>0$  to be determined, and pick  $\psi_{\delta}$  from the previous section. Then

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi_0(f(x)) \right] \leqslant \mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi_\delta(f(x)) \right] \leqslant \mathbb{E}_{z \sim N(0,I_n)} \left[ \psi_\delta(f(z)) \right] + O\left(\frac{1}{\delta^3}\right) 2^{3d/2} d\sqrt{\tau}.$$

where we used Theorem 1.1. Note that  $\psi_{\delta}(f(z)) = \psi_0(f(z))$  if  $f(z) \ge \delta$  or  $f(z) \le 0$ , and otherwise it is at most 1, so

$$\underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \psi_{\delta}(f(z)) \right] \leqslant \underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \psi_0(f(z)) \right] + \underset{z \sim N(0,I_n)}{\Pr} \left[ 0 \leqslant f(z) \leqslant \delta \right].$$

Combining the two inequalities and using Theorem 5.2 we get that

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi_0(f(x)) \right] \leqslant \mathbb{E}_{z \sim N(0,I_n)} \left[ \psi_0(f(z)) \right] + O\left(\frac{1}{\delta^3}\right) 2^{3d/2} d\sqrt{\tau} + O(d\delta^{1/d}).$$

We choose  $\delta = 2^{-C \cdot d \log(d/\varepsilon)}$  for large enough C > 0 so that the second error term is at most  $\varepsilon/2$ , and then  $\tau$  small enough so that the first term is at most  $\varepsilon$ , and the proof is concluded.

#### **5.1.4** Piecewise smooth functions

Using Theorem 5.1, it is not hard now to show that invariance holds for all piecewise smooth test functions  $\psi$ , i.e. test functions for which there is a partition of the real line into intervals  $\mathbb{R} = I_1 \cup \ldots \cup I_r$  such that  $\psi$  is smooth in the interior of each  $I_i$ . We omit the proof.

### 5.2 Invariance principle for functions with small Fourier tails

Next, we extend the invariance principle to functions that are not low-degree, but almost low degree.

**Theorem 5.3.** For all  $C, \varepsilon > 0$ ,  $d \in \mathbb{N}$  there is  $\tau > 0$  such that if  $f(x_1, \ldots, x_n) = \sum \widehat{f}(S)\chi_S(x)$  is a function such that  $\max_i I_i[f^{\leqslant d}] \leqslant \tau$ , and  $\psi \colon \mathbb{R} \to \mathbb{R}$  is a piecewise smooth function C-Lipshitz function with  $\|\psi'''\|_{\infty} \leqslant C$ ,

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi(f(x)) \right] - \mathbb{E}_{z \sim N(0,I_n)} \left[ \psi(f(z)) \right] \leq \varepsilon + 2C \|f^{\geqslant d}\|_2.$$

*Proof.* Write  $f = f^{\leq d} + f^{>d}$ . Then since  $\psi$  is C-Lipshitz

$$\mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi(f(x)) \right] - \mathbb{E}_{x \sim \{-1,1\}^n} \left[ \psi(f^{\leqslant d}(x)) \right] \leqslant \mathbb{E}_{x \sim \{-1,1\}^n} \left[ C \ f^{\leqslant d}(x) \ \right] \leqslant C \|f^{\leqslant d}\|_2.$$

Similarly,

$$\underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \psi(f(z)) \right] - \underset{x \sim \{-1,1\}^n}{\mathbb{E}} \left[ \psi(f^{\leqslant d}(z)) \right] \; \leqslant \underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ C \; \; f^{\leqslant d}(z) \; \right] \leqslant C \|f^{\leqslant d}\|_2.$$

The result now follows from Theorem 5.1.

### 5.3 Other extensions of the invariance principle

There are other extensions of the invariance principle: multi-dimensional versions, more relaxed requirements, general product domains and more. We will not elaborate on these points further.

## 6 Majority is stablest

We finish this lecture by showing one prominent application of the invariance principle, which was actually the original motivation for it. The Gaussian analog of the majority is stablest theorem was already known in the 19th century, and the idea of Mossel, O'Donnell and Oleszkiewicz was to deduce the Boolean case from it. We will show this reduction, starting with presenting the theorem in the Gaussian case.

**Definition 6.1.** For  $\rho \in [0,1]$ , the operator  $T_{\rho}$  acting on functions  $f: \mathbb{R}^n \to \mathbb{R}$  is defined as

$$U_{\rho}(z) = \mathbb{E}_{w \sim N(0, I_n)} \left[ f(\rho z + \sqrt{1 - \rho^2} w) \right].$$

Note that the distribution of  $\rho z + \sqrt{1-\rho^2}w$  is standard Gaussian that is  $\rho$ -correlated with z, so this is the analog of the noise operator from the Boolean case. It is easy to check that  $U_\rho \chi_S(z) = \rho^{|S|} \chi_S(z)$  for all monomials  $\chi_S$ .

**Definition 6.2.** Given  $\rho \in [0,1]$  and  $f: \mathbb{R}^n \to \mathbb{R}$ , the noise stability of f with parameter  $\rho$  is  $\mathsf{Stab}_{\rho}(f) = \langle f, U_{\rho} f \rangle$ .

The Gaussian analog of the majority is stablest theorem states that half-spaces maximize the noise stability of balanced, bounded functions:

**Theorem 6.3.** [Borel's theorem] Let  $\rho \in [0,1]$ , and  $f: \mathbb{R}^n \to [-1,1]$  with  $\mathbb{E}[f] = 0$ . Then  $\mathsf{Stab}_{\rho}(f) \leqslant 1 - \frac{2}{\pi}\mathsf{Arccos}(\rho)$ .

We will not prove this theorem here, though at least for many values of  $\rho$  there is a relatively simple proof due to Kindler and O'Donnell, and in general there are several known proofs which are not too hard. Instead, we will show how to deduce the Majority is Stablest theorem from it.

**Theorem 6.4.** For all  $\varepsilon > 0$ ,  $\rho \in (0,1)$  there are  $d \in \mathbb{R}$  and  $\tau > 0$  such that if  $f : \{-1,1\}^n \to [-1,1]$  is balanced and  $\max_i I_i[f^{\leq d}] \leq \tau$ , then

$$\operatorname{Stab}_{\rho}(f) \leqslant 1 - \frac{2}{\pi} \operatorname{Arccos}(\rho) + \varepsilon.$$

*Proof.* Let  $\delta > 0$  small to be determined, and let  $f' = \mathrm{T}_{1-\delta}f$ . In the homework you will show that  $\mathrm{Stab}_{\rho}(f) \leqslant \mathrm{Stab}_{\rho}(f') + O_{\rho}(\delta)$ , and in the rest of the proof we will upper bound  $\mathrm{Stab}_{\rho}(f')$ .

Take  $d \in \mathbb{N}$  to also be determined later, and define the function  $\mathsf{Square}(t) = t^2$  for  $t \in [0,1]$  and  $\mathsf{Square}(t) = 0$  for  $t \leqslant 0$ , and otherwise 1. Then  $\mathsf{Square}$  is 2-Lipshitz and piecewise smooth, so we may apply the invariance principle on it. Now that

$$\mathsf{Stab}_{\rho}(f') = \langle f', \mathrm{T}_{\rho}f' \rangle = \langle \mathrm{T}_{\sqrt{\rho}}f', \mathrm{T}_{\sqrt{\rho}}f' \rangle = \underset{x \sim \{-1,1\}^n}{\mathbb{E}} \left[ \mathsf{Square}(\mathrm{T}_{\sqrt{\rho}}f'(x)) \right].$$

Thus, by Theorem 5.3 we have

$$\mathsf{Stab}_{\rho}(f') \leqslant \underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \mathsf{Square}(\mathsf{T}_{\sqrt{\rho}}f'(z)) \right] + \frac{\varepsilon}{2} + 4 \| (\mathsf{T}_{\sqrt{\rho}}f')^{\geqslant d} \|_2$$

for  $\tau(d,\varepsilon) > 0$  small enough. Note that

$$\|(\mathbf{T}_{\sqrt{\rho}}f')^{\geqslant d}\|_{2}^{2} \leqslant \sum_{|S|\geqslant d} \widehat{f}'(S)^{2} \leqslant (1-\delta)^{2d},$$

so the second error term is at most  $4(1-\delta)^d$ . Next, we would like to apply Theorem 6.3. Towards this end, note first that as f is multilinear,  $T_{\sqrt{\rho}}f' = U_{\sqrt{\rho}}f'$ . It may not necessarily be the case that f' is bounded on  $\mathbb{R}^n$  (in fact it is most likely not), and to get around this issue we will argue that it is "mostly bounded".

Define  $\operatorname{trunc}(s) = s$  if  $|s| \le 1$ , and otherwise 1 if s > 1 or -1 if s < -1, and consider the function  $F(z) = \operatorname{trunc}(f'(z))$ . By Theorem 5.3

$$\underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \ F(z) - f'(z) \ \right] = \underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \mathsf{dist}(f'(z),[0,1]) \right] \leqslant \underset{x \sim \{-1,1\}^n}{\mathbb{E}} \left[ \mathsf{dist}(f'(x),[0,1]) \right] + 4 \|(f')^{\geqslant d}\|_2,$$

and the first expectation is 0 whereas the error term is at most  $4(1-\delta)^d$ . In particular, it follows that

$$\underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \mathsf{Square}(\mathsf{T}_{\sqrt{\rho}}f'(z)) \right] \leqslant \underset{z \sim N(0,I_n)}{\mathbb{E}} \left[ \mathsf{Square}(\mathsf{T}_{\sqrt{\rho}}F(z)) \right] + 4(1-\delta)^d = \mathsf{Stab}_{\rho}(F) + 4(1-\delta)^d$$

Finally, to apply Theorem 6.3 we would like F to be balanced. Note that

$$\mathbb{E}[F] = \mathbb{E}[F] - \mathbb{E}[f'] \leqslant \mathbb{E}[F(z) - f'(z)] \leqslant 4(1 - \delta)^d,$$

so F is nearly balanced. It is not hard to show that in that case, the conclusion of Theorem 6.3 holds with bit of an error bound. For example, letting  $F'=\frac{F-\mathbb{E}[F]}{1+4(1-\delta)^d}$ , we have that F' is balanced and bounded so  $\operatorname{Stab}_{\rho}(F')\leqslant 1-\frac{2}{\pi}\operatorname{Arccos}(\rho)$ , and

$$\mathsf{Stab}_{\rho}(F) - \mathsf{Stab}_{\rho}(F') \ \leqslant 4\|F - F'\|_1 \leqslant 4 \cdot 4(1 - \delta)^d (\|F\|_1 + 1) \leqslant 32(1 - \delta)^d.$$

Combining everything, we get that

$$\begin{split} \mathsf{Stab}_{\rho}(f) \leqslant \mathsf{Stab}_{\rho}(f') + O_{\rho}(\delta) \leqslant \mathop{\mathbb{E}}_{z \sim N(0,I_n)} \Big[ \mathsf{Square}(\mathsf{T}_{\sqrt{\rho}}f'(z)) \Big] + O_{\rho}(\delta) + O((1-\delta)^d) \\ \leqslant \mathsf{Stab}_{\rho}(F) + O_{\rho}(\delta) + O((1-\delta)^d) \\ \leqslant 1 - \frac{2}{\pi}\mathsf{Arccos}(\rho) + O_{\rho}(\delta) + O((1-\delta)^d). \end{split}$$

Choosing  $\delta(\rho) > 0$  now so that the first error bound is at most  $\varepsilon$ , and then d so that the second error bound is at most  $\varepsilon/2$ , finishes the proof.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 15

#### Dor Minzer

Our next topic will be applications of results from analysis of Boolean functions in the field of hardness of approximation. Our goal will be to show that assuming a conjecture in complexity theory known as the Unique-Games Conjecture, the best known efficient approximation algorithms for the Max-Cut problem, as well as for the Vertex-Cover problem, achieve essentially the best approximation ratio possible by any polynomial time algorithm.

## 1 A brief introduction to complexity theory

Complexity theory studies the boundary between feasible and infeasible for computational problems. Usually, when we say "feasible", we mean that a problem is solvable in polynomial time in the size of the input.

### 1.1 Examples

We consider a few examples here:

**Reachability in graphs.** Consider the problem in which one is given as input a graph G=(V,E) and two vertices  $s,t\in V$ . The goal is to decide whether the graph contains a path from s to t. The size of the input here is O(|V|+|E|), and this problem can be solved in linear time (for example by either the BFS or DFS algorithms).

**Matrix invertibility.** Suppose we are given a matrix  $A \in \mathbb{F}_2^{n \times n}$  as input, and we wish to decide whether A is invertible or not. This problem can be solved using Gaussian elimination, which takes  $O(n^3)$  time, which is polynomial in the input size (which is  $O(n^2)$ ).

**Bipartiteness.** Suppose we are given a graph G=(V,E), and we wish to decide if G is bipartite or not. I.e., we want to decide whether there is a partition  $V=A\cup B$  of the vertices into two sets, such that all edges go across them. At first sight, it's not clear whether one can solve this problem efficiently or not; one attempt is to go over all possible bipartitions A,B, but this takes time  $O(2^n)$ , which is exponential. Upon further inspection though, there is an alternative easy algorithm: start with  $A=B=\emptyset$ , and take any vertex  $v\in V$  arbitrarily and put it in A. Now put all the neighbours of v in B; now in each step, take a vertex from either A or B, and put all of its neighbours in the other part. If we ever reach a contradiction – we say the graph is not bipartite, otherwise we find a bipartition this way. Furthermore, the running time of this algorithm is O(|V|+|E|).

**3-SAT.** A 3-CNF formula is a formula of the form  $\phi = (x_1 \lor x_2 \lor \overline{x_3}) \land (x_2 \lor \overline{x_{17}} \lor x_{11}) \land \ldots \land (x_1 \lor x_8 \lor x_{11})$ . I.e., we have *n*-variables  $x_1, \ldots, x_n$ , and  $\phi$  is an AND of *m*-clauses, each clause containing an OR over 3 literals (a literal is a variable of its negation). The input in the 3-SAT problem is to decide, given a 3-CNF formula  $\phi$ , whether it is satisfiable or not. I.e., whether there is an assignment of 0, 1 values to the variables that satisfies all of the clauses of  $\phi$ .

Clearly, there is an easy algorithm that runs in time  $O(m2^n)$  that solves the 3-SAT problem; slightly faster algorithms with running time  $2^{\gamma n}$  where  $\gamma < 1$  are known, but the best known algorithms for this problem still have exponential running time. It is widely believed that there are no polynomial time algorithms for this problem (this is equivalent to the  $P \neq NP$  conjecture), but currently it is not even known how to rule out the existence of algorithms with running time  $O(n \log^{10} n)$ .

**Maximum Cut.** The Max-Cut problem is a generalization of the bipartiteness problem above. Given a graph G=(V,E), one wants to find the bipartition V=(A,B) that maximizes the number of edges that cross this bipartition. We note that the formulation of the problem we have here differs from the formulation of the problems above; the above problems were phrased as "decision problems" wherein the output is either 0 or 1 depending on whether the input satisfies a certain condition or not. Here, we have phrased the problem as an optimization problem, and one can state a decision analog of this problem. In this case, it is also not known how to solve this problem efficiently, and it is again suspected that it is in fact impossible.

**Minimum Vertex-Cover.** Given a graph G=(V,E), a vertex cover  $C\subseteq V$  is a set of vertices that touches each edge  $e\in E$ , i.e. it contains at least one of its endpoints. The goal in the Minimum Vertex-Cover problem is, given a graph G=(V,E), find the smallest vertex-cover in it. We do not know how to solve this problem efficiently, and again suspect that it is impossible.

#### 1.2 NP-hardness

The above examples already give a taste of a theme going on in complexity theory. In order to evidence the feasibility of a computational problem, "all" one to do is demonstrate an efficient algorithm for it. How can one prove that there is *no* efficient algorithm for a problem though? After all, general computation may be very complex and do a whole bunch of clever manipulations that are not immediately evident. You can even think of the problem of proving mathematical theorems this way; given a statement, finding a proof for it may be a highly non-trivial task. Mostly for this reason, there are no results of this form (this is known as "proving lower bounds" in computational complexity), and we only know how to argue about very limited models of computation.

Still though, we would like to gain confidence to support our belief that there is no efficient algorithm exists for problems such as 3-SAT, Maximum-Cut, or Minimum Vertex-Cover. The main way complexity theorist do things along these lines is by the means of *reductions*, which we shortly explain. But before that, let's state a theorem that reductions are able to establish.

**Theorem 1.1.** Suppose there exists an efficient algorithm for the Max-Cut problem (or the Minimum Vertex-Cover problem). Then there exists an efficient algorithm for the 3-SAT problem.

In fact, the reverse direction also holds. If there is an efficient algorithm for 3-SAT, then there is also an efficient algorithm for the Max-Cut problem as well as for the Minimum Vertex-Cover. In other words, as far as polynomial algorithms are concerned, these problems are in the same basket. Loosely speaking,

<sup>&</sup>lt;sup>1</sup>We will not give a comprehensive treatment of these distinctions in this course.

this points out that the "root cause" we were unable to find an efficient algorithm for each of these problems is the same. This is the beginning of the theory of NP-completeness and NP-hardness which started out in the 70's. Formally, we say a problem is NP-hard, if assuming we have an efficient algorithm for it, we can construct an efficient algorithm for the 3-SAT problem; in this language, the above theorem simply states that Max-Cut and Minimum Vertex-Cover are NP-hard.

#### 1.3 Coping with NP-hardness

The fact that NP-hard problems are something people face very often, both in theory and in practice, has led researchers to consider ways to handle such problems. For example, can one find sub-classes of instances of 3-SAT that occur in some area (say, formal verification of programs), and show that for this class of instances there is an efficient algorithm? This is one way to cope with NP-hardness that people do look at which we will not discuss further.

Another option is to relax our notion of what it means to solve a problem. Namely, suppose we have a 3-CNF formula which is satisfiable, but instead of finding an assignment that satisfies all of the clauses, we manage to find an assignment satisfying at least 99% of the clauses. In many cases, this will be almost as good, so it makes sense to ask whether this is possible or not. This leads us to discuss *approximation problems*.

## 2 Approximation problems

We move on to discuss approximation versions of some of the problems we have presented thus far.

### 2.1 Approximately solving 3-SAT

Suppose we are given a 3-CNF formula  $\phi$  and we are promised there is a satisfying assignment. What is the best assignment we can find efficiently? The most obvious thing to try is a random assignment: for each i, take  $x_i$  as uniform bit. Note that the probability a clause is satisfied is at least 7/8, and so in expectation a random assignment satisfies at least 7/8m clauses. This observation can easily be turned into an efficient algorithm (we will not do it explicitly here). Further note that we managed to satisfy 7/8m clauses without even using the fact that  $\phi$  was satisfiable. Can we do any better?

### 2.2 Approximately solving Vertex-Cover

Suppose we have a graph G = (V, E), and we are promised that there is a vertex-cover of size  $\gamma n$ . What is the smallest vertex cover we can find efficiently?

**Claim 2.1.** There is an efficient algorithm that finds a vertex-cover of size at most  $2\gamma n$ .

*Proof.* The algorithm starts with  $C = \emptyset$ , and E' = E. At each step, the algorithm takes some edge  $e \in E'$ , adds both of its endpoints to C, and then removes from E' all edges that contain at least one of these vertices as endpoints.

Clearly this is an efficient algorithm, and next we argue that  $|C| \leq 2\gamma n$  in the end of the algorithm. Let  $\tilde{C}$  be any other vertex cover of G. Note that at each time we add vertices to C,  $\tilde{C}$  must contain at least one of these vertices (otherwise it wouldn't cover the edge we inspected), so we get that  $|C| \leq 2 \ \tilde{C}$ .

Thus, we can find a 2-approximation for Vertex-Cover. Can we do any better?

### 2.3 Approximately solving Max-Cut

Suppose we have a graph G=(V,E), and we are promised that there is a cut of size  $(1-\varepsilon)m$ . What is the largest cut we can find efficiently? Choosing a bipartition  $V=A\cup B$  uniformly, one can show that the expected number of edges that go across it is  $\frac{1}{2}m$ , and this again can be turned into a  $\frac{1}{2}$ -approximation algorithm. Can we do any better?

#### 3 The PCP theorem

In order to answer questions regarding the feasibility and infeasibility for approximation problems, one has to extend the theory of NP-hardness to the realm of approximation problems. This is the type of problems that are handled in the field of hardness of approximation, which essentially started with a result known as the PCP theorem. The theorem has several equivalent formulations, one of which is the following formulation using the notion of gap problems we introduce next.

Let  $0 \le s < c \le 1$ . The gap-3SAT[c, s] problem is the promise problem wherein one is given a 3SAT instance  $\phi$ , which is promised to belong in one of the following cases:

- 1. **YES case**: there is an assignment to  $\phi$  satisfying at least c fraction of the clauses in  $\phi$ .
- 2. **NO case**: no assignment satisfies more than s fraction of the clauses in  $\phi$ .

The goal in the problem is distinguish which one of these cases does the given instance belong to.

Intuitively, the reason to consider such problems is that they give a convenient formalism that captures approximation; if one cannot even distinguish between formulas that are c-satisfiable and s-satisfiable, then one can certainly not approximate the 3-SAT problem within factor s/c.

The notion of gap problems can be applied to general optimization problem, and we will indeed use it in order to study the complexity of approximation problems.

**Theorem 3.1** (The PCP Theorem). There exists s < 1, such that gap-3SAT[1, s] is NP-hard.

We will not prove this theorem in this course (it may well take us several lectures to do so). Instead, we will outline some applications of this result, and give some hint as to how analysis of Boolean functions enters the picture in such problems.

### 3.1 Implications of the PCP theorem

Starting out with the PCP theorem, one can prove a host of hardness of approximation results. For example, one can show that the 7/8 approximation algorithm we had for the 3SAT problem is essentially tight:

**Theorem 3.2** (Håstad 97'). For all 
$$\varepsilon > 0$$
, gap-3SAT  $\left[1, \frac{7}{8} + \varepsilon\right]$  is NP-hard.

One can also prove some hardness results for the other two problems we've discussed, though in this case the hardness result don't quite match the algorithms we've seen.

**Theorem 3.3** (Håstad, Trevisan-Sorkin-Sudan-Williamson 00'). *It is NP-hard to approximate the Max-Cut problem within factor*  $\frac{16}{17}$ .

Despite much effort, this NP-hardness result still stands as best to date.

**Theorem 3.4** (Dinur-Safra 02'). It is NP-hard to approximate the Minimum Vertex-Cover problem within factor 1.36.

Here, better NP-hardness results have been recently proved, and currently stand at  $\sqrt{2}-o(1)$ .

### 3.2 The Unique-Games Conjecture

So how does one make progress on these problems in order to determine the approximation ratio wherein these problems become computationally infeasible? To remedy this situation, Khot observed in a 2002 that if a "dream version" of the PCP theorem was proved, then it is conceivable that one could make progress on these problems. Towards this end, Khot formulated a conjecture called the Unique-Games Conjecture, asserting that a dream version of the PCP theorem holds. To state this conjecture, we first have to define the Unique-Games problem.

**Definition 3.5.** An instance of Unique-Games, denoted by  $\Psi$ , is composed of a bipartite, bi-regular graph  $G = (V = L \cup R, E)$ , a finite alphabet  $\Sigma$ , and a collection of constraints  $\Phi = (\phi_e)_{e \in E}$ ) one for each edge. Each one the constraint  $\phi_e$  is a 1-to-1 map,  $\phi_e \colon \Sigma \to \Sigma$ .

For an edge e, the constraint  $\phi_e$  defines a collection of tuples which are deemed as satisfactory assignments to the endpoints of the edge, which is  $\{(\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma\}$ .

The goal in Unique-Games is to find an assignment  $A: V \to \Sigma$  that satisfies as many of the constraints  $\phi_e$ . The value of a Unique-Games instance, denoted by val $(\Psi)$ , is defined to be

$$\max_{A:\ V\to\Sigma} \frac{\#\{e\mid A \text{ satisfies } \phi_e\}}{|E|},$$

i.e. the maximum fraction of constraints that can be satisfied by any assignment.

It is easy to see that given a Unique-Games instance  $\Psi$  promised to have  $val(\Psi) = 1$ , one can efficiently find an assignment that satisfies all of the constraints in  $\Psi$  (how?). What about if we are only given the weaker promise that  $val(\Psi) \geqslant 0.99$ ? The previous algorithm clearly breaks, and Khot conjectured that in this case it is hard to find a really good assignment.

**Conjecture 3.6** (The Unique-Games Conjecture). For all  $\varepsilon, \delta > 0$ , there exists  $k \in \mathbb{N}$  such that given a Unique-Games instance  $\Psi$ , it is NP-hard to distinguish between:

- 1. **YES case**:  $val(\Psi) \ge 1 \varepsilon$ .
- 2. **NO case**:  $val(\Psi) \leq \delta$ .

*In other words, gap-UniqueGames*<sub>k</sub> $[1 - \varepsilon, \delta]$  *is NP-hard.* 

Khot initially showed that if (a variant of this) conjecture is true, then Vertex-Cover is hard to approximate within factor  $\sqrt{2} - o(1)$ . Shortly after proposing this conjecture, researchers have realized that using Unique-Games as a starting problem, one can show tight inapproximability result for a wide range of computational problems. Furthermore, such results are intimately related to analysis of Boolean functions, and often reduce to proving some results about Boolean functions. In fact, some of the results that we've seen in this course were directly motivated by such applications.

Indeed, in this course we will see 2 implications of the Unique-Games Conjecture, namely to the problem of determining the complexity of approximating the Minimum Vertex-Cover and the Maximum Cut.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 16

#### Dor Minzer

In this lecture, we will discuss the Max-Cut problem in more detail. We will show the Goemans-Williamson algorithm, and show that assuming the Unique-Games Conjecture presented last time, this algorithm is tight.

# 1 The Goemans-Williamson algorithm

Recall that last time, we have seen a  $\frac{1}{2}$ -approximation algorithm for the Max-Cut problem. In 1995, Goemans and Williamson showed that (surprisingly), this simple algorithm is not optimal, and that there is a better approximation algorithm that achieves  $\alpha_{GW} \approx 0.87856$  times the optimum in this problem. Their algorithm is very geometric in spirit, and is a prominent example of the use of semi-definite programming relaxations in order to solve optimization problems.

### 1.1 The integer programming relaxation

We first phrase the Max-Cut problem as an integer program. For each vertex  $v \in V$  we create a variable  $x_v$ , whose value is supposed to be in  $\{-1,1\}$ . The idea is that  $x_v=1$  will represent that v is on the left side, and  $x_v=-1$  will represent that v is on the right side. Thus, if  $(u,v) \in E$ , then  $x_u x_v=-1$  iff (u,v) crosses the cut, and otherwise  $x_u x_v=1$ . Therefore, the following program solves Max-Cut

$$\label{eq:max} \begin{array}{ll} \max & \frac{1}{2} \sum_{(u,v) \in E} 1 - x_u x_v \\ \text{subject to} & x_v \in \{-1,1\} & \forall v \in V. \end{array}$$

However, integer programming is NP-hard in general. Hence it seems that making this formulation doesn't advance us anywhere. That being said, this formulation does motivate us to look at higher dimensional, *semi-definite program* formulation of the problem (SDP).

#### 1.2 The semi-definite programming relaxation

In the SDP formulation of the problem, instead of having a sign  $\pm 1$  for each  $x_u$ , we allow  $x_u$  to take any value in the unit ball in  $\mathbb{R}^m$  (where m has to be chosen appropriately).

$$\max \qquad \frac{1}{2} \sum_{(u,v) \in E} 1 - \langle x_u, x_v \rangle$$
 subject to  $\|x_v\|_2 = 1$   $\forall v \in V$ .

The good feature of this program, is that one can solve this optimization problem now. <sup>1</sup> The bad feature of this program is that a solution no longer gives us a cut; at least not in a straight-forward. But now we get to

<sup>&</sup>lt;sup>1</sup>At least approximately, and thanks to the convexity that this has introduced to the problem. This is really an optimization problem over the cone of PSD matrices; the matrix here is the matrix of inner products  $J = (\langle x_u, x_v \rangle)_{u,v \in V}$ . We will not elaborate on this fact further in this course.

the amazing part: one can actually take a vector solution to the SDP program, and salvage from it a pretty good cut!

Here's the idea. Suppose the optimum size of the cut in our graph G is  $\rho |E|$ , where  $\rho \in [1/2, 1]$ , and let  $\{x_v\}_{v \in V}$  be a solution to SDP program. First, it is clear that the optimum of the SDP program is at least  $\rho |E|$  (why?), so in particular

$$\frac{1}{2} \sum_{(u,v) \in E} 1 - \langle x_u, x_v \rangle \geqslant \rho |E|.$$

We now generate a randomized cut from the vector solution. Take a random vector h from the unit ball in  $\mathbb{R}^m$ , and define

$$L = \{ v \mid \langle x_v, h \rangle \leqslant 0 \}; \qquad R = \{ v \mid \langle x_v, h \rangle > 0 \}.$$

Our goal is to analyze the expected number of edges that crosses the cur (L,R). Fix an edge  $(u,v) \in E$ ; then the probability that (u,v) is cut is  $\theta_{u,v}/\pi$ , where  $\theta_{u,v}$  is the angle between u and v. Thus, by linearity of expectation the expected size of the cut is

$$\sum_{(u,v)\in E} \frac{\theta_{u,v}}{\pi} = \sum_{(u,v)\in E} \frac{\operatorname{Arccos}(\langle x_u,x_v\rangle)}{\pi} \geqslant \sum_{(u,v)\in E} \alpha_{GW} \left(1-\langle x_u,x_v\rangle\right) \geqslant \alpha_{GW} \rho \left|E\right|.$$

Here,  $\alpha_{GW}=\min_{z\in[-1,1]}\frac{\mathrm{Arccos}(z)/\pi}{(1-z)/2}\approx0.878\ldots$ ; given this expectation calculation, standard tools allows one to design an approximation algorithm that achieves this approximation ratio.

Note that the calculation that we did here is earily similar to the calculation we did to compute the stability of the majority function. This turns out not to be a coincidence, as we will see later on in this lecture.

#### 1.3 The Goemans-Willaimson algorithm for almost bipartite graphs

With a more careful analysis, one can show that if the original size of the cut was very large, say  $\rho = 1 - \varepsilon$  for small  $\varepsilon$ , then the above analysis could be significantly improve.

**Theorem 1.1.** Suppose G=(V,E) has a cut of size  $(1-\varepsilon)|E|$ . Then the expected size of the cut in the Goemans-Williamson algorithm is at least  $\left(1-\frac{2}{\pi}\sqrt{\varepsilon}-O(\varepsilon^{1.5})\right)|E|$ .

#### 2 A hardness result for Max-Cut

In this section, we prove the following result due to Khot, Kindler, O'Donnell and Mossel.

**Theorem 2.1.** Assuming the Unique-Games Conjecture, for all  $\rho \in (0,1)$  and  $\varepsilon > 0$ , given a graph G = (V, E) it is NP-hard to distinguish between the following two cases:

- 1. **YES case**: G has a cut of fractional size at least  $\frac{1}{2} + \frac{1}{2}\rho \varepsilon$ .
- 2. **NO case**: all cuts in G have fractional size at most  $1 \frac{1}{\pi} Arccos(\rho) + \varepsilon$ .

In gap notations, gap-MaxCut $[\rho, 1 - \operatorname{Arccos}(\rho) + \varepsilon]$  is NP-hard for all  $\rho \in (0, 1)$ ,  $\varepsilon > 0$ , assuming the Unique-Games Conjecture. Choosing  $\rho = -z$  where achieves the minimum in the definition of  $\alpha_{GW}$  (z turns out to be negative), this theorem implies the optimality of the Goemans-Williamson algorithm.

To prove this theorem we shall use gap preserving reductions. First, recall the statement of UGC:

**Definition 2.2.** An instance of Unique-Games, denoted by  $\Psi$ , is composed of a bipartite, bi-regular graph  $G = (V = L \cup R, E)$ , a finite alphabet  $\Sigma$ , and a collection of constraints  $\Phi = (\phi_e)_{e \in E}$ ) one for each edge. Each one the constraint  $\phi_e$  is a 1-to-1 map,  $\phi_e \colon \Sigma \to \Sigma$ .

For an edge e, the constraint  $\phi_e$  defines a collection of tuples which are deemed as satisfactory assignments to the endpoints of the edge, which is  $\{(\sigma, \phi_e(\sigma)) \mid \sigma \in \Sigma\}$ .

**Conjecture 2.3** (The Unique-Games Conjecture). For all  $\eta > 0$ , there exists  $k \in \mathbb{N}$  such that given a Unique-Games instance  $\Psi$ , it is NP-hard to distinguish between:

- 1. **YES case**:  $val(\Psi) \geqslant 1 \eta$ .
- 2. **NO case**:  $val(\Psi) \leq \eta$ .

In other words, gap-UniqueGames $_k[1-\varepsilon,\delta]$  is NP-hard.

We will show a polynomial time procedure  $M \colon \Psi \to G$ , that given an instance  $\Psi$  of Max-Cut, produces a graph G, such that:

- 1. If  $\operatorname{val}(\Psi) \geqslant 1 \eta$ , then G has a cut of fractional size at least  $\frac{1}{2} + \frac{1}{2}\rho \varepsilon$ .
- 2. If  $\operatorname{val}(\Psi) \leqslant \eta$ , then all cuts in G have fractional size at most  $1 \frac{1}{\pi} \operatorname{Arccos}(\rho) + \varepsilon$ .

In particular, once we show this procedure, this proves Theorem 2.1 (why?). This is the type of reductions that most often appear in TCS.

#### 2.1 Dictatorship vs no-influential-coordinates paradigm

A basic paradigm to prove hardness of approximation results proceeds by constructing instances of the problem we're interested in over the Boolean cube, wherein good solutions corresponds to dictatorship functions, whereas any function that only has small individual influences is automatically guaranteed to not be a good solution. In our case, we would like to design a (weighted) graph over  $\{-1,1\}^n$ , such that

- 1. For any  $i \in [n]$ , the dictatorship cut, i.e.  $L = \{x \mid x_i = 1\}$ ,  $R = \{x \mid x_i = -1\}$ , contains many edges.
- 2. If  $f: \{-1,1\}^n \to \{-1,1\}$  is balanced, and has no influential coordinates, then the cut that it defines does not contain many edges.

So how would we design such graph in this case? Let  $\rho > 0$  be a parameter, best thought of as close to 1, i.e.  $\rho = 1 - \varepsilon$ . We look at the graph corresponding to  $-\rho$  correlated points, i.e. for each  $x \in \{-1,1\}^n$ , the distribution over its neighbours is the distribution  $T_{-\rho}x$ .

- 1. For any  $i \in [n]$ , the dictatorship cut, i.e.  $L = \{x \mid x_i = 1\}$ ,  $R = \{x \mid x_i = -1\}$  contains edges of total weight  $\frac{1}{2} + \frac{1}{2}\rho$  (why?).
- 2. If  $f: \{-1,1\}^n \to \{-1,1\}$  is balanced odd function, and has no influential coordinates, then the size of the cut is

$$\Pr_{\substack{x \\ y \sim T_{-\rho}x}} \left[ f(x) \neq f(y) \right] = \frac{1}{2} (1 - \mathsf{Stab}_{-\rho}(f)) = \frac{1}{2} + \frac{1}{2} \mathsf{Stab}_{\rho}(f) \leqslant \frac{1}{2} + \frac{1}{2} \left( 1 - \frac{2}{\pi} \mathsf{Arccos}(\rho) \right) + o(1),$$

which is equal to  $1 - \frac{1}{\pi} \text{Arccos}(\rho) + o(1)$ . Here, we used the Majority is Stablest theorem.

Thus, using the Majority is Stablest theorem we managed to construct a graph on the Boolean cube wherein dictators correspond to good cuts, and functions that have no influential coordinates correspond to bad cuts. In the rest of this lecture, we will see how to transfer this construction into a hardness result, assuming UGC.

## 2.2 A reduction from Unique-Games to Max-Cut

We are now ready to present the reduction. Let  $\rho=1-\varepsilon$ . Starting with a bi-partite UG instance  $\Psi=(V\cup U,E,\Sigma,\Phi)$ , we wish to construct a Max-Cut instance with the properties described above. The idea will be to introduce, for each vertex  $v\in V$  a separate hybercube  $\{-1,1\}^{\Sigma}$ , and using a cut in that hypercube to encode the label that v is supposed to get in  $\Psi$ . More specifically, we will want to associate with each label  $\sigma$  of v which is supposed to have high value; this will be the dictatorship cut, i.e. the cut defined by  $f_v(x)=x_{\sigma}$ . Once we do that, we will be able to argue that if  $\Psi$  has a good assignment, then the graph we produce G will have a large cut corresponding to the dictatorship functions in each hypercube.

To ensure soundness, we must take care of two potential issues:

- 1. Penalizing cuts that are defined by functions that do not "resemble" any dictatorship. We have already dealt with this issue the last section, wherein we argued that in that case the cut size would be at most  $1 \frac{1}{\pi} \mathsf{Arccos}(\rho) + o(1)$  if f does not have any coordinate with significant low-degree influence.
- 2. Penalizing violating the constraints of  $\Psi$ . Namely, suppose we have two vertices  $v \in V$ ,  $u \in U$  that have an edge between them, and they have been assigned by dictatorship functions  $f_v(x) = x_{\sigma_v}$ ,  $f_u(x) = y_{\sigma_u}$ , but  $\sigma_v, \sigma_u$  do not satisfy the constraint between v and u in  $\Psi$ . In that case, we would want to penalize this cut, as it does not correspond to a good assignment in  $\Psi$ . To deal with this issue, our edges will not really be inside the hypercube of each vertex v, but rather across hypercubes. For that, it is important to note that there is a natural bijection between the hypercube of v and the hypercube of v respecting the constraint between them, which is simply v0 where v1 where v2 where v3 where v3 where v4 where v5 where v6 and the hypercube of v6 are specting the constraint between them, which is simply v6 where v8 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9 where v9

This almost finishes the informal overview of the reduction, except that if we were to execute the plan as is, we would get a bipartite graph (the sides being the hypercubes of V and the hypercubes of U), and to remedy that we only leave one of these sides alive, and take two steps in the graph of  $\Psi$  instead of one.

We now proceed to the formal construction of the reduction. Given  $\Psi = (V \cup U, E, \Sigma, \Phi)$ , we construct a weighted max-cut instance G = (V', E', w) as follows.

- The vertices: For each  $v \in V$  we construct a cube over  $\Sigma$ ,  $\{v\} \times \{-1,1\}^{\Sigma}$ , which we refer to as the long-code of v. A  $\pm 1$  assignment to these vertices should be thought as a potential encoding one of the labels in  $\Sigma$  for v.
- The edges are weighted according to the following randomized process. Sample  $u \in U$  and  $v, v' \in V$  two neighbours of u independently. Let x be a uniformly chosen vector from  $\{-1,1\}^{\Sigma}$ , and sample  $y \sim T_{-\rho}x$ . Consider the points

$$z = \phi_{u,v}(x),$$
  $z' = \phi_{u,v'}(y),$  where  $\phi_{u,v}(y)_{\sigma} = y_{\phi_{(u,v)}(\sigma)} \, \forall \sigma \in \Sigma.$ 

The edge output by the process is (z, z').

We prove the following lemma, encapsulating the analysis of the reduction.

**Lemma 2.4.** For all  $\rho \in (0,1)$ ,  $\delta > 0$  there is  $\eta > 0$  such that:

- 1. Completeness: if  $\Psi$  is at least  $1-\eta$  satisfiable, then there is a cut in G of weight at least  $\frac{1}{2}(1+\rho)-\delta$ .
- 2. Soundness: if  $\Psi$  is at most  $\eta$  satisfiable, then G has no cut whose weight exceeds  $1 \frac{1}{\pi}\mathsf{Arccos}(\rho) + \delta$ .

#### 2.3 Analysis of the reduction

We now analyze the construction. First, we show the completeness of the construction, asserting that if  $\Psi$  is highly satisfiable, then there exists a large cut on the graph we have constructed.

#### **Completeness**

Suppose there is a coloring  $A \colon V \cup U \to \Sigma$  satisfying at least  $1 - \eta$  fraction of the edges. We assign  $\pm 1$  values to the cube of v according to the dictatorship assignment of A(v). Namely, we define the cut in the graph G by

$$f(v, x) = x_{A(v)}$$
 for  $(v, x) \in V \times \{-1, 1\}^{\Sigma}$ .

We analyze the weight of the cut defined by f. Looking at the process describing the weights of the edges in G', Since the graph of  $\Psi$  is regular, the marginal distribution of each one of the edges (u,v),(u,v') is uniform; therefore the probability one of them is not satisfied by A is at most  $2\eta$ , so with probability at least  $1-2\eta$  both edges are satisfied.

Sample x, y as in the process, and look at  $\phi_{(u,v)}(x), \phi_{(u,v')}(y)$ . Note that  $y_{A(u)} \neq x_{A(u)}$  with probability  $\frac{1}{2} + \frac{1}{2}\rho$ , and if that happens, since both edges (u,v) and (u,v') are satisfied, we get that

$$f(v,z) = z_{A(v)} = z_{\phi_{u,v}(A(u))} = x_{A(u)} \neq y_{A(u)} = z'_{\phi_{u,v}(A(u))} = f(v,z').$$

We conclude that the weight of edges crossing the cut is at least  $\frac{1}{2} + \frac{1}{2}\rho - 2\eta$ .

#### **Soundness**

In this part, we show that if the UG instance  $\Psi$  had no good satisfying assignments then the graph G does not have a large cut. This is usually done (and so will be our case) in a counter-positive way. Assuming we have a large cut in the graph, we will construct a good assignment for  $\Psi$ .

Let  $f: V \times \{-1,1\}^{\Sigma} \to \{-1,1\}$  be a function corresponding to a large cut, that is a cut of size at least  $\frac{1}{\pi} \mathsf{Arccos}(\rho) + \delta$ . The fractional size of the cut is exactly

$$\Pr_{\substack{u,v,v'\\x,y,z,z'}} \left[ f(v',z) \neq f(v,z) \right].$$

Let  $\nu$  be a vector from  $\{-1,1\}^{\sigma}$  such each coordinate is -1 with probability  $\frac{1}{2}(1-\rho)$ . Then the previous probability is the same as

$$\Pr_{\substack{u,v,v'\\x,\nu}} \left[ f(v,\phi_{(u,w)}x) \neq f(v',\nu \cdot \phi_{(u,w')}x) \right].$$

Define for  $u \in U$ ,  $v \in V$ 

$$g_u(x) = \underset{v:(u,v) \in E}{\mathbb{E}} \left[ f(v, \phi_{(u,v)}x) \right], \qquad g_v(x) = f(v,x).$$

Intuitively, u asks his neighbours what side it should be on, and takes the average of the suggestions. Then

$$\Pr_{\substack{u,v,v'\\x,\nu}} \left[ f(v,\phi_{(u,w)}x) \neq f(v',\nu \cdot \phi_{(u,w')}x) \right] = \frac{1}{2} \left( 1 - \underset{\substack{u,v,v'\\x,\nu}}{\mathbb{E}} \left[ f(v,\phi_{(u,w)}x)f(v',\nu \cdot \phi_{(u,w')}x) \right] \right) \\
= \frac{1}{2} \left( 1 - \underset{\substack{u\\x,\nu}}{\mathbb{E}} \left[ \underset{v}{\mathbb{E}} \left[ f(v,\phi_{(u,w)}x) \right] \underset{v'}{\mathbb{E}} \left[ f(v',\phi_{(u,w')}(\nu \cdot x)) \right] \right] \right) \\
= \frac{1}{2} \left( 1 - \underset{\substack{u\\x,\nu}}{\mathbb{E}} \left[ g_u(x)g_u(\nu \cdot x) \right] \right) \\
= \frac{1}{2} \left( 1 - \underset{\substack{u\\x,\nu}}{\mathbb{E}} \left[ \operatorname{Stab}_{-\rho}[g_u] \right] \right).$$

We conclude that since the fractional size of the cut is at least  $1 - \frac{1}{\pi} Arccos(\rho) + \delta$ , it holds that

$$\mathop{\mathbb{E}}_{u}\left[\mathsf{Stab}_{-\rho}[g_{u}]\right] < \frac{2}{\pi}\mathsf{Arccos}(\rho) - 1 - 2\delta.$$

Therefore for at least  $\delta$  fractional of the u's,  $\mathsf{Stab}_{-\rho}[g_u] < 1 - \frac{2}{\pi}\mathsf{Arccos}(\rho) - \delta$ . We need a version of the Majority is Stablest theorem for negative correlation parameters.

**Theorem 2.5.** For all  $\rho \in (0,1)$ ,  $\delta > 0$  there exist  $d \in \mathbb{N}$ ,  $\tau > 0$  such that if  $f : \{-1,1\}^n \to [-1,1]$  is a function for which  $\max_i I_i^{\leqslant d}[f] \leqslant \tau$ , then

$$\mathsf{Stab}_{-\rho}(f)\geqslant \frac{2}{\pi}\mathsf{Arccos}(\rho)-1-\delta.$$

*Proof.* Let  $f_{\text{odd}}$  be the odd part of f. Then  $f_{\text{odd}}$  is balanced and we have by the Fourier expression for stability that  $\mathsf{Stab}_{-\rho}(f) \geqslant \mathsf{Stab}_{-\rho}(f_{\text{odd}}) = -\mathsf{Stab}_{\rho}(f_{\text{odd}})$ . By the Majority is stablest theorem we get that for appropriate choice of d,  $\tau$ ,  $\mathsf{Stab}_{\rho}(f_{\text{odd}}) \leqslant 1 - \frac{2}{\pi}\mathsf{Arccos}(\rho) + \delta$ .

We fix  $d, \tau$  corresponding to  $\rho, \delta$  as in Theorem 2.5 and apply it to get that there is i such that  $I_i^{\leq d}[g_u] \geqslant \delta$ . We call such u good. Define

$$\operatorname{List}_{\xi}(v) = \left\{ i \mid I_i^{\leqslant d}[g_v] \geqslant \xi \right\}.$$

Since the sum of the d degree influence is at most d,  $|\text{List}S(v)| \leq d/\xi$ ; the important point is that this quantity only depends on  $\rho, \varepsilon$  (and not on  $|\Sigma|$ ). We finish by showing that if u is good and  $i \in \text{List}_{\delta}(u)$ , then a non-negligible fraction of his neighbours v have  $\phi_{(u,v)}(i) \in \text{List}_{\delta/2}(w)$ 

$$\begin{split} I_i^{\leqslant d}[g_u] &= \sum_{S: i \in S, |S| \leqslant d} \widehat{g_u}^2(S) \\ &= \sum_{S: i \in S, |S| \leqslant d} \mathop{\mathbb{E}}_{v: (u,v) \in E} \left[ \widehat{g_v}(\phi_{(u,v)}S) \right]^2, \end{split}$$

where we used the definition of low degree influence and the following simple lemma

Lemma 2.6. 
$$\widehat{g_u}(S) = \mathbb{E}_{w:(u,w)\in E}\left[\widehat{g_w}(\phi_{(u,w)}S)\right]$$
.

We continue by using Jensen

$$\begin{split} I_{i}^{\leq d}[g_{u}] \leq \sum_{S:i \in S, |S| \leq d} \mathbb{E}_{v:(u,v) \in E} \left[ \widehat{g_{v}}(\phi_{(u,v)}S)^{2} \right] &= \mathbb{E}_{v:(u,v) \in E} \left[ \sum_{S:i \in S, |S| \leq d} \widehat{g_{v}}(\phi_{(u,v)}S)^{2} \right] \\ &= \mathbb{E}_{v:(u,v) \in E} \left[ \sum_{T:\phi_{(u,v)}(i) \in T, |T| \leq d} \widehat{g_{v}}(T)^{2} \right] \\ &= \mathbb{E}_{v:(u,v) \in E} \left[ I_{\phi_{(u,v)}(i)}^{\leq d} \left[ g_{v} \right] \right]. \end{split}$$

From  $I_i^{\leq d}[g_u] \geqslant \delta$  and the above it follows that for at least  $\delta/2$  fraction of the v neighbours of u it holds that  $I_{\phi_{(u,v)}(i)}^{\leq d}[g_v] \geq \delta/2$ , or in other words  $\phi_{(u,v)}(i) \in \mathsf{List}(v)$ .

#### Randomized assignment to the Unique-Games instance

Now we finish the proof. For each good  $u \in U$  assign a label  $i \in \mathsf{List}_{\delta}(u)$  randomly, and for each  $v \in V$  assign a label from  $\mathsf{List}_{\delta/2}(v)$  randomly. We now lower the probability a randomly chosen edge from  $\Psi$  is satisfied.

Choose (u,v) randomly. With probability at least  $\delta$ , the vertex u is good, and conditioned on that with probability at least  $\delta/2$ ,  $\operatorname{List}_{\delta/2}(v)$  is not empty. We know that it has at most  $2d/\delta$  elements and at least one of them matches label we assigned to u, and hence the probability the edge is satisfied conditioned on the previous events happening it at least  $\frac{1}{2d/\delta} = \delta/2d$ . We conclude that the probability that a random edge is satisfied is at least

$$\delta \cdot \frac{\delta}{2} \cdot \frac{\delta}{2k} > \eta,$$

in contradiction to the fact we started with a NO case instance of Unique-Games.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.218 Topics in Combinatorics Spring 2021 – Lecture 17

#### Dor Minzer

In this lecture, we will discuss the Vertex-Cover problem in greater detail, and prove that the simple 2-approximation algorithm we have seen for it is essentially optimal assuming the Unique-Games Conjecture.

## 1 Preliminaries

## 1.1 The independent set problem

For technical reasons, it is more convenient to work with the independent set problem. Given a graph G=(V,E), an independent set in G is a set of vertices  $I\subseteq V$  that contains no edge from E. Noting that a set I is an independent set iff  $V\setminus I$  is a vertex cover, it follows that  $\mathsf{IS}(G)=n-\mathsf{VC}(G)$ , where  $\mathsf{IS}(G)$  denotes the size of the maximum independent set in G, and  $\mathsf{VC}(G)$  denotes the size of the smallest vertex cover in G.

The main result we present here is the following hardness result:

**Theorem 1.1.** Assuming UGC, for all  $\varepsilon > 0$ , given a graph G = (V, E) it is NP-hard to distinguish between the cases:

- 1. **YES case**:  $\mathsf{IS}(G) \geqslant \left(\frac{1}{2} \varepsilon\right) n$ .
- 2. NO case:  $\mathsf{IS}(G) \leqslant \varepsilon n$ .

Using the observation above about the relationship between independent sets and vertex-covers, we have:

**Corollary 1.2.** Assuming UGC, for all  $\varepsilon > 0$ , given a graph G = (V, E) it is NP-hard to distinguish between the cases:

- 1. **YES** case:  $VC(G) \leq (\frac{1}{2} + \varepsilon) n$ .
- 2. NO case:  $VS(G) \ge (1 \varepsilon)n$ .

In particular, it follows from the corollary that assuming UGC, it is NP-hard to approximate the size of the minimum vertex cover up to factor  $\frac{1-\varepsilon}{1/2+\varepsilon}=2-O(\varepsilon)$ , for all  $\varepsilon>0$ . We will henceforth focus our discussion on proving Theorem 1.1.

The proof of the theorem follows the dictatorship testing framework introduced in the previous lecture, and we begin by introducing the two ingredients.

## 1.2 The p-biased Kneser graph

Recall that last time, we used the  $\rho$ -noisy cube to encode dictatorships using cuts. Here, we want to use independent sets in order to encode dictatorships, and we want that a dictatorship will correspond to a large independent set whereas functions that are very far from being dictatorships will correspond to either sets that are not independent or small independent sets. Towards this end, we introduce the p-biased Kneser graph.

**Definition 1.3.** Let  $0 \le p < 1/2$ . The p-biased Kneser graph is a graph whose vertex set is P([n]), and the weight of a set A is  $\mu_p(A) = p^{|A|}(1-p)^{n-|A|}$ . The edges of the graph are  $E = \{(A, B) \mid A \cap B = \emptyset\}$ .

Looking at the Kneser graph, we see that independent sets in it are creatures we have already encountered: they are simply intersecting families. In this language, a dictatorship family is a family of the form  $\mathcal{F} = \{A \mid A \ni i\}$ , and it has p-biased measure p (and it is also the heaviest independent set in the graph). Moreover, we have proved that any independent set in the graph, which is an intersecting family, is nearly contained in a junta. Thus, if it is of non-negligible measure, it must have an influential coordinate. Therefore, at least intuitively, if we have a family of non-negligible measure with no influential variables, we automatically get it is not independent. This observation is what will ultimately give us the gap.

### 1.3 A stronger form of the Unique-Games Conjecture

The second ingredient we need is a stronger form of the Unique-Games Conjecture. Recall that an assignment to a Unique-Game is a labeling  $A \colon V \to \Sigma$ , and we say an assignment satisfies a constraint if it gives the two endpoints of the edge matching labels. A t-assignment is a labeling which assigns to each vertex t possible assignments, i.e.  $A \colon V \to {\Sigma \choose t}$ . We say A satisfies an edge (u, v) if A(u), A(v) contain pairs of labels that are compatible with the constraint of u, v, i.e. if  $A(v) \cap \phi_{u,v}(A(u)) \neq \emptyset$ .

**Definition 1.4** (A strongish form of UGC). For  $\eta > 0$ ,  $t \in \mathbb{N}$  we are given a non-bipartite Unique-Games instance  $\Psi = (X, E, \Sigma, \Phi)$ , and we wish to distinguish between the following two cases:

- 1. **YES case**: there exists  $X' \subseteq X$  of size at least  $(1 \eta)|X|$ , and an assignment  $A: X' \to \Sigma$ , such that A satisfies all of the constraints inside X'.
- 2. **NO case**: for all  $X' \subseteq X$  of size at least  $\eta |X|$  and a t-assignment, i.e.  $A \colon X' \to {\Sigma \choose t}$ , not all of the constraints in X' are satisfied by A.

It turns out that there is a reduction from general Unique-Games to strongish unique games. Namely, one can prove the following result.

**Theorem 1.5.** Assuming UGC, for all  $t \in \mathbb{N}$ ,  $\eta > 0$ , the problem gap-StrongishUG<sub>t</sub>[1 -  $\eta$ ,  $\eta$ ] is NP-hard.

We will not prove this theorem here. Instead, we will show a reduction from Strongish Unique-Games to the Indepednent Set problem.

## 2 The reduction

Fix  $\varepsilon > 0$ , and denote  $p = \frac{1}{2} - \varepsilon$ . Starting with an instance of strongish unique games  $\Psi = (X, E, \Sigma, \Phi)$ , our goal is to produce a (weighted) graph G = (V, w, E') such that: if  $\Psi$  was in the YES case, then G has

an independent set of eight at least  $p - \varepsilon$ , and if  $\Psi$  was in the NO case, then the largest independent set in G has weight at most  $\varepsilon$ .

For each  $x \in X$ , we produce a copy of the Kneser graph over  $\Sigma$ . Namely, our vertices are  $V = X \times P(\Sigma)$  as for the edges, we create edges inside the Kneser graph of each vertex  $x \in X$ , i.e. we insert the edges

$$E_1 = \{ \{(x, A), (x, B)\} \mid x \in X, A, B \subseteq \Sigma, A \cap B = \emptyset \}.$$

We also add edges across the Kneser graphs; the idea is similar to the idea in the last lecture, since we want to ensure compatibility between the encodings given by each Kneser graph. More precisely, we add the edges

$$E_2 = \{ \{(x, A), (x', B)\} \mid x, x' \in X, (x, x') \in E, A, B \subseteq \Sigma, B \cap \phi_{x, x'}(A) = \emptyset$$
.

In words, we add edges between the vertices in the Kneser graphs of x and x' if the two sets do not contain a pair of labels that is compatible with the constraint  $\phi_{x,x'}$ . The set of edges E' is  $E_1 \cup E_2$ .

Finally, the weight of a vertex (x, A) is  $w(x, A) = \frac{1}{|X|} \mu_p(A)$ . This completes the description of the reduction.

We prove the following lemma which summarizes the properties of the reduction.

**Lemma 2.1.** For all  $\varepsilon > 0$ ,  $p = \frac{1}{2} - \varepsilon$  there are  $t \in \mathbb{N}$  and  $\eta > 0$  such that the following holds.

- 1. If  $\Psi$  is from the **YES case** of Strongish Unique-Games, then G has an independent set of weight at least  $p \varepsilon$ .
- 2. If  $\Psi$  is from the **NO** case of Strongish Unique-Games, then the heaviest independent set in G has weight at most  $\varepsilon$ .

This lemma, together with Theorem 1.5, immediately implies Theorem 1.1.

## 3 Analysis of the reduction

We now analyze the reduction.

#### 3.1 Completeness

Suppose there is  $X' \subseteq X$  of size at least  $(1 - \eta)|X|$  and an assignment  $H: X' \to \Sigma$  satisfying all of the constraints in X'. Define

$$I = \{(x, A) \mid x \in X', A \ni H(x) .$$

We claim that I has weight  $p - \eta$  and that I is an independent set. Indeed,

$$w(I) = \sum_{x \in X'} \frac{1}{|X|} \mu_p(\{A \subseteq \Sigma \mid A \ni H(x)\}) = \sum_{x \in X'} \frac{1}{|X|} p = \frac{|X'|}{|X|} p \geqslant (1 - \eta) p \geqslant p - \eta \geqslant p - \varepsilon.$$

Now, to see that I is an independent set, assume for contradiction it contains an edge between say (x,A) and (x',B). Clearly we must have that  $x \neq x'$  (otherwise A,B both contain H(x)), so H satisfies the constraint between x and x'. It thus follows that A contains H(x), and B contains  $H(x') = \phi_{x,x'}(H(x))$ , and so  $\phi_{x,x'}(A) \cap B \neq \emptyset$ , so this is actually not an edge in the graph G. Contradiction.

#### 3.2 Soundness

We now move on to the soundness of the construction. We will not give the entire argument, and instead convey the spirit of the matter.

Suppose we have an independent set I in G of weight at least  $\varepsilon$ . Consider the upwards closure of the family

$$I \uparrow = \{ (x, A) \mid \exists B \subseteq A, (x, B) \in I \}.$$

It is easy to see that  $I \uparrow$  is also independent set. Abusing notations, we drop the  $\uparrow$  notation and denote this family by I.

For each  $x \in X$ , let

$$I_x = \{ A \subseteq \Sigma \mid (x, A) \in I \}.$$

Note that

$$\mathbb{E}_{x \in X} \left[ \mu_p(I_x) \right] = w(I) \geqslant \varepsilon,$$

so letting  $X_1 = \{x \mid \mu_p(I_x) \ge \varepsilon\}$ , we have that  $|X'| \ge \frac{\varepsilon}{2} |X|$ .

Next, define  $f:[p,p+\varepsilon/2]\to [0,1]$  by  $f(q)=\mathbb{E}_{x\in X}[\mu_q(I_x)]$ . Then by Lagrange we may find  $q'\in(p,p+\varepsilon/2)$  such that

$$f'(q') = \frac{f(q + \varepsilon/2) - f(q)}{q + \varepsilon/2 - q} \leqslant \frac{2}{\varepsilon}.$$

Thus,

$$\mathbb{E}_{x}\left[\frac{d}{dq}\mu_{q}(I_{x})|_{q=q'}\right] \leqslant \frac{2}{\varepsilon},$$

and letting  $X_2 = \left\{ x \mid \frac{d}{dq} \mu_q(I_x) \mid_{q=q'} \leqslant \frac{8}{\varepsilon^2} \right\}$  we have by Markov's inequality that  $|X_2| \geqslant \left(1 - \frac{\varepsilon}{4}\right) |X|$ . We fix q' and  $X_2$  henceforth.

Thus, we take  $X' = X_1 \cap X_2$ , and note that  $|X'| \geqslant \frac{\varepsilon}{4} |X|$ .

#### 3.2.1 Applying Friedgut's Junta Theorem

Note that here, for each  $x \in X'$  we have that  $\frac{d}{dq}\mu_q(I_x)|_{q=q'} \leqslant \frac{8}{\varepsilon^2}$ , hence by Friedgut's Theorem we get that  $I_x$  is close to a junta, i.e. to a family that depends only on coordinates  $J_x \subseteq \Sigma$  where  $|J_x| = O_{\varepsilon}(1) = t$ .

Here, we will make a simplifying assumption. This assumption is not necessary and there are ways to circumvent it, but it adds an additional technical difficulty which we wish to avoid. Instead of assuming that  $I_x$  is close to a junta, we will simply assume it is a junta. Namely, we will assume that there is  $\mathcal{J}_x \subseteq J_x$  such that

$$I_x = \{ A \subseteq \Sigma \mid A \cap J_x \in \mathcal{J}_x \}.$$

We are now ready to define a t-assignment. Indeed, define  $H: X' \to {X \choose t}$  by  $H(x) = J_x$ . To finish the proof, we show that H satisfies all of the constraints inside X', which gives us contradiction to the fact  $\Psi$  was from the no case.

#### 3.2.2 The Juntas are intersecting

**Lemma 3.1.** H defined above satisfies all of the constraints inside X'.

*Proof.* Assume towards contradiction this is not the case, and let  $x,x' \in X'$  be such that H fails to satisfy the constraint between them. Then  $J_{x'} \cap \phi_{x,x'}(J_x) = \emptyset$ . As  $\mu_q(I_x), \mu_q(I_{x'}) > 0$ , we may find  $A_x \in \mathcal{J}_x$ ,  $A_{x'} \in \mathcal{J}_{x'}$ , and as  $J_{x'} \cap \phi_{x,x'}(J_x) = \emptyset$ , we have that  $A_{x'} \cap \phi_{x,x'}(A_x) = \emptyset$ . Thus, there is an edge between  $(x,A_x)$  and  $(x',A_{x'})$  in our graph G, and we next argue that both of these points are in I. This yields a contradiction to the fact that I is an independent set.

Indeed, as  $I_x$  is a  $J_x$  junta and  $A_x \in \mathcal{J}_x$ , we get that  $A_x \in I_x$ , and similarly for  $A_{x'}$ . This completes the proof.

18.218 Topics in Combinatorics: Analysis of Boolean Functions Spring 2021

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.
