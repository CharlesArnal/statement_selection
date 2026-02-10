# AN EXPOSITION OF BRETAGNOLLE AND MASSART'S PROOF OF THE KMT THEOREM FOR THE UNIFORM EMPIRICAL PROCESS

R. M. Dudley

February 23, 2005

## Preface

These lecture notes, part of a course given in Aarhus, August 1999, treat the classical empirical process defined in terms of empirical distribution functions. A proof, expanding on one in a 1989 paper by Bretagnolle and Massart, is given for the Komlós-Major-Tusnády result on the speed of convergence of the empirical process to a Brownian bridge in the supremum norm.

Herein "A := B" means A is defined by B, whereas "A =: B" means B is defined by A.

Richard Dudley Cambridge, Mass., August 24, 1999

## Contents

| 1 | Empirical distribution functions: the KMT theorem |                                              |    |  |
|---|---------------------------------------------------|----------------------------------------------|----|--|
|   | 1.1                                               | Introduction                                 | 1  |  |
|   | 1.2                                               | Statements: the theorem and Tusnády's lemmas | 2  |  |
|   | 1.3                                               | Stirling's formula: Proof of Lemma 1.5       | 3  |  |
|   | 1.4                                               | Proof of Lemma 1.4                           | 4  |  |
|   | 1.5                                               | Proof of Lemma 1.2                           | 12 |  |
|   | 1.6                                               | Inequalities for the separate processes      | 13 |  |
|   | 1.7                                               | Proof of Theorem 1.1                         | 16 |  |
|   | 1.8                                               | Another way of defining the KMT construction | 22 |  |

### Chapter 1

## Empirical distribution functions: the KMT theorem

#### 1.1 Introduction

Let U[0,1] be the uniform distribution on [0,1] and U its distribution function. Let  $X_1, X_2, \ldots$  be independent and identically distributed random variables with law U. Let  $F_n(t)$  be the empirical distribution function based on  $X_1, X_2, \ldots, X_n$ ,

$$F_n(t) := \frac{1}{n} \sum_{j=1}^n 1_{\{X_j \le t\}},$$

and  $\alpha_n(t)$  the corresponding empirical process, i.e.,  $\alpha_n(t) = \sqrt{n}(F_n(t) - t)$ ,  $t \in [0, 1]$ . Here  $\alpha_n$  may be called the *classical* empirical process. Recall that a *Brownian bridge* is a Gaussian stochastic process B(t),  $0 \le t \le 1$ , with EB(t) = 0 and EB(t)B(u) = t(1-u) for  $0 \le t \le u \le 1$ . Donsker (1952) proved (neglecting measurability problems) that  $\alpha_n(t)$  converges in law to a Brownian bridge B(t) with respect to the sup norm. Komlós, Major, and Tusnády (1975) stated a sharp rate of convergence, namely that on some probability space there exist  $X_i$  i.i.d. U[0,1] and Brownian bridges  $B_n$  such that

$$P\left(\sup_{0 \le t \le 1} |\sqrt{n}(\alpha_n(t) - B_n(t))| > x + c \log n\right) < Ke^{-\lambda x}$$
(1.1)

for all n and x, where c, K, and  $\lambda$  are positive absolute constants. Komlós, Major and Tusnády (KMT) formulated a construction giving a joint distribution of  $\alpha_n$  and  $B_n$ , and this construction has been accepted by later workers. But Komlós, Major and Tusnády gave hardly any proof for (1.1). Csörgő and Révész (1981) sketched a method of proof of (1.1) based on lemmas of G. Tusnády, Lemmas 1.2 and 1.4 below. The implication from Lemma 1.4 to 1.2 is not difficult, but Csörgő and Révész did not include a proof of Lemma 1.4. Bretagnolle and Massart (1989) gave a proof of the lemmas and of the inequality (1.1) with specific constants, Theorem 1.1 below. Bretagnolle and Massart's proof was rather compressed and some readers have had difficulty following it. Csörgő and Horváth (1993), pp. 116-139, expanded the proof while making it more elementary and gave a proof of Lemma 1.4 for  $n \geq n_0$  where  $n_0$  is at least 100. The purpose of the present chapter is to give a detailed and in some minor details corrected version of the original Bretagnolle and Massart proof of the lemmas for all n, overlapping in

part with the Csörgő and Horváth proof, then to prove (1.1) for some constants, as given by Bretagnolle and Massart and largely following their proof.

Mason and van Zwet (1987) gave another proof of the inequality (1.1) and an extended form of it for subintervals  $0 \le t \le d/n$  with  $1 \le d \le n$  and  $\log n$  replaced by  $\log d$ , without Tusnády's inequalities and without specifying the constants  $c, K, \lambda$ . Some parts of the proof sketched by Mason and van Zwet are given in more detail by Mason (1998).

**Acknowledgments**. I am very grateful to Evarist Giné, David Mason, Jon Wellner, and Uwe Einmahl for conversations and correspondence on the topic.

#### 1.2 Statements: the theorem and Tusnády's lemmas

The main result of the present chapter is:

**Theorem 1.1.** (Bretagnolle and Massart) The approximation (1.1) of the empirical process by the Brownian bridge holds with c = 12, K = 2 and  $\lambda = 1/6$  for  $n \ge 2$ .

The rest of this chapter will give a proof of the theorem. In a preprint, Rio (1991, Theorem 5.1) states in place of (1.1)

$$P\left(\sup_{0 \le t \le 1} |\sqrt{n}(\alpha_n(t) - B_n(t))| > ax + b\log n + \gamma\log 2\right) < Ke^{-x}$$
(1.2)

for  $n \ge 8$  where a = 3.26, b = 4.86,  $\gamma = 2.70$ , and K = 1. This implies that for  $n \ge 8$ , (1.1) holds with c = 5.76, K = 1, and  $\lambda = 1/3.26$ , where all three constants are better than in Theorem 1.1.

Tusnády's lemmas are concerned with approximating symmetric binomial distributions by normal distributions. Let  $\mathcal{B}(n, 1/2)$  denote the symmetric binomial distribution for n trials. Thus if  $B_n$  has this distribution,  $B_n$  is the number of successes in n independent trials with probability 1/2 of success on each trial. For any distribution function F and 0 < t < 1 let  $F^{-1}(t) := \inf\{x : F(x) \ge t\}$ . Here is one of Tusnády's lemmas (Lemma 4 of Bretagnolle and Massart (1989)).

**Lemma 1.2.** Let  $\Phi$  be the standard normal distribution function and Y a standard normal random variable. Let  $\Phi_n$  be the distribution function of  $\mathcal{B}(n, 1/2)$  and set  $C_n := \Phi_n^{-1}(\Phi(Y)) - n/2$ . Then

$$|C_n| \le 1 + (\sqrt{n}/2)|Y|,$$
 (1.3)

$$|C_n - (\sqrt{n}/2)Y| \le 1 + Y^2/8.$$
 (1.4)

Recall the following well known and easily checked facts:

**Theorem 1.3.** Let X be a real random variable with distribution function F.

- (a) If F is continuous then F(X) has a U[0,1] distribution.
- (b) For any F, if V has a U[0,1] distribution then  $F^{-1}(V)$  has distribution function F.

Thus  $\Phi(Y)$  has a U[0,1] distribution and  $\Phi_n^{-1}(\Phi(Y))$  has distribution  $\mathcal{B}(n,1/2)$ . Lemma 1.2 will be shown (by a relatively short proof) to follow from:

**Lemma 1.4.** Let Y be a standard normal variable and let  $\beta_n$  be a binomial random variable with distribution  $\mathcal{B}(n, 1/2)$ . Then for any integer j such that  $0 \le j \le n$  and n + j is even, we have

$$P(\beta_n \ge (n+j)/2) \ge P(\sqrt{n}Y/2 \ge n(1-\sqrt{1-j/n})),$$
 (1.5)

$$P(\beta_n \ge (n+j)/2) \le P(\sqrt{n}Y/2 \ge (j-2)/2).$$
 (1.6)

Remarks. The restriction that n+j be even is not stated in the formulation of the lemma by Bretagnolle and Massart (1989), but n+j is always even in their proof. If (1.6) holds for n+j even it also holds directly for n+j odd, but the same is not clear for (1.5). It turns out that only the case n+j even is needed in the proof of Lemma 1.2, so I chose to restrict the statement to that case.

The following form of Stirling's formula with remainder is used in the proof of Lemma 1.4.

**Lemma 1.5.** Let  $n! = (n/e)^n \sqrt{2\pi n} A_n$  where  $A_n = 1 + \beta_n/(12n)$ , which defines  $A_n$  and  $\beta_n$  for  $n = 1, 2, \cdots$ . Then  $\beta_n \downarrow 1$  as  $n \to \infty$ .

#### 1.3 Stirling's formula: Proof of Lemma 1.5

It can be checked directly that  $\beta_1 > \beta_2 > \cdots > \beta_8 > 1$ . So it suffices to prove the lemma for  $n \geq 8$ . We have  $A_n = \exp((12n)^{-1} - \theta_n/(360n^3))$  where  $0 < \theta_n < 1$ , see Whittaker and Watson (1927), p. 252 or Nanjundiah (1959). Then by Taylor's theorem with remainder,

$$A_n = \left(1 + \frac{1}{12n} + \frac{1}{288n^2} + \frac{1}{6(12n)^3} \phi_n e^{1/12n}\right) \exp(-\theta_n/(360n^3))$$

where  $0 < \phi_n < 1$ . Next,

$$\beta_{n+1} \le 12(n+1) \left[ \exp\left(\frac{1}{12(n+1)}\right) - 1 \right]$$
  
 $\le 1 + \frac{1}{24(n+1)} + \frac{1}{6(12(n+1))^2} e^{1/(12(n+1))},$ 

from which  $\limsup_{n\to\infty} \beta_n \leq 1$ , and

$$\beta_n = 12n[A_n - 1] \ge 12n\left[\left(1 + \frac{1}{12n} + \frac{1}{288n^2}\right)\exp(-1/(360n^3)) - 1\right].$$

Using  $e^{-x} \ge 1 - x$  gives

$$\beta_n \geq 12n \left[ \frac{1}{12n} + \frac{1}{288n^2} - \frac{1}{360n^3} \left( 1 + \frac{1}{12n} + \frac{1}{288n^2} \right) \right]$$
$$= 1 + \frac{1}{24n} - \frac{1}{30n^2} \left( 1 + \frac{1}{12n} + \frac{1}{288n^2} \right).$$

Thus  $\liminf_{n\to\infty}\beta_n\geq 1$  and  $\beta_n\to 1$  as  $n\to\infty$ . To prove  $\beta_n\geq\beta_{n+1}$  for  $n\geq 8$  it will suffice to show that

$$1 + \frac{1}{24(n+1)} + \frac{e^{1/108}}{6 \cdot 144n^2} \le 1 + \frac{1}{24n} - \frac{1}{30n^2} \left[ 1 + \frac{1}{96} + \frac{1}{288 \cdot 8^2} \right]$$

or

$$\frac{e^{1/108}}{6 \cdot 144n^2} + \frac{1}{30n^2} \left[ 1 + \frac{1}{96} + \frac{1}{288 \cdot 64} \right] \le \frac{1}{24n(n+1)}$$

or that  $0.035/n^2 \le 1/[24n(n+1)]$  or  $0.84 \le 1 - 1/(n+1)$ , which holds for  $n \ge 8$ , proving that  $\beta_n$  decreases with n. Since its limit is 1, Lemma 1.5 is proved.

#### 1.4 Proof of Lemma 1.4

First, (1.5) will be proved. For any  $i = 0, 1, \dots, n$  such that n + i is even, let k := (n + i)/2 so that k is an integer,  $n/2 \le k \le n$ , and i = 2k - n. Let  $p_{ni} := P(\beta_n = (n + i)/2) = P(\beta_n = k) = \binom{n}{k}/2^n$  and  $x_i := i/n$ . Define  $p_{ni} := 0$  for n + i odd. The factorials in  $\binom{n}{k}$  will be approximated via Stirling's formula with correction terms as in Lemma 1.5. To that end, let

$$CS(u, v, w, x, n) := \frac{1 + u/(12n)}{(1 + v/[6n(1-x)])(1 + w/[6n(1+x)])}.$$

By Lemma 1.5, we can write for  $0 \le i < n$  and n + i even

$$p_{ni} = CS(x_i, n)\sqrt{2/\pi n} \exp(-ng(x_i)/2 - (1/2)\log(1 - x_i^2))$$
(1.7)

where  $g(x) := (1+x)\log(1+x) + (1-x)\log(1-x)$  and  $CS(x_i, n) := CS(\beta_n, \beta_{n-k}, \beta_k, x_i, n)$ . By Lemma 1.5 and since  $k \ge n/2$ ,

$$1^+ := 1.013251 \ge 12(e(2\pi)^{-1/2} - 1) = \beta_1 \ge \beta_{n-k} \ge \beta_k \ge \beta_n > 1.$$

Thus, for  $x := x_i$ , by clear or easily checked monotonicity properties,

$$CS(x,n) \leq CS(\beta_n, \beta_k, \beta_k, x, n) =$$

$$\left(1 + \frac{\beta_n}{12n}\right) \left[1 + \frac{\beta_k}{3n(1-x^2)} + \frac{\beta_k^2}{36n^2(1-x^2)}\right]^{-1}$$

$$\leq CS(\beta_n, \beta_k, \beta_k, 0, n) \leq CS(\beta_n, \beta_n, \beta_n, 0, n)$$

$$\leq CS(1, 1, 1, 0, n) = \left(1 + \frac{1}{12n}\right) \left[1 + \frac{1}{3n} + \frac{1}{36n^2}\right]^{-1}.$$

It will be shown next that  $\log(1+y) - 2\log(1+2y) \le -3y + 7y^2/2$  for  $y \ge 0$ . Both sides vanish for y = 0. Differentiating and clearing fractions, we get a clearly true inequality. Setting y := 1/(12n) then gives

$$\log CS(x_i, n) \le -1/(4n) + 7/(288n^2). \tag{1.8}$$

To get a lower bound for CS(x,n) we have by an analogous string of inequalities

$$CS(x,n) \ge \left(1 + \frac{1}{12n}\right) \left\{1 + \frac{1^+}{3n(1-x^2)} + \frac{(1^+)^2}{36n^2(1-x^2)}\right\}^{-1}.$$
 (1.9)

The inequality (1.5) to be proved can be written as

$$\sum_{i=j}^{n} p_{ni} \ge 1 - \Phi(2\sqrt{n}(1 - \sqrt{1 - j/n})). \tag{1.10}$$

When j=0 the result is clear. When  $n \leq 4$  and j=n or n-2 the result can be checked from tables of the normal distribution. Thus we can assume from here on

$$n \ge 5. \tag{1.11}$$

CASE I. Let  $j^2 \ge 2n$ , in other words  $x_j \ge \sqrt{2/n}$ . Recall that for t > 0 we have  $P(Y > t) \le (t\sqrt{2\pi})^{-1} \exp(-t^2/2)$ , e.g. Dudley (1993), Lemma 12.1.6(a). Then (1.10) follows easily when j = n and  $n \ge 5$ . To prove it for j = n - 2 it is enough to show

$$n(2 - \log 2) - 4\sqrt{2n} + \log(n+1) + 4 + \log[2\sqrt{2\pi}(\sqrt{n} - \sqrt{2})] \ge 0, \quad n \ge 5.$$

The left side is increasing in n for  $n \ge 5$  and is  $\ge 0$  at n = 5.

For  $5 \le n \le 7$  we have  $(n-4)^2 < 2n$ , so we can assume in the present case that  $2n \le j^2 \le (n-4)^2$  and  $n \ge 8$ . Let  $y_i := 2\sqrt{n}(1-\sqrt{1-i/n})$ . Then it will suffice to show

$$p_{ni} \ge \int_{y_i}^{y_{i+2}} \phi(u) du, \quad i = j, j+2, \cdots, n-4,$$
 (1.12)

where  $\phi$  is the standard normal density function. Let

$$f_n(x) := \sqrt{n/2\pi(1-x)} \exp(-2n(1-\sqrt{1-x})^2).$$
 (1.13)

By the change of variables  $u = 2\sqrt{n}(1-\sqrt{1-x})$ , (1.12) becomes

$$p_{ni} \geq \int_{x_i}^{x_{i+2}} f_n(x) dx. \tag{1.14}$$

Clearly  $f_n > 0$ . To see that  $f_n(x)$  is decreasing in x for  $\sqrt{2/n} \le x \le 1 - 4/n$ , note that

$$2(1-x)f_n'/f_n = 1 - 4n[\sqrt{1-x} - 1 + x],$$

so  $f_n$  is decreasing where  $\sqrt{1-x}-(1-x)>1/(4n)$ . We have  $\sqrt{y}-y\geq y$  for  $y\leq 1/4$ , so  $\sqrt{y}-y>1/(4n)$  for  $1/(4n)< y\leq 1/4$ . Let y:=1-x. Also  $\sqrt{1-x}-(1-x)>x/4$  for x<8/9, so  $\sqrt{1-x}-(1-x)>1/(4n)$  for 1/n< x<8/9. Thus  $\sqrt{1-x}-(1-x)>1/(4n)$  for 1/n< x<1-1/(4n), which includes the desired range. Thus to prove (1.14) it will be enough to show that

$$p_{ni} \ge (2/n)f_n(x_i), \quad i = j, j + 2, \dots, n - 4.$$
 (1.15)

So by (1.7) it will be enough to show that for  $\sqrt{2/n} \le x \le 1 - 4/n$  and  $n \ge 8$ ,

$$CS(x,n)(1+x)^{-1/2}\exp[n\{4(1-\sqrt{1-x})^2-g(x)\}/2] \ge 1.$$
 (1.16)

Let

$$J(x) := 4(1 - \sqrt{1 - x})^2 - g(x). \tag{1.17}$$

Then J is increasing for 0 < x < 1, since its first and second derivatives are both 0 at 0, while its third derivative is easily checked to be positive on (0,1). In light of (1.9), to prove (1.16) it suffices to show that

$$\left(1 + \frac{1}{12n}\right)e^{nJ(x)/2} \ge \sqrt{1+x}\left(1 + \frac{1^+}{3n(1-x^2)} + \frac{(1^+)^2}{36n^2(1-x^2)}\right).$$
(1.18)

When  $x \le 1 - 4/n$  and  $n \ge 8$  the right side is less than 1.5, using first  $\sqrt{1+x} \le \sqrt{2}$ , next  $x \le 1 - 4/n$ , and lastly  $n \ge 8$ . For  $x \ge 0.55$  and  $n \ge 8$  the left side is larger than 1.57, so (1.18) is proved for  $x \ge 0.55$ . We will next need the inequality

$$J(x) \ge x^3/2 + 7x^4/48, \quad 0 \le x \le 0.55.$$
 (1.19)

To check this one can calculate J(0) = J'(0) = J''(0) = 0,  $J^{(3)}(0) = 3$ ,  $J^{(4)}(0) = 7/2$ , so that the right side of (1.19) is the Taylor series of J around 0 through fourth order. One then shows straightforwardly that  $J^{(5)}(x) > 0$  for  $0 \le x < 1$ .

It follows since  $nx^2 \geq 2$  and  $n \geq 8$  that  $nJ(x)/2 \geq x/2 + 7/24n$ . Let  $K(x) := \exp(x/2)/\sqrt{1+x}$  and  $\kappa(x) := (K(x)-1)/x^2$ . We will next see that  $\kappa(\cdot)$  is decreasing on [0,1]. To show  $\kappa' \leq 0$  is equivalent to  $e^{x/2}[4+4x-x^2] \geq 4(1+x)^{3/2}$ , which is true at x=0. Differentiating, we would like to show  $e^{x/2}[6-x^2/2] \geq 6\sqrt{1+x}$ , or squaring that and multiplying by 4,  $e^x(144-24x^2+x^4) \geq 144(1+x)$ . This is true at x=0. Differentiating, we would like to prove  $e^x(144-48x-24x^2+4x^3+x^4) \geq 144$ . Using  $e^x \geq 1+x$  and algebra gives this result for  $0 \leq x \leq 1$ .

It follows that  $K(x) \ge 1 + 0.3799/n$  when  $\sqrt{2/n} \le x \le 0.55$ . It remains to show that for  $x \le 0.55$ ,

$$\left(1 + \frac{1}{12n}\right) \left(1 + \frac{0.3799}{n}\right) e^{7/(24n)} \ge 1 + \frac{1^+}{3n(1-x^2)} + \frac{(1^+)^2}{36n^2(1-x^2)}.$$

At x = 0.55 the right side is less than 1 + 0.543/n, so Case I is completed since  $0.543 \le 1/12 + 0.3799 + 7/24$ .

CASE II. The remaining case is  $j < \sqrt{2n}$ . For any integer k,  $P(\beta_n \ge k) = 1 - P(\beta_n \le k - 1)$ . For k = (n+j)/2 we have k-1 = (n+j-2)/2. If n is odd, then  $P(\beta_n \ge n/2) = 1/2 = P(Y \ge 0)$ . If n is even, then  $P(\beta_n \ge n/2) - p_{n0}/2 = 1/2 = P(Y \ge 0)$ . So, since  $p_{n0} = 0$  for n odd, (1.5) is equivalent to

$$\frac{1}{2}p_{n0} + \sum_{0 < i < j-2} p_{ni} \le P(0 \le Y \le 2\sqrt{n}(1 - \sqrt{1 - j/n})). \tag{1.20}$$

Given  $j < \sqrt{2n}$ , a family  $I_0, I_1, \dots, I_K$  of adjacent intervals will be defined such that for n odd,

$$p_{ni} \le P(\sqrt{n}Y/2 \in I_k) \text{ with } i = 2k+1, \ 0 \le k \le K := (j-3)/2,$$
 (1.21)

while for n even,

$$p_{ni} \le P(\sqrt{n}Y/2 \in I_k) \text{ with } i = 2k, \ 1 \le k \le K := (j-2)/2,$$
 (1.22)

and

$$p_{n0}/2 \le P(\sqrt{n}Y/2 \in I_0).$$
 (1.23)

In either case,

$$I_0 \cup I_1 \cup \dots \cup I_K \subset [0, n(1 - \sqrt{1 - j/n})].$$
 (1.24)

The intervals will be defined by

$$\delta_{k+1} := (k+1)/n + k(k+1/2)(k+1)/n^{3/2}, \quad k \ge 0, \tag{1.25}$$

$$\Delta_{k+1} := \delta_{k+1} + k + 1/2 = \delta_{k+1} + (i+1)/2, \quad i = 2k, \quad n \text{ even},$$
 (1.26)

$$\Delta_{k+1} := \delta_{k+1} + k + 1 = \delta_{k+1} + (i+1)/2, \quad i = 2k+1, \quad n \text{ odd},$$
 (1.27)

$$I_k := [\Delta_k, \Delta_{k+1}] \text{ with } \Delta_0 = 0.$$
 (1.28)

It will be shown that  $I_0, I_1, \dots, I_K$  defined by (1.25) through (1.28) satisfy (1.21) through (1.24). Recall that  $n \geq 5$  (1.11) and  $x_i := i/n$ .

Proof of (1.24). It needs to be shown that  $\Delta_{K+1} \leq n(1-\sqrt{1-x_j})$ . Since  $j < \sqrt{2n}$ , we have  $K \leq j/2 - 1 < \sqrt{n/2} - 1$  and

$$\delta_{K+1} \leq (K+1)/n + K(K+1/2)/(n\sqrt{2}) \leq x_j/2 + nx_j^2/(4\sqrt{2}).$$

We have  $\Delta_{K+1} = nx_j/2 - 1/2 + \delta_{K+1}$ . It will be shown next that

$$1 - \sqrt{1 - x} \ge x/2 + x^2/8, \quad 0 \le x \le 1.$$
 (1.29)

The functions and their first derivatives agree at 0 while the second derivative of the left side is clearly larger.

It then remains to prove that

$$1/2 + nx_j^2(1/8 - 1/4\sqrt{2}) - x_j/2 \ge 0.$$

This is true since  $nx_j^2 \le 2$  and  $x_j \le (2/8)^{1/2} = 1/2$ , so (1.24) is proved.

Proof of (1.21)-(1.23). First it will be proved that

$$p_{ni} \le \frac{\sqrt{2}}{\sqrt{\pi n}} \exp \left[ -\frac{1}{4n} + \frac{7}{288n^2} - \frac{(n-1)i^2}{2n^2} + \frac{(i/n)^{2n}}{2n(1-i^2/n^2)} \right].$$
 (1.30)

In light of (1.7) and (1.8), it is enough to prove, for x := i/n, that

$$-[ng(x) + \log(1 - x^2) - (n - 1)x^2]/2 \le x^{2n}/2n(1 - x^2).$$
(1.31)

It is easy to verify that for  $0 \le t < 1$ ,

$$g(t) = (1+t)\log(1+t) + (1-t)\log(1-t) = \sum_{r=1}^{\infty} t^{2r}/r(2r-1).$$

Thus the left side of (1.31) can be expanded as  $\sum_{r\geq 2} x^{2r} (1 - n/(2r - 1))/2r = A + B$  where  $A = \sum_{r=2}^{n-1}$  and  $B = \sum_{r\geq n}$ . We have

$$d^{2}A/dx^{2} = \sum_{2 \le r \le (n+1)/2} (2r - n - 1)(x^{2r-2} - x^{2n-2r})$$

which is  $\leq 0$  for  $0 \leq x \leq 1$ . Since A = dA/dx = 0 for x = 0 we have  $A \leq 0$  for  $0 \leq x \leq 1$ . Then,  $2nB \leq x^{2n}/(1-x^2)$ , so (1.30) is proved.

We have for  $n \ge 5$  and  $x \le (\sqrt{2n} - 2)/n$  that  $x^{2n}/(1-x^2) < 10^{-3}$ , since  $n \mapsto (\sqrt{2n} - 2)/n$  is decreasing in n for  $n \ge 8$  and the statement can be checked for n = 5, 6, 7, 8. So (1.30) yields

$$p_{ni} \le \sqrt{2/\pi n} \exp[-0.249/n + 7/288n^2 - (n-1)i^2/2n^2].$$
 (1.32)

Next we will need:

**Lemma 1.6.** For any  $0 \le a < b$  and a standard normal variable Y,

$$P(Y \in [a, b]) \ge \sqrt{1/2\pi}(b - a) \exp[-a^2/4 - b^2/4]\phi(a, b)$$
 (1.33)

where  $\phi(a,b) := [4/(b^2 - a^2)] \sinh[(b^2 - a^2)/4] \ge 1$ .

*Proof.* Since the Taylor series of sinh around 0 has all coefficients positive, and  $(\sinh u)/u$  is an even function, clearly  $\sinh u/u \ge 1$  for any real u. The conclusion of the lemma is equivalent to

$$\frac{a+b}{2} \int_{a}^{b} \exp(-u^{2}/2) du \ge \exp(-a^{2}/2) - \exp(-b^{2}/2). \tag{1.34}$$

Letting x := b - a and v := u - a we need to prove

$$\left(a + \frac{x}{2}\right) \int_0^x \exp(-av - v^2/2) dv \ge 1 - \exp(-ax - x^2/2).$$

This holds for x=0. Taking derivatives of both sides and simplifying, we would like to show

$$\int_0^x \exp(-av - v^2/2) dv \ge x \exp(-ax - x^2/2).$$

This also holds for x = 0, and differentiating both sides leads to a clearly true inequality, so Lemma 1.6 is proved.

For the intervals  $I_k$ , Lemma 1.6 yields

$$P(\sqrt{n}Y/2 \in I_k) \ge \sqrt{2/\pi n}\phi_k \exp[-(\Delta_{k+1}^2 + \Delta_k^2)/n + \log(\Delta_{k+1} - \Delta_k)]$$
 (1.35)

where  $\phi_k := \phi(2\Delta_k/\sqrt{n}, 2\Delta_{k+1}/\sqrt{n})$ . The aim is to show that the ratio of the bounds (1.35) over (1.32) is at least 1.

First consider the case k = 0. If n is even, this means we want to prove (1.23). Using (1.32) and (1.35) and  $\phi_0 \ge 1$ , it suffices to show that

$$0.249/n - 7/288n^2 - 1/4n - 1/n^2 - 1/n^3 + \log(1 + 2/n) \ge 0.$$

Since  $\log(1+u) \ge u - u^2/2$  for  $u \ge 0$  by taking a derivative, it will be enough to show that

$$(E)_n := 1.999/n - 3/n^2 - 7/288n^2 - 1/n^3 \ge 0,$$

and it is easily checked that  $n(E)_n > 0$  since  $n \ge 5$ .

If n is odd, then (1.32) applies for i=2k+1=1 and we have  $\Delta_0=0$ ,  $\Delta_1=\delta_1+1=1+1/n$  so (1.35) yields

$$P(\sqrt{n}Y/2 \in I_0) \ge \sqrt{2/\pi n} \exp[-(1+1/n)^2/n + \log(1+1/n)].$$

Using  $\log(1+u) \ge u - u^2/2$  again, the desired inequality can be checked since  $n \ge 5$ . This completes the case k = 0.

Now suppose  $k \ge 1$ . In this case,  $i < \sqrt{2n} - 2$  implies  $n \ge 10$  for n even and  $n \ge 13$  for n odd. Let  $s_k := \delta_k + \delta_{k+1}$  and  $d_k := \delta_{k+1} - \delta_k$ . Then for i as in the definition of  $\Delta_{k+1}$ ,

$$\Delta_{k+1} + \Delta_k = i + s_k, \tag{1.36}$$

$$\Delta_{k+1} - \Delta_k = 1 + d_k, \tag{1.37}$$

$$s_k = \frac{2k+1}{n} + \frac{2k^3+k}{n^{3/2}},\tag{1.38}$$

and

$$d_k = \frac{1}{n} + \frac{3k^2}{n^{3/2}}. (1.39)$$

From the Taylor series of sinh around 0 one easily sees that  $(\sinh u)/u \ge 1 + u^2/6$  for all u. Letting  $u := (\Delta_{k+1}^2 - \Delta_k^2)/n \ge i/n$  gives

$$\log \phi_k \ge \log(1 + i^2/6n^2). \tag{1.40}$$

We have

$$d_k \le 3/(2\sqrt{n}) \tag{1.41}$$

since  $2k \leq \sqrt{2n} - 2$  and  $n \geq 10$ . Next we have another lemma:

**Lemma 1.7.**  $\log(1+x) \ge \lambda x$  for  $0 \le x \le \alpha$  for each of the pairs  $(\alpha, \lambda) = (0.207, 0.9)$ , (0.195, 0.913), (0.14, 0.93), (0.04, 0.98).

*Proof.* Since  $x \mapsto \log(1+x)$  is concave, or equivalently we are proving  $1+x \ge e^{\lambda x}$  where the latter function is convex, it suffices to check the inequalities at the endpoints, where they hold.  $\Box$ 

Lemma 1.7 and (1.40) then give

$$\log \phi_k \ge 0.98i^2/6n^2 \tag{1.42}$$

since  $i^2/(6n^2) \le 1/3n \le 0.04$ ,  $n \ge 10$ . Next,

**Lemma 1.8.** We have  $\log(\Delta_{k+1} - \Delta_k) \geq \lambda d_k$  where  $\lambda = 0.9$  when n is even and  $n \geq 20$ ,  $\lambda = 0.93$  when n is odd and  $n \geq 25$ , and  $\lambda = 0.913$  when k = 1 and  $n \geq 10$ . Only these cases are possible (for  $k \geq 1$ ).

*Proof.* If n is even and  $k \ge 2$ , then  $4 \le i = 2k < \sqrt{2n} - 2$  implies  $n \ge 20$ . If n is odd and  $k \ge 2$ , then  $5 \le i = 2k + 1 < \sqrt{2n} - 2$  implies  $n \ge 25$ . So only the given cases are possible.

We have  $k \leq k_n := \sqrt{n/2} - 1$  for n even or  $k_n := \sqrt{n/2} - 3/2$  for n odd. Let  $d(n) := 1/n + 3k_n^2/n^{3/2}$  and  $t := 1/\sqrt{n}$ . It will be shown that d(n) is decreasing in n,

separately for n even and odd. For n even we would like to show that  $3t/2 + (1 - 3\sqrt{2})t^2 + 3t^3$  is increasing for  $0 \le t \le 1/\sqrt{20}$  and in fact its derivative is > 0.04. For n odd we would like to show that  $3t/2 + (1 - 9/\sqrt{2})t^2 + 27t^3/4$  is increasing. We find that its derivative has no real roots and so is always positive as desired.

Since  $d(\cdot)$  is decreasing for  $n \geq 20$ , its maximum for n even,  $n \geq 20$  is at n = 20 and we find it is less than 0.207 so Lemma 1.7 applies to give  $\lambda = 0.9$ . Similarly for n odd and  $n \geq 25$  we have the maximum d(25) < 0.14 and Lemma 1.7 applies to give  $\lambda = 0.93$ .

If k = 1 then  $n \mapsto n^{-1} + 3/n^{3/2}$  is clearly decreasing. Its value at n = 10 is less than 0.195 and Lemma 1.7 applies with  $\lambda = 0.913$ . So Lemma 1.8 is proved.

It will next be shown that for  $n \ge 10$ 

$$s_k \le n^{-1} + k/\sqrt{n}.$$
 (1.43)

By (1.38) this is equivalent to  $2/\sqrt{n} + (2k^2 + 1)/n \le 1$ . Since  $k \le \sqrt{n/2} - 1$  one can check that (1.43) holds for  $n \ge 14$ . For n = 10, 11, 12, 13 note that k is an integer, in fact  $k \le 1$ , and (1.43) holds.

After some calculations, letting  $s := s_k$  and  $d := d_k$  and noting that

$$\Delta_k^2 + \Delta_{k+1}^2 = \frac{1}{2} [(\Delta_{k+1} - \Delta_k)^2 + (\Delta_k + \Delta_{k+1})^2],$$

to show that the ratio of (1.35) to (1.32) is at least 1 is equivalent to showing that

$$-\frac{is}{n} - \frac{d}{n} - \frac{s^2}{2n} - \frac{d^2}{2n} - \frac{1}{2n} - \frac{7}{288n^2} - \frac{i^2}{2n^2} + \frac{0.249}{n} + \log(1+d) + \log\phi_k \ge 0.$$
 (1.44)

Proof of (1.44). First suppose that n is even and  $n \ge 20$  or n is odd and  $n \ge 25$ . Apply the bound (1.41) for  $d^2/2n$ , (1.42) for  $\log \phi_k$ , (1.43) for s and Lemma 1.8 for  $\log(1+d)$ . Apply the exact value (1.39) of d in the d/n and  $\lambda d$  terms. We assemble together terms with factors  $k^2$ , k and no factor of k, getting a lower bound A for (1.44) of the form

$$A := \alpha [k^2/n^{3/2}] - 2\beta [k/n^{5/4}] + \gamma [1/n]$$
 (1.45)

where, if n is even, so i = 2k and  $\lambda = 0.9$ , we get

$$\alpha = 0.7 - [2.5 - 2(0.98)/3]/\sqrt{n} - 3/n,$$
 
$$\beta = n^{-3/4} + n^{-5/4}/2,$$
 
$$\gamma = 0.649 - [17/8 + 7/288]/n - 1/2n^2.$$

Note that for each fixed n, A is 1/n times a quadratic in  $k/n^{1/4}$ . Also,  $\alpha$  and  $\gamma$  are increasing in n while  $\beta$  is decreasing. Thus for  $n \geq 20$  the supremum of  $\beta^2 - \alpha \gamma$  is attained at n = 20 where it is < -0.06. So the quadratic has no real roots and since  $\alpha > 0$  it is always positive, thus (1.44) holds.

When n is odd, i = 2k + 1,  $\lambda = 0.93$  and  $n \ge 25$ . We get a lower bound A for (1.44) of the same form (1.45) where now

$$\alpha = 0.79 - [2.5 - 2(0.98)/3]/\sqrt{n} - 3/n,$$

$$\beta = 1/2n^{1/4} + 2(1 - 0.98/6)/n^{3/4} + 1/2n^{5/4},$$
  

$$\gamma = 0.679 - (3.625 + 7/288 - 0.98/6)/n - 1/2n^2.$$

For the same reasons, the supremum of  $\beta^2 - \alpha \gamma$  for  $n \ge 25$  is now attained at n = 25 and is negative (less than -0.015), so the conclusion (1.44) again holds.

It remains to consider the case k=1 where n is even and  $n\geq 10$  or n is odd and  $n\geq 13$ . Here instead of bounds for  $s_k$  and  $d_k$  we use the exact values (1.38) and (1.39) for k=1. We still use the bounds (1.42) for  $\log \phi_k$  and Lemma 1.8 for  $\log (1+d_k)$ . When n is even, i=2k=2, and we obtain a lower bound A' for (1.44) of the form  $a_1/n + a_2/n^{3/2} + \cdots$ . All terms  $n^{-2}$  and beyond have negative coefficients. Applying the inequality  $-n^{-(3/2)-\alpha} \geq -n^{-3/2} \cdot 10^{-\alpha}$  for  $n\geq 10$  and  $\alpha=1/2,1,\cdots$ , I found a lower bound  $A'\geq 0.662/n-1.115/n^{3/2}>0$  for  $n\geq 10$ . The same method for n odd gave  $A'\geq 0.662/n-1.998/n^{3/2}>0$  for  $n\geq 13$ . The proof of (1.5) is complete.

Proof of (1.6). For n odd, (1.6) is clear when j=1, so we can assume  $j\geq 3$ . For n even, (1.6) is clear when j=2. We next consider the case j=0. By symmetry we need to prove that  $p_{n0} \leq P(\sqrt{n}|Y|/2 \leq 1)$ . This can be checked from a normal table for n=2. For  $n\geq 4$  we have  $p_{n0} \leq \sqrt{2/\pi n}$  by (1.32). The integral of the standard normal density from  $-2/\sqrt{n}$  to  $2/\sqrt{n}$  is clearly larger than the length of the interval times the density at the endpoints, namely  $2\sqrt{2/\pi n} \exp(-2/n)$ . Since  $\exp(-2/n) \geq 1/2$  for  $n \geq 4$  the proof for n even and j=0 is done.

We are left with the cases  $j \geq 3$ . For j = n, we have  $p_{nn} = 2^{-n}$  and can check the conclusion for n = 3, 4 from a normal table. Let  $\phi$  be the standard normal density. We have the inequality, for t > 0,

$$P(Y \ge t) \ge \psi(t) := \phi(t)[t^{-1} - t^{-3}],$$
 (1.46)

Feller (1968), p. 175. Feller does not give a proof. For completeness, here is one:

$$\psi(t) = -\int_{t}^{\infty} \psi'(x)dx = \int_{t}^{\infty} \phi(x)(1 - 3x^{-4})dx \le P(Y \ge t).$$

To prove (1.6) via (1.46) for  $j = n \ge 5$  we need to prove

$$1/2^n \le \phi(t_n)t_n^{-1}(1-t_n^{-2})$$

where  $t_n := (n-2)/\sqrt{n}$ . Clearly  $n \mapsto t_n$  is increasing. For  $n \ge 5$  we have  $1 - t_n^{-2} \ge 4/9$  and  $(2\pi)^{-1/2}e^{2-2/n} \cdot 4/9 \ge 0.878$ . Thus it suffices to prove

$$n(\log 2 - 0.5) + 0.5 \log n - \log(n - 2) + \log(0.878) > 0, n > 5.$$

This can be checked for n = 5, 6 and the left side is increasing in n for  $n \ge 6$ , so (1.6) for  $j = n \ge 5$  follows.

So it will suffice to prove  $p_{ni} \leq P(\sqrt{n}Y/2 \in [(i-2)/2, i/2])$  for  $j \leq i < n$ . From (1.30) and Lemma 1.6, and the bound  $\phi_k \geq 1$ , it will suffice to prove, for x := i/n,

$$-\frac{1}{4n} + \frac{7}{288n^2} - \frac{(n-1)x^2}{2} + \frac{x^{2n}}{2n(1-x^2)} \le -\frac{n[(x-2/n)^2 + x^2]}{4}$$

where  $3/n \le x \le 1 - 2/n$ . Note that  $2n(1-x^2) \ge 4$ . Thus it is enough to prove that

$$x - x^2/2 - x^{2n}/4 \ge 3/4n + 7/288n^2$$

for  $3/n \le x \le 1$  and  $n \ge 5$ , which holds since the function on the left is concave, and the inequality holds at the endpoints. Thus (1.6) and Lemma 1.4 are proved.

#### 1.5 Proof of Lemma 1.2

Let G(x) be the distribution function of a normal random variable Z with mean n/2 and variance n/4 (the same mean and variance as for  $\mathcal{B}(n,1/2)$ ). Let  $B(k,n,1/2) := \sum_{0 \le i \le k} \binom{n}{i} 2^{-n}$ . Lemma 1.4 directly implies

$$G(\sqrt{2kn} - n/2) \le B(k, n, 1/2) \le G(k+1)$$
 for  $k \le n/2$ . (1.47)

Specifically, letting k := (n - j)/2, (1.6) implies

$$B(k, n, 1/2) \le P(Z \ge n - k - 1) = P(k + 1 \ge n - Z) = G(k + 1)$$

since n-Z has the same distribution as Z. (1.5) implies

$$B(k, n, 1/2) \ge P\left(\frac{n}{2} - \frac{\sqrt{n}}{2}Y \le -\frac{n}{2} + \sqrt{2kn}\right) = G(\sqrt{2kn} - n/2).$$

Let

$$\eta := \Phi_n^{-1}(G(Z)). \tag{1.48}$$

This definition of  $\eta$  from Z is called a quantile transformation. By Theorem 1.3, G(Z) has a U[0,1] distribution and  $\eta$  a  $\mathcal{B}(n,1/2)$  distribution. It will be shown that

$$Z-1 \le \eta \le Z + (Z-n/2)^2/2n + 1 \text{ if } Z \le n/2,$$
 (1.49)

and

$$Z - (Z - n/2)^2 / 2n - 1 \le \eta \le Z + 1 \text{ if } Z \ge n/2.$$
 (1.50)

Define a sequence of extended real numbers  $-\infty = c_{-1} < c_0 < c_1 < \dots < c_n = +\infty$  by  $G(c_k) = B(k, n, 1/2)$  Then one can check that  $\eta = k$  on the event  $A_k := \{\omega : c_{k-1} < Z(\omega) \le c_k\}$ . By  $(1.47), G(c_k) = B(k, n, 1/2) \le G(k+1)$  for  $k \le n/2$ . So, on the set  $A_k$  for  $k \le n/2$  we have  $Z - 1 \le c_k - 1 \le k = \eta$ . Note that for n even,  $n/2 < c_{n/2}$  while for n odd,  $n/2 = c_{(n-1)/2}$ . So the left side of (1.49) is proved.

If Y is a standard normal random variable with distribution function  $\Phi$  and density  $\phi$  then  $\Phi(x) \leq \phi(x)/x$  for x > 0, e.g. Dudley (1993), Lemma 12.1.6(a). So we have

$$P(Z \le -n/2) = P\left(\frac{n}{2} + \frac{\sqrt{n}}{2}Y \le -\frac{n}{2}\right) =$$

$$P\left(\frac{\sqrt{n}}{2}Y \le -n\right) = \Phi(-2\sqrt{n}) \le \frac{e^{-2n}}{2\sqrt{2\pi n}} < \frac{1}{2^n}.$$

So  $G(-n/2) < G(c_0) = 2^{-n}$  and  $-n/2 < c_0$ . Thus if  $Z \le -n/2$  then  $\eta = 0$ . Next note that  $Z + (Z - n/2)^2/2n = (Z + n/2)^2/2n \ge 0$  always. Thus the right side of (1.49) holds when  $Z \le -n/2$  and whenever  $\eta = 0$ . Now assume that  $Z \ge -n/2$ . By (1.47), for  $1 \le k \le n/2$ 

$$G((2(k-1)n)^{1/2} - n/2) \le B(k-1, n, 1/2) = G(c_{k-1}),$$

from which it follows that  $(2(k-1)n)^{1/2} - n/2 \le c_{k-1}$  and

$$k-1 \le (c_{k-1} + n/2)^2 / 2n.$$
 (1.51)

The function  $x \mapsto (x + n/2)^2$  is clearly increasing for  $x \ge -n/2$  and thus for  $x \ge c_0$ . Applying (1.51) we get on the set  $A_k$  for  $1 \le k \le n/2$ 

$$\eta = k \le (Z + n/2)^2 / 2n + 1 = Z + (Z - n/2)^2 / 2n + 1.$$

Since  $P(Z \le n/2) = 1/2 \le P(\eta \le n/2)$ , and  $\eta$  is a non-decreasing function of  $Z, Z \le n/2$  implies  $\eta \le n/2$ . So (1.49) is proved.

It will be shown next that  $(\eta, Z)$  has the same joint distribution as  $(n - \eta, n - Z)$ . It is clear that  $\eta$  and  $n - \eta$  have the same distribution and that Z and n - Z do. We have for each  $k = 0, 1, \dots, n, n - \eta = k$  if and only if  $\eta = n - k$  if and only if  $c_{n-k-1} < Z \le c_{n-k}$ . We need to show that this is equivalent to  $c_{k-1} \le n - Z < c_k$ , in other words  $n - c_k < Z \le n - c_{k-1}$ . Thus we want to show that  $c_{n-k-1} = n - c_k$  for each k. It is easy to check that  $G(n - c_k) = P(Z \ge c_k) = 1 - G(c_k)$  while  $G(c_k) = B(k, n, 1/2)$  and  $G(c_{n-k-1}) = B(n - k - 1, n, 1/2) = 1 - B(k, n, 1/2)$ . The statement about joint distributions follows. (1.49) thus implies (1.50).

Some elementary algebra, (1.49) and (1.50) imply

$$|\eta - Z| \le 1 + (Z - n/2)^2 / 2n$$
 (1.52)

and since Z < n/2 implies  $\eta \le n/2$  and Z > n/2 implies  $\eta \ge n/2$ ,

$$|\eta - n/2| \le 1 + |Z - n/2|. \tag{1.53}$$

Letting  $Z=(n+\sqrt{n}Y)/2$  and noting that then  $G(Z)\equiv\Phi(Y),$  (1.48), (1.52), and (1.53) imply Lemma 1.2 with  $C_n=\eta-n/2$ .

#### 1.6 Inequalities for the separate processes

We will need facts providing a modulus of continuity for the Brownian bridge and something similar for the empirical process (although it is discontinuous). Let  $h(t) := +\infty$  if  $t \le -1$  and

$$h(t) := (1+t)\log(1+t) - t, \quad t > -1.$$
 (1.54)

**Lemma 1.9.** Let  $\xi$  be a binomial random variable with parameters n and p. Then for any  $x \geq 0$  and m := np we have

$$P(\xi - m \ge x) \le \inf_{s>0} e^{-sx} E e^{s(\xi - m)} = \left(\frac{m}{m+x}\right)^{m+x} \left(\frac{n-m}{n-m-x}\right)^{n-m-x}.$$
 (1.55)

If  $p \le 1/2$  then bounds for the right side of (1.55) give

$$P(\xi \ge m + x) \le \exp\left(-\frac{m}{1-p}h\left(\frac{x}{m}\right)\right) \tag{1.56}$$

and

$$P(\xi \le m - x) \le \exp(-x^2/[2p(1-p)]).$$
 (1.57)

*Proof.* The first inequality in (1.55) is clear. Let E(k, n, p) denote the probability of at least k successes in n independent trials with probability p of success on each trial, and B(k, n, p) the probability of at most k successes. According to Chernoff's inequalities (Chernoff, 1954), we have with q := 1 - p

$$E(k, n, p) \leq (np/k)^k (nq/(n-k))^{n-k}$$
 if  $k \geq np$ ,

and symmetrically

$$B(k, n, p) \leq (np/k)^k (nq/(n-k))^{n-k}$$
 if  $k \leq np$ .

These inequalities hold for k not necessarily an integer; for this and the equality in (1.55) see also Hoeffding (1963). Then for  $p \le 1/2$ , (1.56) is a consequence proved by Bennett (1962), see also Shorack and Wellner (1986, p. 440, (3)), and (1.57) is a consequence proved by Okamoto (1958) and extended by Hoeffding (1963).

Let  $F_n$  be an empirical distribution function for the uniform distribution on [0,1] and  $\alpha_n(t) := \sqrt{n}(F_n(t) - t)$ ,  $0 \le t \le 1$ , the corresponding empirical process. The previous lemma extends via martingales to a bound for the empirical process on intervals.

**Lemma 1.10.** For any *b* with  $0 < b \le 1/2$  and x > 0,

$$P(\sup_{0 \le t \le b} |\alpha_n(t)| > x/\sqrt{n}) \le 2 \exp\left(-\frac{nb}{1-b}h\left(\frac{x(1-b)}{nb}\right)\right)$$

$$\le 2 \exp(-nb(1-b)h(x/(nb))). \tag{1.58}$$

Remark. The bound given by (1.58) is Lemma 2 of Bretagnolle and Massart (1989). Lemma 1.2 of Csörgő and Horváth (1993), p. 116, has instead the bound  $2\exp(-nbh(x/(nb)))$ . This does not follow from Lemma 1.10, while the converse implication holds by (1.83) below, but I could not follow Csörgő and Horváth's proof of their form.

*Proof.* From the binomial conditional distributions of multinomial variables we have for  $0 \le s \le t < 1$ 

$$E(F_n(t)|F_n(u), u \le s) = E(F_n(t)|F_n(s))$$

$$= F_n(s) + \frac{t-s}{1-s}(1-F_n(s)) = \frac{t-s}{1-s} + \frac{1-t}{1-s}F_n(s),$$

from which it follows directly that

$$E\left(\frac{F_n(t)-t}{1-t}\Big|F_n(u),\ u\leq s\right) = \frac{F_n(s)-s}{1-s},$$

in other words, the process  $(F_n(t) - t)/(1 - t)$ ,  $0 \le t < 1$  is a martingale in t (here n is fixed). Thus,  $\alpha_n(t)/(1 - t)$ ,  $0 \le t < 1$ , is also a martingale, and for any real s the process  $\exp(s\alpha_n(t)/(1 - t))$  is a submartingale, e.g. Dudley (1993), 10.3.3(b). Then

$$P(\sup_{0 \le t \le b} \alpha_n(t) > x/\sqrt{n}) \le P(\sup_{0 \le t \le b} \alpha_n(t)/(1-t) > x/\sqrt{n})$$

which for any s > 0 equals

$$P\left(\sup_{0 \le t \le b} \exp(s\alpha_n(t)/(1-t)) > \exp(sx/\sqrt{n})\right).$$

By Doob's inequality (e.g. Dudley (1993), 10.4.2, for a finite sequence increasing up to a dense set) the latter probability is

$$\leq \inf_{s>0} \exp(-sx/\sqrt{n})E\exp(s\alpha_n(b)/(1-b)) \leq \exp\left(-\frac{nb}{1-b}h\left(\frac{x(1-b)}{nb}\right)\right)$$

by Lemma 1.9, (1.56). In the same way, by (1.57) we get

$$P(\sup_{0 \le t \le b} (-\alpha_n(t)) > x/\sqrt{n}) \le \exp(-x^2(1-b)/(2nb)).$$
(1.59)

It is easy to check that  $h(u) \le u^2/2$  for  $u \ge 0$ , so the first inequality in Lemma 1.10 follows. It is easily shown by derivatives that  $h(qy) \ge q^2 h(y)$  for  $y \ge 0$  and  $0 \le q \le 1$ . For q = 1 - b, the bound in (1.58) then follows.

We next have a corresponding inequality for the Brownian bridge.

**Lemma 1.11.** Let B(t),  $0 \le t \le 1$ , be a Brownian bridge, 0 < b < 1 and x > 0. Let  $\Phi$  be the standard normal distribution function. Then

$$P(\sup_{0 \le t \le b} B(t) > x) = 1 - \Phi(x/\sqrt{b(1-b)})$$

$$+\exp(-2x^2)\left(1-\Phi\left(\frac{(1-2b)x}{\sqrt{b(1-b)}}\right)\right).$$
 (1.60)

If  $0 < b \le 1/2$ , then for all x > 0,

$$P(\sup_{0 \le t \le b} B(t) > x) \le \exp(-x^2/(2b(1-b))). \tag{1.61}$$

*Proof.* Let X(t),  $0 \le t < \infty$  be a Wiener process. For some real  $\alpha$  and value of X(1) let  $\beta := X(1) - \alpha$ . It will be shown that for any real  $\alpha$  and y

$$P\{\sup_{0 \le t \le 1} X(t) - \alpha t > y | X(1)\} = 1_{\{\beta > y\}} + \exp(-2y(y - \beta)) 1_{\{\beta \le y\}}.$$
 (1.62)

Clearly, if  $\beta > y$  then  $\sup_{0 \le t \le 1} X(t) - \alpha t > y$  (let t = 1). Suppose  $\beta \le y$ . One can apply a reflection argument as in the proof of Dudley (1993), Proposition 12.3.3, where details are given on making such an argument rigorous. Let X(t) = B(t) + tX(1) for  $0 \le t \le 1$ , where  $B(\cdot)$  is a Brownian bridge. We want to find  $P(\sup_{0 \le t \le 1} B(t) + \beta t > y)$ . But this is the same as  $P(\sup_{0 \le t \le 1} Y(t) > y | Y(1) = \beta)$  for a Wiener process Y. For  $\beta \le y$ , the probability that  $\sup_{0 \le t \le 1} Y(t) > y$  and  $\beta \le Y(1) \le \beta + dy$  is the same by reflection as  $P(2y - \beta \le Y(1) \le 2y - \beta + dy)$ . Thus the desired conditional probability, for the standard normal density  $\phi$ , is  $\phi(2y - \beta)/\phi(\beta) = \exp(-2y(y - \beta))$  as stated. So (1.62) is proved.

We can write the Brownian bridge B as W(t) - tW(1),  $0 \le t \le 1$ , for a Wiener process W. Let  $W_1(t) := b^{-1/2}W(bt)$ ,  $0 \le t < \infty$ . Then  $W_1$  is a Wiener process. Let  $\eta := W(1) - W(b)$ . Then  $\eta$  has a normal N(0, 1 - b) distribution and is independent of  $W_1(t)$ ,  $0 \le t \le 1$ . Let  $\gamma := ((1 - b)W_1(1) - \sqrt{b}\eta)\sqrt{b}/x$ . We have

$$P(\sup_{0 \le t \le b} B(t) > x | \eta, W_1(1)) = P\left(\sup_{0 \le t \le 1} (W_1(t) - (bW_1(1) + \sqrt{b}\eta)t) > x/\sqrt{b}|\eta, W_1(1)\right).$$

Now the process  $W_1(t) - (bW_1(t) + \sqrt{b\eta})t$ ,  $0 \le t \le 1$ , has the same distribution as a Wiener process Y(t),  $0 \le t \le 1$ , given that  $Y(1) = (1 - b)W_1(1) - \sqrt{b\eta}$ . Thus by (1.62) with  $\alpha = 0$ ,

$$P(\sup_{0 \le t \le b} B(t) > x | \eta, W_1(1)) = 1_{\{\gamma > 1\}} + 1_{\{\gamma \le 1\}} \exp(-2x^2(1 - \gamma)/b).$$
 (1.63)

Thus, integrating gives

$$P(\sup_{0 \le t \le b} B(t) > x) = P(\gamma > 1) + \exp(-2x^2/b)E\left(\exp(2x^2\gamma/b)1_{\{\gamma \le 1\}}\right).$$

From the definition of  $\gamma$  it has a  $N(0, b(1-b)/x^2)$  distribution. Since x is constant, the latter integral with respect to  $\gamma$  can be evaluated by completing the square in the exponent and yields (1.60).

We next need the inequality, for  $x \geq 0$ ,

$$1 - \Phi(x) \le \frac{1}{2} \exp(-x^2/2). \tag{1.64}$$

This is easy to check via the first derivative for  $0 \le x \le \sqrt{2/\pi}$ . On the other hand we have the inequality  $1 - \Phi(x) \le \phi(x)/x$ , x > 0, e.g. Dudley (1993), 12.1.6(a), which gives the conclusion for  $x \ge \sqrt{2/\pi}$ .

Applying (1.64) to both terms of (1.60) gives (1.61), so the Lemma is proved.

#### 1.7 Proof of Theorem 1.1

For the Brownian bridge B(t),  $0 \le t \le 1$ , it is well known that for any x > 0

$$P(\sup_{0 \le t \le 1} |B(t)| \ge x) \le 2 \exp(-2x^2),$$

e.g. Dudley (1993), Proposition 12.3.3. It follows that

$$P(\sqrt{n} \sup_{0 < t < 1} |B(t)| \ge u) \le 2 \exp(-u/3)$$

for  $u \ge n/6$ . We also have  $|\alpha_1(t)| \le 1$  for all t and

$$P(\sup_{0 \le t \le 1} |\alpha_n(t)| \ge x) \le D \exp(-2x^2),$$
 (1.65)

which is the Dvoretzky-Kiefer-Wolfowitz inequality with a constant D. Massart (1990) proved (1.65) with the sharp constant D=2. Earlier Hu (1985) proved it with  $D=4\sqrt{2}$ . D=6 suffices for present purposes. Given D, it follows that for  $u \ge n/6$ ,

$$P(\sqrt{n} \sup_{0 \le t \le 1} |\alpha_n(t)| \ge u) \le D \exp(-u/3).$$

For  $x < 6 \log 2$ , we have  $2e^{-x/6} > 1$  so the conclusion of Theorem 1.1 holds. For  $x > n/3 - 12 \log n$ ,  $u := (x + 12 \log n)/2 > n/6$  so the left side of (1.1) is bounded above by  $(2+D)n^{-2}e^{-x/6}$ . We have  $(2+D)n^{-2} \le 2$  for  $n \ge 2$  and  $0 \le 6$ .

Thus it will be enough to prove Theorem 1.1 when

$$6\log 2 \le x \le n/3 - 12\log n. \tag{1.66}$$

The function  $t \mapsto t/3 - 12 \log t$  is decreasing for t < 36, increasing for t > 36. Thus one can check that for (1.66) to be non-vacuous is equivalent to

$$n \geq 204. \tag{1.67}$$

Let N be the largest integer such that  $2^N \leq n$ , so that  $\nu := 2^N \leq n < 2\nu$ . Let Z be a  $\nu$ -dimensional normal random variable with independent components, each having mean 0 and variance  $\lambda := n/\nu$ . For integers  $0 \leq i < m$  let  $A(i,m) := \{i+1,\dots,m\}$ . For any two vectors  $a := (a_1,\dots,a_{\nu})$  and  $b := (b_1,\dots,b_{\nu})$  in  $\mathbb{R}^{\nu}$ , we have the usual inner product  $(a,b) := \sum_{i=1}^{\nu} a_i b_i$ . For any subset  $D \subset A(0,\nu)$  let  $1_D$  be its indicator function as a member of  $\mathbb{R}^{\nu}$ . For any integers  $j = 0, 1, 2, \cdots$  and  $k = 0, 1, \cdots$ , let

$$I_{j,k} := A(2^{j}k, 2^{j}(k+1)),$$
 (1.68)

let  $e_{j,k}$  be the indicator function of  $I_{j,k}$  and for  $j \geq 1$ , let  $e'_{j,k} := e_{j-1,2k} - e_{j,k}/2$ . Then one can easily check that the family  $\mathcal{E} := \{e'_{j,k} : 1 \leq j \leq N, \ 0 \leq k < 2^{N-j}\} \cup \{e_{N,0}\}$  is an orthogonal basis of  $\mathbb{R}^{\nu}$  with  $(e_{N,0}, e_{N,0}) = \nu$  and  $(e'_{j,k}, e'_{j,k}) = 2^{j-2}$  for each of the given j, k. Let  $W_{j,k} := (Z, e_{j,k})$  and  $W'_{j,k} := (Z, e'_{j,k})$ . Then since the elements of  $\mathcal{E}$  are orthogonal it follows that the random variables  $W'_{j,k}$  for  $1 \leq j \leq N$ ,  $0 \leq k < 2^{N-j}$  and  $W_{N,0}$  are independent normal with

$$EW'_{j,k} = EW_{N,0} = 0, \quad Var(W'_{j,k}) = \lambda 2^{j-2}, \quad Var(W_{N,0}) = \lambda \nu.$$
 (1.69)

Recalling the notation of Lemma 1.2, let  $\Phi_n$  be the distribution function of a binomial  $\mathcal{B}(n, 1/2)$  random variable, with inverse  $\Phi_n^{-1}$ . Now let  $G_m(t) := \Phi_m^{-1}(\Phi(t))$ .

We will begin defining the construction that will connect the empirical process with a Brownian bridge. Let

$$U_{N,0} := n \tag{1.70}$$

and then recursively as j decreases from j = N to j = 1,

$$U_{j-1,2k} := G_{U_{j,k}}((2^{2-j}/\lambda)^{1/2}W'_{j,k}), \quad U_{j-1,2k+1} := U_{j,k} - U_{j-1,2k}, \tag{1.71}$$

 $k=0,1,\cdots,2^{N-j}-1$ . Note that by (1.69),  $(2^{2-j}/\lambda)^{1/2}W'_{j,k}$  has a standard normal distribution, so  $\Phi$  of it has a U[0,1] distribution. It is easy to verify successively for  $j=N,N-1,\cdots,0$  that the random vector  $\{U_{j,k},\ 0\leq k<2^{N-j}\}$  has a multinomial distribution with parameters

 $n, 2^{j-N}, \dots, 2^{j-N}$ . Let  $X := (U_{0,0}, U_{0,1}, \dots, U_{0,\nu-1})$ . Then the random vector X has a multinomial distribution with parameters  $n, 1/\nu, \dots, 1/\nu$ .

The random vector X is equal in distribution to

$$\{n(F_n((k+1)/\nu) - F_n(k/\nu)), \ 0 \le k \le \nu - 1\},\tag{1.72}$$

while for a Wiener process W, Z is equal in distribution to

$$\{\sqrt{n}(W((k+1)/\nu) - W(k/\nu)), \ 0 \le k \le \nu - 1\}.$$
(1.73)

Without loss of generality, we can assume that the above equalities in distribution are actual equalities for some uniform empirical distribution functions  $F_n$  and Wiener process  $W = W_n$ . Specifically, consider a vector of i.i.d. uniform random variables  $(x_1, \dots, x_n) \in \mathbb{R}^n$  such that

$$F_n(t) := \frac{1}{n} \sum_{i=1}^n 1_{\{x_j \le t\}}$$

and note that W has sample paths in C[0,1]. Both  $\mathbb{R}^n$  and C[0,1] are separable Banach spaces. Thus one can let  $(x_1, \dots, x_n)$  and W be conditionally independent given the vectors in (1.72) and (1.73) which have the joint distribution of X and Z, by the Vorob'ev-Berkes-Philipp theorem, see Berkes and Philippp (1979), Lemma A1. Then we define a Brownian bridge by  $B_n(t) := W_n(t) - tW_n(1)$  and the empirical process  $\alpha_n(t) := \sqrt{n}(F_n(t) - t)$ ,  $0 \le t \le 1$ . By our choices, we then have

$$\left\{n(F_n(j/\nu) - j/\nu)\right\}_{j=0}^{\nu} = \left\{\sum_{i=0}^{j-1} \left(X_i - \frac{n}{\nu}\right)\right\}_{j=0}^{\nu}$$
(1.74)

and

$$\left\{\sqrt{n}B_n(j/\nu)\right\}_{j=0}^{\nu} = \left\{\left(\sum_{i=0}^{j-1} Z_i\right) - \frac{j}{\nu}\sum_{r=0}^{\nu-1} Z_r\right\}_{j=0}^{\nu}.$$
 (1.75)

Theorem 1.1 will be proved for the given  $B_n$  and  $\alpha_n$ . Specifically, we want to prove

$$P_0 := P\left(\sup_{0 \le t \le 1} |\alpha_n(t) - B_n(t)| > (x + 12\log n)/\sqrt{n}\right) \le 2\exp(-x/6).$$
 (1.76)

It will be shown that  $\alpha_n(j/\nu)$  and  $B_n(j/\nu)$  are not too far apart for  $j=0,1,\dots,\nu$  while the increments of the processes over the intervals between the lattice points  $j/\nu$  are also not too large.

Let C := 0.29. Let M be the least integer such that

$$C(x+6\log n) \le \lambda 2^{M+1}. (1.77)$$

Since  $n \ge 204$  (1.67) and  $\lambda < 2$  this implies  $M \ge 2$ . We have by definition of M and (1.66)

$$2^{M} \le \lambda 2^{M} \le C(x + 6 \log n) \le Cn/3 < 0.1 \cdot 2^{N+1} < 2^{N-2}$$

so  $M \leq N - 3$ .

For each  $t \in [0,1]$ , let  $\pi_M(t)$  be the nearest point of the grid  $\{i/2^{N-M}, 0 \le i \le 2^{N-M}\}$ , or if there are two nearest points, take the smaller one. Let D := X - Z and  $D(m) := \sum_{i=1}^m D_i$ . Let C' := 0.855 and define

$$\Theta := \{ U_{j,k} \le \lambda (1 + C') 2^j \text{ whenever } M + 1 < j \le N, \ 0 \le k < 2^{N-j} \}$$

$$\cap \{ U_{j,k} \ge \lambda (1 - C') 2^j \text{ whenever } M < j \le N, \ 0 \le k < 2^{N-j} \}.$$

Then

$$P_0 \leq P_1 + P_2 + P_3 + P(\Theta^c)$$

where

$$P_1 := P\left(\sup_{0 \le t \le 1} |\alpha_n(t) - \alpha_n(\pi_M(t))| > 0.28(x + 6\log n)/\sqrt{n}\right), \tag{1.78}$$

$$P_2 := P\left(\sup_{0 \le t \le 1} |B_n(t) - B_n(\pi_M(t))| > 0.22(x + 6\log n)/\sqrt{n}\right), \tag{1.79}$$

and, recalling (1.74) and (1.75).

$$P_3 := 2^{N-M} \max_{m \in A(M)} P\left\{ \left( |D(m) - \frac{m}{\nu} D(\nu)| > 0.5x + 9\log n \right) \cap \Theta \right\}, \tag{1.80}$$

where  $A(M) := \{k2^M : k = 1, 2, \dots\} \cap A(0, \nu).$ 

First we bound  $P(\Theta^c)$ . Since by (1.71)  $U_{j,k} = U_{j-1,2k} + U_{j-1,2k+1}$ , we have

$$\Theta^{c} \subset \bigcup_{0 \le k < 2^{N-M-2}} \{ U_{M+2,k} > (1+C')\lambda 2^{M+2} \} \cup \bigcup_{0 \le k < 2^{N-M-1}} \{ U_{M+1,k} < (1-C')\lambda 2^{M+1} \}.$$

Since  $U_{M+2,k}$  and  $U_{M+1,k}$  are binomial random variables, Lemma 1.9 gives

$$P(\Theta^c) \le 2^{N-M-1} \left( \exp(-\lambda 2^{M+2} h(C')) + \exp(-\lambda 2^{M+1} h(-C')) \right).$$

Now  $2h(C') \ge 0.5823 \ge h(-C') \ge 0.575$  (note that C' has been chosen to make 2h(C') and h(-C') approximately equal). By definition of M (1.77),  $\lambda 2^{M+1} \ge C(x+6\log n)$ , and 0.575C > 1/6, so

$$P(\Theta^c) \le 2^{-M} \exp(-x/6).$$
 (1.81)

Next, to bound  $P_1$  and  $P_2$ . Let  $b := 2^{M-N-1} \le 1/2$ . Since  $\alpha_n(t)$  has stationary increments, we can apply Lemma 1.10. Let  $u := x + 6 \log n$ . We have by definition of M (1.77)

$$nb = n2^{M-N-1} < Cu/2.$$
 (1.82)

By (1.66), u < n/3 so b < C/6. Recalling (1.54), note that  $h'(t) \equiv \log(1+t)$ . Thus h is increasing. For any given v > 0 it is easy to check that

$$y \mapsto yh(v/y)$$
 is decreasing for  $y > 0$ . (1.83)

Lemma 1.10 gives

$$P_1 \leq 2^{N-M+2} \exp\left(-nb(1-b)h\left(\frac{0.28u}{nb}\right)\right)$$

$$< 2^{N-M+2} \exp\left(-\frac{C}{2} \left[1 - \frac{C}{6}\right] uh\left(0.28 \cdot \frac{2}{C}\right)\right)$$

by (1.83) and (1.82) and since 1 - b > 1 - C/6, so one can calculate

$$P_1 \le 2^{N-M+2}e^{-u/6} \le 2^{2-M}\lambda^{-1}\exp(-x/6).$$
 (1.84)

(1.85)

The Brownian bridge also has stationary increments, so Lemma 1.11, (1.61) and (1.82) give

$$P_2 \le 2^{N-M+2} \exp(-(0.22u)^2/(2nb))$$
  
 $< 2^{N-M+2} \exp(-(0.22)^2 u/C) < 2^{2-M} \lambda^{-1} e^{-x/6}$ 

since  $(0.22)^2/C > 1/6$ .

It remains to bound  $P_3$ . Fix  $m \in A(M)$ . A bound is needed for

$$P_3(m) := P\left\{ \left( |D(m) - \frac{m}{\nu} D(\nu)| > 0.5x + 9\log n \right) \cap \Theta \right\}.$$
 (1.86)

For each  $j = 1, \dots, N$  take k(j) such that  $m \in I_{j,k(j)}$ . By the definition (1.68) of  $I_{j,k}$ ,  $k(M) = m2^{-M} - 1$  and k(j) = [k(j-1)/2] for  $j = 1, \dots, N$  where [x] is the largest integer  $\leq x$ . From here on each double subscript j, k(j) will be abbreviated to the single subscript j, e.g.  $e'_{j} := e'_{j,k(j)}$ . The following orthogonal expansion holds in  $\mathcal{E}$ :

$$1_{A(0,m)} = \frac{m}{\nu} e_{N,0} + \sum_{M < j \le N} c_j e'_j, \tag{1.87}$$

where  $0 \le c_j \le 1$  for  $m < j \le N$ . To see this, note that  $1_{A(0,m)} \perp e'_{j,k}$  for  $j \le M$  since  $2^M$  is a divisor of m. Also,  $1_{A(0,m)} \perp e'_{j,k}$  for  $k \ne k(j)$  since  $1_{A(0,m)}$  has all 0's or all 1's on the set where  $e'_{j,k}$  has non-zero entries, half of which are +1/2 and the other half -1/2. In an orthogonal expansion  $f = \sum_j c_j f_j$  we always have  $c_j = (f, f_j)/\|f_j\|^2$  where  $\|v\|^2 := (v, v)$ . We have  $\|e'_j\| = 2^{(j-2)/2}$ . Now,  $(1_{A(0,m)}, e'_j)$  is as large as possible when the components of  $e'_j$  equal = 1/2 only for indices  $\le m$ , and then the inner product equals  $2^{j-2}$ , so  $|c_j| \le 1$  as stated. The  $m/\nu$  factor is clear.

We next have

$$e_j = 2^{j-N} e_{N,0} + \sum_{i>j} (-1)^{s(i,j,m)} 2^{j+1-i} e_i'$$
 (1.88)

where s(i, j, m) = 0 or 1 for each i, j, m so that the corresponding factors are  $\pm 1$ , the signs being immaterial in what follows. Let  $\Delta_j := (D, e'_j)$ . Then from (1.87),

$$\left| D(m) - \frac{m}{\nu} D(\nu) \right| \leq \sum_{M < j \leq N} |\Delta_j|. \tag{1.89}$$

Recall that  $W'_j = (Z, e'_j)$  (see between (1.68) and (1.69)) and D = X - Z. Let  $\xi_j := (2^{2-j}/\lambda)^{1/2}W'_j$  for  $M < j \leq N$ . Then by (1.69) and the preceding statement,  $\xi_{M+1}, \dots, \xi_N$  are i.i.d. standard normal random variables. We have  $U_{j,k} = (X, e_{j,k})$  for all j and k from the definitions. Then  $U_j = (X, e_j)$ . Let  $U'_j = (X, e'_j)$ . By (1.71) and Lemma 1.2, (1.4),

$$|U_j' - \sqrt{U_j}\xi_j/2| \le 1 + \xi_j^2/8.$$
 (1.90)

Let

$$L_j := |W_j' - \sqrt{U_j}\xi_j/2| = |\xi_j||\sqrt{U_j} - \sqrt{\lambda 2^j}|/2$$

by definition of  $\xi_i$ . Thus

$$|\Delta_j| \le L_j + 1 + \xi_j^2 / 8. \tag{1.91}$$

Then we have on  $\Theta$ 

$$|\sqrt{U_j} - \sqrt{\lambda 2^j}| = |U_j - \lambda 2^j| / (\sqrt{\lambda 2^j} + \sqrt{U_j}) \le \frac{|U_j - \lambda 2^j|}{\sqrt{\lambda 2^j}} \cdot \frac{1}{1 + \sqrt{1 - C'}},$$

where as before C' := 0.855. Then by (1.71), (1.88) and (1.3) of Lemma 1.2,

$$|U_j - \lambda 2^j| \le 2^{j-N} |U_N - n| + 2 \sum_{j < i \le N} 2^{j-i} |U_i'|$$

$$\leq 2 + (\lambda(1+C'))^{1/2} \sum_{j < i \leq N} 2^{j-i/2} |\xi_i|$$

on  $\Theta$ , recalling that by (1.70),  $U_N = U_{N,0} = n$ . Let  $C_2 := 1/(1+\sqrt{1-C'})$ . It follows that

$$L_{j} \leq 2^{-j/2}C_{2}|\xi_{j}| + \frac{1}{2}C_{2}\sqrt{1+C'}\sum_{j \leq i \leq N} 2^{(j-i)/2}|\xi_{j}||\xi_{i}|. \tag{1.92}$$

Applying the inequality  $|\xi_i||\xi_j| \leq (\xi_i^2 + \xi_j^2)/2$ , we get the bound

$$\sum_{M < j \le N} \sum_{j < i \le N} 2^{(j-i)/2} |\xi_i \xi_j| \le \sum_{M < j \le N} A_j \xi_j^2$$
(1.93)

where

$$A_j := \frac{1}{2} \left( \sum_{M < r < j} 2^{(r-j)/2} + \sum_{j < i < N} 2^{(j-i)/2} \right).$$

Then

$$A_j \leq \frac{1}{2} \left[ \frac{2^{-1/2} - 2^{(M-j)/2}}{1 - 2^{-1/2}} + \frac{2^{-1/2}}{1 - 2^{-1/2}} \right]$$
  
$$\leq 1 + \sqrt{2} - 2^{(M-j-2)/2} / (1 - 2^{-1/2}).$$

Let  $C_3 := C_2(1+\sqrt{2})\sqrt{1+C'}/2 \le 1.19067$ . Then

$$\sum_{M < j \le N} L_j \le C_3 \sum_{M < j \le N} \xi_j^2 + \sum_{M < j \le N} 2^{-j/2} |\xi_j| C_2 \left( 1 - \frac{\sqrt{1 + C'}}{2} 2^{(M-2)/2} |\xi_j| / (1 - 2^{-1/2}) \right). \tag{1.94}$$

Let

$$C_4 := \frac{\sqrt{1+C'}}{4(1-2^{-1/2})} = \frac{\sqrt{2}\sqrt{1+C'}(\sqrt{2}+1)}{4},$$

and for each M let  $c_M := 1/(4C_42^{M/2})$ . Then for any real number x, we have  $x(1-C_42^{M/2}x) \le c_M$ . It follows that

$$\sum_{M < j \leq N} L_j \ \leq \ \sum_{M < j \leq N} C_3 \xi_j^2 + c_M C_2 2^{-j/2}$$

$$\leq C_2 c_M 2^{-(M+1)/2} / (1 - 2^{-1/2}) + \sum_{M < j \le N} C_3 \xi_j^2$$

$$\leq \frac{C_2 2^{-M}}{\sqrt{2} \sqrt{1 + C'}} + \sum_{M < j \le N} C_3 \xi_j^2.$$

Thus, combining (1.91) and (1.94) we get on  $\Theta$ 

$$\sum_{M < j \le N} |\Delta_j| \le N + \left(\frac{1}{8} + C_3\right) \sum_{M < j \le N} \xi_j^2.$$
 (1.95)

We have  $E \exp(t\xi^2) = (1-2t)^{-1/2}$  for t < 1/2 and any standard normal variable  $\xi$  such as  $\xi_j$  for each j. Since  $\xi_{M+1}, \dots, \xi_N$  are independent we get

$$E \exp\left(\left(\frac{1}{3} \sum_{M < j \le N} |\Delta_j|\right) 1_{\Theta}\right) \le e^{N/3} \left(1 - \frac{2}{3} \left(C_3 + \frac{1}{8}\right)\right)^{(M-N)/2}$$

$$< e^{N/3} 2^{1.513(N-M)} < 2^{2N-1.5M}.$$

Markov's inequality and (1.89) then yield

$$P_3(m) < e^{-x/6} n^{-3} 2^{2N-1.5M}$$

Thus

$$P_3 \le e^{-x/6} n^{-3} 2^{3N-2.5M} \le 2^{-2.5M} e^{-x/6}.$$
 (1.96)

Collecting (1.81), (1.84), (1.85) and (1.96) we get that  $P_0 \leq (2^{3-M}\lambda^{-1} + 2^{-M} + 2^{-2.5M})e^{-x/6}$ . By (1.77) and (1.67) and since  $x \geq 6 \log 2$  (1.66) and  $M \geq 2$ , it follows that Theorem 1.1 holds.  $\square$ 

#### 1.8 Another way of defining the KMT construction

Now, here is an alternate description of the KMT construction as given in the previous section. For any Hilbert space H, the *isonormal process* is a stochastic process L indexed by H such that the joint distributions of L(f) for  $F \in H$  are normal (Gaussian) with mean 0 and covariance given by the inner product in H, EL(f)L(g) = (f,g). Since the inner product is a nonnegative definite bilinear form, such a process exists. Moreover, we have:

**Lemma 1.12.** For any Hilbert space H, an isonormal process L on H is linear, that is, for any  $f,g \in H$  and constant c, L(cf+g)=cL(f)+L(g) almost surely.

*Proof.* The variable L(cf+g)-cL(f)-L(g) clearly has mean 0 and by a short calculation one can show that its variance is also 0, so it is 0 almost surely.

The Wiener process (Brownian motion) is a Gaussian stochastic process  $W_t$  defined for  $t \geq 0$  with mean 0 and covariance  $EW_sW_t = \min(s,t)$ . One can obtain a Wiener process easily from an isonormal process as follows. Let H be the Hilbert space  $L^2([0,\infty),\lambda)$  where  $\lambda$  is Lebesgue measure. Let  $W_t := L(1_{[0,t]})$ . This process is Gaussian, has mean 0 and clearly

has the correct covariance. Historically, the Wiener process was defined first, and then L(f) was defined only for the particular Hilbert space  $L^2([0,\infty))$  by way of a "stochastic integral"  $L(f) = \int_0^\infty f(t)dW_t$ , which generally doesn't exist as an ordinary integral but is defined as a limit in probability, approximating f in  $L^2$  by step functions. Defining L first seems much easier.

The Brownian bridge process, as has been treated throughout this chapter, is a Gaussian stochastic process  $B_t$  defined for  $0 \le t \le 1$  with mean 0 and covariance  $EB_tB_u = t(1-u)$  for  $0 \le t \le u \le 1$ . Given a Wiener process  $W_t$ , it is easy to see that  $B_t = W_t - tW_1$  for  $0 \le t \le 1$  defines a Brownian bridge.

For j=0,1,2,..., and  $k=1,...,2^j$  let  $I_{j,k}$  be the open interval  $((k-1)/2^j,k/2^j)$ . Let  $T_{j,k}$  be the "triangle function" defined as 0 outside  $I_{j,k}$ , 1 at the midpoint  $(2k-1)/2^{j+1}$ , and linear in between. For a function  $f:[0,1]\mapsto\mathbb{R}$  and r=0,1,..., let  $[f]_r:=f$  at  $k/2^r$  for  $k=0,1,...,2^r$  and linear in between. Let

$$f_{j,k} := W_{j,k}(f) := f\left(\frac{2k-1}{2^{j+1}}\right) - \frac{1}{2}\left[f\left(\frac{k-1}{2^{j}}\right) + f\left(\frac{k}{2^{j}}\right)\right].$$

**Lemma 1.13.** If f is affine, that is  $f(t) \equiv a + bt$  where a and b are constants, then  $f_{j,k} = 0$  for all j and k.

*Proof.* One can check this easily if f is a constant or if  $f(t) \equiv t$ , then use linearity of the operation  $W_{j,k}$  on functions for each j and k.

**Lemma 1.14.** For any  $f: [0,1] \to \mathbb{R}$  and  $r = 0, 1, ..., for <math>0 \le t \le 1$ 

$$[f]_r(t) = f(0) + t[f(1) - f(0)] + \sum_{j=0}^{r-1} \sum_{k=1}^{2^j} f_{j,k} T_{j,k}(t),$$

where the sum is defined as 0 for r = 0.

*Proof.* For r = 0 we have f(0) + t[f(1) - f(0)] = f(0) when t = 0, f(1) when t = 1, and the function is linear in between, so it equals  $[f]_0$ . Then by Lemma 1.13 and linearity of the operations  $W_{j,k}$  we can assume in the proof for  $r \ge 1$  that f(0) = f(1) = 0.

For r=1 we have  $f_{0,1}T_{0,1}(t)=0=f(t)$  for t=0 or 1 and f(1/2) for t=1/2, with linearity in between, so  $f_{0,1}T_{0,1}=[f]_1$ , proving the case r=1. Then, by induction on r, we can apply the same argument on each interval  $I_{r,k}$ ,  $k=1,...,2^r$ , to prove the lemma.

The following is clear since a continuous function on [0,1] is uniformly continuous:

**Lemma 1.15.** If f is continuous on [0,1] then  $[f]_r$  converges to f uniformly as  $r \to \infty$ . It follows that for any  $f \in C[0,1]$ ,

$$f(t) = f(0) + t[f(1) - f(0)] + \sum_{j=0}^{\infty} \sum_{k=1}^{2^{j}} f_{j,k} T_{j,k}(t),$$

where the sum converges uniformly on [0,1]. Thus, the sequence of functions

$$1, t, T_{0,1}, T_{1,1}, T_{1,2}, ..., T_{j,1}, ..., T_{j,2^j}, T_{j+1,1}, ...,$$

is known as the Schauder basis of C[0,1]. This basis fits well with a simple relation between the Brownian motion or Wiener process  $W_t$ ,  $t \geq 0$ , and the Brownian bridge  $B_t$ ,  $0 \leq t \leq 1$ , given by  $B_t = W_t - tW_1$ ,  $0 \leq t \leq 1$ . Both processes are 0 at 0, and their Schauder expansions differ only in the linear "t" term where  $W_t$  has the coefficient  $W_1$  and  $W_2$  has the coefficient 0, by the following fact:

**Lemma 1.16.** 
$$W_{i,k}(B_i) = W_{i,k}(W_i)$$
 for all  $j = 0, 1, ...$  and  $k = 1, ..., 2^j$ .

*Proof.* We need only note that  $W_{j,k}(\cdot)$  is a linear operation on functions for each j and k and  $W_{j,k}(tW_1) = 0$  by Lemma 1.13.

**Lemma 1.17.** The random variables  $W_{j,k}(B_i)$  for j = 0, 1, ... and  $k = 1, ..., 2^j$  are independent with distribution  $N(0, 2^{-j-2})$ .

*Proof.* We have by the previous lemma

$$W_{j,k}(B_{\cdot}) = W_{j,k}(W_{\cdot}) = W_{(2k-1)/2^{j+1}} - \frac{1}{2} \left[ W_{(k-1)/2^{j}} + W_{k/2^{j}} \right]$$
$$= L(1_{[0,(2k-1)/2^{j+1}]}) - \frac{1}{2} \left[ L(1_{[0,(k-1)/2^{j}]}) + L(1_{[0,k/2^{j}]}) \right]$$

which by linearity of the isonormal process L, Lemma 1.12, equals  $L(g_{i,k})$  where

$$g_{j,k} := 1_{[0,(2k-1)/2^{j+1}]} - \frac{1}{2} \left[ 1_{[0,(k-1)/2^{j}]} + 1_{[0,k/2^{j}]} \right]$$
$$= \frac{1}{2} \left[ 1_{((k-1)/2^{j},(2k-1)/2^{j+1}]} - 1_{((2k-1)/2^{j+1},k/2^{j}]} \right].$$

(These functions  $g_{j,k}$ , multiplied by some constants, are known as Haar functions.) To finish the proof of Lemma 1.17 we will use the following:

**Lemma 1.18.** The functions  $g_{j,k}$  and  $g_{j',k'}$  are orthogonal in  $L^2([0,1])$  (with Lebesgue measure) unless (j,k) = (j',k').

Proof. If j = j', the functions  $g_{j,k}$  are orthogonal for different k since they are supported on non-overlapping intervals  $I_{j,k}$ . If  $j \neq j'$ , say j' < j, then  $g_{j,k}$  is 0 outside of  $I_{j,k}$ , equal to 1/2 on the left half of it and -1/2 on the right half, while  $g_{j',k'}$  is constant on the interval, so the functions are orthogonal, proving Lemma 1.18.

Returning to the proof of Lemma 1.17, we have that L of orthogonal functions are independent normal variables with mean 0, and  $E(L(f)^2) = ||f||^2$ , where

$$||g_{j,k}||^2 = \int_0^1 g_{j,k}(t)^2 dt = 1/2^{j+2}$$

since  $g_{j,k}^2$  equals 1/4 on an interval of length 1/2<sup>j</sup> and is 0 elsewhere. So Lemma 1.17 is proved.

There are other ways of expanding functions on [0,1] beside Schauder bases, for example, Fourier series. Fourier series have the advantage that the terms in the series are orthogonal

functions with respect to Lebesgue measure on [0,1]. The Schauder basis functions are not orthogonal, for example the constant function 1 is not orthogonal to any of the other functions in the sequence, and the functions are all nonnegative, so those whose supports overlap are non-orthogonal. However, the Schauder functions are indefinite integrals of constant multiples of the orthogonal functions  $g_{j,k}$  or equivalently constant multiples of Haar functions, and it turns out that the indefinite integral fits well with the processes we are considering, as in the above proof. In a sense, the Wiener process  $W_t$  is the indefinite integral of the isonormal process L via  $W_t = L(1_{[0,t]})$ .

Let  $\Phi_m$  be the distribution function of the binomial  $\operatorname{bin}(m,1/2)$  distribution,  $\Phi_m(x) := 0$  for x < 0,  $\Phi_m(x) := \sum_{j=0}^k {m \choose k} 2^{-m}$  for  $k \le x < k+1$ , k=0,1,...,m-1, and  $\Phi_m(x) := 1$  for  $x \ge m$ . For a function F from  $\mathbb R$  into itself let  $F^{\leftarrow}(y) := \inf\{x : F(x) \ge y\}$ , as in Lemma 1.3. Let  $H(t|m) := \Phi_m^{\leftarrow}(t)$  for 0 < t < 1.

Now to proceed with the KMT construction, for a given n, let  $B^{(n)}$  be a Brownian bridge process. Let  $V_{0,1} := n$ . Let  $V_{1,1} := H(\Phi(2W_{0,1}(B^{(n)}))|n)$ ,  $V_{1,2} := V_{0,1} - V_{1,1}$ . By Lemma 1.17,  $2W_{0,1}(B^{(n)})$  has law N(0,1), thus  $\Phi$  of it has law U[0,1] by Lemma 1.3(a), and  $V_{1,1}$  has law bin(n,1/2) by Lemma 1.3(b). We will define empirical distribution functions  $U_n$  for the U[0,1] distribution recursively over dyadic rationals, beginning with  $U_n(0) = 0$ ,  $U_n(1) = 1$ , and  $U_n(1/2) = V_{1,1}/n$ . These values have their correct distributions so far. Now given  $V_{j-1,k}$  for some  $j \geq 2$  and all  $k = 1, ..., 2^{j-1}$ , let

$$V_{j,2k-1} := H(\Phi(2^{(j+1)/2}W_{j-1,k}(B^{(n)})|V_{j-1,k})$$

and  $V_{j,2k} := V_{j-1,k} - V_{j,2k-1}$ . This completes the recursive definition of the  $V_{j,i}$ . Then  $W_{j-1,k}(B^{(n)})$  has law  $N(0,2^{-j-1})$  by Lemma 1.17, so  $2^{(j+1)/2}$  times it has law N(0,1), and  $\Phi$  of the product has law U[0,1] by Lemma 1.3(a), so  $V_{j,2k-1}$  has law  $\operatorname{bin}(V_{j-1,k},1/2)$  by Lemma 1.3(b). Let  $U_n(1/4) := V_{2,1}/n$ ,  $U_n(3/4) := U_n(1/2) + V_{2,2}/n$ , and so on. Then  $U_n(k/2^j)$  for  $k = 0, 1, ..., 2^j$  have their correct joint distribution and and when taken for all j = 1, 2, ..., they uniquely define  $U_n$  on [0,1] by monotonicity and right-continuity, which has all the properties of an empirical distribution function for U[0,1].

With the help of Lemma 1.2, one can show that the Schauder coefficients of the empirical process  $\alpha_n := n^{1/2}(U_n - U)$ , where U is the U[0,1] distribution function, are close to those of  $B^{(n)}$ . Lemma 1.2 has to be applied not only for the given n but also for n replaced by  $V_{j,k}$ , and that creates some technical problems. For the present, the proof in the previous section is not rewritten here in terms of the present construction.

#### REFERENCES

Bennett, George W. (1962). Probability inequalities for the sum of bounded random variables. J. Amer. Statist. Assoc. 57, 33–45.

Berkes, I., and Philipp, W. (1979). Approximation theorems for independent and weakly dependent random vectors. *Ann. Probab.* **7**, 29-54.

Bretagnolle, J., and Massart, P. (1989). Hungarian constructions from the nonasymptotic viewpoint. *Ann. Probab.* **17**, 239–256.

Chernoff, H. (1952). A measure of efficiency for tests of a hypothesis based on the sum of observations. *Ann. Math. Statist.* **23**, 493-507.

Csörgő, M., and Horváth, L. (1993). Weighted Approximations in Probability and Statistics. Wiley, Chichester.

Csörgő, M., and Révész, P. (1981). Strong Approximations in Probability and Statistics. Academic, New York.

Donsker, Monroe D. (1952). Justification and extension of Doob's heuristic approach to the Kolmogorov-Smirnov theorems. *Ann. Math. Statist.* **23**, 277–281.

Dudley, Richard M. (1984). A Course on Empirical Processes. Ecole d'été de probabilités de St.-Flour, 1982. Lecture Notes in Math. 1097, 1-142, Springer.

Dudley, R. M. (2002). *Real Analysis and Probability*. Second ed., Cambridge University Press.

Feller, William (1968). An Introduction to Probability Theory and Its Applications. Vol. 1, 3d ed. Wiley, New York.

Hoeffding, W. (1963). Probability inequalities for sums of bounded random variables. *J. Amer. Statist. Assoc.* **58**, 13-30.

Hu, Inchi (1985). A uniform bound for the tail probability of Kolmogorov-Smirnov statistics. *Ann. Statist.* **13**, 821-826.

Komlós, J., Major, P., and Tusnády, G. (1975). An approximation of partial sums of independent RV'-s and the sample DF. I. Z. Wahrscheinlichkeitstheorie verw. Gebiete 32, 111–131.

Mason, D. M. (1998). Notes on the KMT Brownian bridge approximation to the uniform empirical process. Preprint.

Mason, D. M., and van Zwet, W. (1987). A refinement of the KMT inequality for the uniform empirical process. *Ann. Probab.* **15**, 871-884.

Massart, P. (1990). The tight constant in the Dvoretzky-Kiefer-Wolfowitz inequality. *Ann. Probab.* **18**, 1269-1283.

Nanjundiah, T. S. (1959). Note on Stirling's formula. *Amer. Math. Monthly* **66**, 701-703. Okamoto, Masashi (1958). Some Inequalities Relating to the Partial Sum of Binomial Probabilities. *Ann. Inst. Statist. Math.* **10**, 29-35.

Rio, E. (1991). Local invariance principles and its application to density estimation. Prépubl Math. Univ. Paris-Sud 91-71.

Rio, E. (1994). Local invariance principles and their application to density estimation. *Probab. Theory Related Fields* **98**, 21-45.

Shorack, G., and Wellner, J. A. (1986). *Empirical Processes with Applications to Statistics*. Wiley, New York.

Whittaker, E. T., and Watson, G. N. (1927). *Modern Analysis*, 4th ed., Cambridge Univ. Press, Repr. 1962.

---

## THE DELTA-METHOD AND ASYMPTOTICS OF SOME ESTIMATORS

The delta-method gives a way that asymptotic normality can be preserved under nonlinear, but differentiable, transformations. The method is well known; one version of it is given in J. Rice, *Mathematical Statistics and Data Analysis*, 2d. ed., 1995. A simple form of it using only a first derivative, for functions of one variable, will be given here. (A multidimensional version is used in Section 3.7 of Mathematical Statistics, 18.466 course notes by R. Dudley, on the MIT OCW website.)

**Theorem.** Let  $Y_n$  be a sequence of real-valued random variables such that for some  $\mu$  and  $\sigma$ ,  $\sqrt{n}(Y_n - \mu)$  converges in distribution as  $n \to \infty$  to  $N(0, \sigma^2)$ . Let f be a function from  $\mathbb{R}$  into  $\mathbb{R}$  having a derivative  $f'(\mu)$  at  $\mu$ . Then  $\sqrt{n}[f(Y_n) - f(\mu)]$  converges in distribution as  $n \to \infty$  to  $N(0, f'(\mu)^2 \sigma^2)$ .

**Remarks**. In statistics, where  $\mu$  is an unknown parameter, one will want f to be differentiable at all possible  $\mu$  (and preferably, for f' to be continuous, although that is not needed in the proof).

**Proof.** We have  $Y_n - \mu = O_p(1/\sqrt{n})$  as  $n \to \infty$ . Also,  $f(y) = f(\mu) + f'(\mu)(y - \mu) + o(|y - \mu|)$  as  $y \to \mu$  by definition of derivative. Thus

$$f(Y_n) = f(\mu) + f'(\mu)(Y_n - \mu) + o_n(|Y_n - \mu|),$$

SO

$$\sqrt{n}[f(Y_n) - f(\mu)] = f'(\mu)\sqrt{n}(Y_n - \mu) + \sqrt{n}o_p(1/\sqrt{n}).$$

The last term is  $o_p(1)$ , so the conclusion follows.

Let's say a distribution function F has a good median if F has a continuous density F' = f with f(m) > 0 at m, the median of F. More precisely, f(m) > 0 and f continuous at m imply that F is strictly increasing in a neighborhood of m, so m is the unique x with F(x) = 1/2 and so the unique median. Let's find the asymptotic distribution of the sample median. First let n = 2k + 1 odd, so the nth sample median  $m_n = X_{(k+1)}$ . If F is the U[0,1] distribution, let its order statistics be  $U_{(1)} < \cdots < U_{(n)}$ . Recall that  $U_{(j)}$  has a beta distribution  $\beta_{j,n-j+1}$  for each j, so the sample median  $U_{(k+1)}$  has a  $\beta_{k+1,k+1}$  distribution. Its density is  $x^k(1-x)^k/B(k+1,k+1)$  for  $0 \le x \le 1$  and 0 elsewhere. The distribution has mean 1/2 and variance 1/[4(2k+3)] = 1/[4(n+2)].

This beta distribution is asymptotically normal with its mean and variance as  $n \to \infty$  or equivalently  $k \to \infty$ . This fact is a special case of facts known since about 1920, but lacking a handy reference, I'll indicate a proof. Let y = x - (1/2), so  $|y| \le 1/2$  where the density is non-zero. On that interval,

$$x^{k}(1-x)^{k} = \left(\frac{1}{2} + y\right)^{k} \left(\frac{1}{2} - y\right)^{k} = \left(\frac{1}{4} - y^{2}\right)^{k} = 4^{-k}(1 - 4y^{2})^{k}.$$

We have  $(1 - 4y^2)^k \le \exp(-4ky^2)$  for all y with  $|y| \le 1/2$ , and for any constant c and  $|y| \le c/\sqrt{k}$ ,  $k \log(1-4y^2) + 4ky^2 = O(k(4y^2)^2) = O(1/k) = O(1/n)$  as  $n \to \infty$  and  $k \to \infty$ ,

so for such y (depending on k),  $(1-4y^2)^k$  is asymptotic to  $\exp(-4ky^2)$ . It follows that  $\beta_{k+1,k+1}$  is asymptotically normal with mean 1/2 and variance 1/(8k) which is asymptotic to 1/(4n). In other words  $\sqrt{n}[U_{(k+1)}-\frac{1}{2}]$  converges in distribution as  $n\to\infty$  to N(0,1/4).

Now for any distribution function F with a good median m, and n=2k+1 odd, the sample median  $m_n=X_{(k+1)}$  has the distribution of  $F^{\leftarrow}(U_{(k+1)})$  because  $F^{\leftarrow}$  is monotonic (non-decreasing, and strictly increasing in a neighborhood of  $\frac{1}{2}$ ). We have  $F^{\leftarrow}(1/2)=m$ . So by the delta-method theorem above,  $\sqrt{n}(m_n-m)$ , being equal in distribution to  $\sqrt{n}(F^{\leftarrow}(U_{(k+1)})-F^{\leftarrow}(1/2))$ , converges in distribution as  $n\to\infty$  to  $N(0,(F^{\leftarrow})'(1/2)^2/4)=N(0,1/(4f(m)^2))$ , as stated in Randles and Wolfe, p. 227, line 2, for symmetric distributions.

For n=2k even,  $U_{(k)}$  and  $U_{(k+1)}$  have  $\beta_{k,k+1}$  and  $\beta_{k+1,k}$  distributions respectively, and  $|U_{(k+1)}-U_{(k)}|=O_p(1/n)$ . For the sample median  $m_{U,n}=[U_{(k)}+U_{(k+1)}]/2$ , we then also have  $|m_{U,n}-U_{(k)}|=O_p(1/n)$ . By a small adaptation of the argument for the n odd case, we get that  $\sqrt{n}(U_{(k)}-\frac{1}{2})$  converges in distribution to N(0,1/4) as  $n=2k\to\infty$ , and so does  $\sqrt{n}(m_{U,n}-\frac{1}{2})$ . So, for a distribution F with a good median m and sample medians  $m_n$ , we get  $\sqrt{n}(m_n-m)$  converging in distribution as  $n\to\infty$  to  $N(0,1/(4f(m)^2))$ , just as when n is odd and as stated by Randles and Wolfe.

Next, let's consider the Hodges-Lehmann estimator. In this case, beside assuming F has a good median m, we'll assume the distribution is symmetric around m. (If a distribution is symmetric around a point  $\theta$ , then  $\theta$  must be the median.) In other words, there is a density  $f_0$  with  $f_0(-x) = f_0(x)$  for all x,  $f_0(0) > 0$ ,  $f_0$  is continuous at 0, and the density f is  $f_m(x) \equiv f_0(x-m)$ , which is then symmetric around m. Given  $X_1, ..., X_n$  i.i.d. with a distribution F satisfying the given conditions, but otherwise unknown, the Hodges-Lehmann estimator  $\hat{\theta}_{HL}$  is the median of the numbers  $(X_i + X_j)/2$  for  $1 \le i \le j \le n$ . There are n(n+1)/2 of these numbers (which are called Walsh averages). The sample median is an estimator of the unknown m, and  $\hat{\theta}_{HL}$  is another which is often better. To look into it we'll consider some U-statistics. For any real x,  $x_1$ , and  $x_2$  let  $h_x(x_1, x_2) = \Psi(2x - x_1 - x_2)$ . This kernel is symmetric under interchanging  $x_1$  and  $x_2$  for each x.

We want to find the asymptotic behavior of  $\hat{\theta}_{HL} - m$ , specifically, that it's asymptotically normal with mean 0 and variance C/n for some C depending on F. In doing this, we can assume m = 0, because subtracting m from all the observations makes m = 0 and doesn't change the distribution of the difference. So we can assume F is symmetric around 0.

Let G be the distribution function of  $X_1 + X_2$ . Then G has a density g given by the convolution of f with itself,  $g(x) = \int_{-\infty}^{\infty} f(x-y)f(y)dy$ . We have for all x

$$Eh_x(X_1, X_2) = P(X_1 + X_2 < 2x) = G(2x).$$

The quantity called  $\zeta_1$ , entering into the asymptotic variance of the *U*-statistic formed from the kernel  $h_x$ , is given by

$$\zeta_1 = P(X_1 + X_2 < 2x, X_1 + X_3 < 2x) - G(2x)^2.$$

We are interested especially in x = 0 since that is now the median and center of symmetry of F and of G. For x = 0 we get

$$P(X_1 + X_2 < 0, X_1 + X_3 < 0) = \int_{-\infty}^{\infty} F(-u)^2 dF(u) =$$

$$\int_{-\infty}^{\infty} [1 - F(u)]^2 dF(u) = \int_{0}^{1} (1 - t)^2 dt = 1/3,$$

and  $Eh_0 = 1/2$ , so  $\zeta_1 = 1/12$ . We have a kernel of order r = 2, and the asymptotic variance of a *U*-statistic is  $r^2\zeta_1$ . Defining a *U*-statistic depending on x we have

$$U_{(x)}^{(n)} = \binom{n}{2}^{-1} \sum_{1 \le i \le j \le n} \Psi(x - X_i - X_j).$$

For x=0, bearing in mind that under symmetry around  $0, -X_i-X_j$  is equal in distribution to  $X_i+X_j$ , this becomes the *U*-statistic that Randles and Wolfe call  $U_4$  and is closely related to the Wilcoxon signed-rank statistic. We get that  $\sqrt{n}(U_{(x=0)}^{(n)}-\frac{1}{2})$  converges in distribution as  $n\to\infty$  to N(0,1/3).

If we included all the terms with i=j in the sum defining the U-statistic, giving another statistic  $V^{(n)}$ , it would make a difference of O(n) in the sum, thus O(1/n) in  $U^{(n)}$ , thus  $O(1/\sqrt{n})$  in  $\sqrt{n}U^{(n)}$ , so  $\sqrt{n}(V^{(n)}-\frac{1}{2})$  also has a distribution converging to N(0,1/3). In other words,  $V^{(n)}=\frac{1}{2}+Z_n/\sqrt{3n}+o_p(1/\sqrt{n})$  where  $Z_n$  converges in distribution to N(0,1) as  $n\to\infty$ .

The Hodges-Lehmann estimate  $\hat{\theta}_{HL}$  is an x for which  $V_{(x)}^{(n)} = \frac{1}{2} + O(1/n^2)$ . For x near 0, specifically  $|x| = O(1/\sqrt{n})$ ,  $Eh_x = G(2x)$  which will be within  $O(1/\sqrt{n})$  of 1/2. The asymptotic variance of  $V_{(x)}^{(n)}$  will still be 1/(3n) plus smaller terms that don't affect the asymptotic distribution. So we will have, where again  $Z_n$  is asymptotically N(0,1),

$$V_{(x)}^{(n)} = G(2x) + Z_n / \sqrt{3n} + o_p(1/\sqrt{n}).$$

If this equals 1/2 (within  $O(1/n^2)$ ), then

$$\hat{\theta}_{HL} = x = \frac{1}{2}G^{\leftarrow} \left(\frac{1}{2} - (Z_n/\sqrt{3n})\right) + o_p(1/\sqrt{n}).$$

It follows by the delta-method that the distribution of  $\sqrt{n}(\hat{\theta}_{HL} - m) = \sqrt{n}\hat{\theta}_{HL}$  converges to  $N(0, \sigma^2)$  where

$$\sigma^2 = (G^{\leftarrow})'(1/2)^2/12 = 1/(12G'(0)^2) = 1/(12g(0)^2)$$

and by convolution  $g(0) = \int_{-\infty}^{\infty} f(0-x)f(x)dx = \int_{-\infty}^{\infty} f(x)^2 dx$  by symmetry. So the asymptotic variance of the Hodges-Lehmann statistic is  $1/[12n\{\int_{-\infty}^{\infty} f(x)^2 dx\}^2]$ , as indicated by Randles and Wolfe on p. 228, (7.3.12) and (7.3.14).

Note. We considered a family of U-statistics indexed by a parameter x. There is a theory of such families, called U-processes, begun in some papers by Deborah Nolan and David Pollard in Annals of Statistics. In the present case, since  $U_{(x)}^{(n)}$  is non-decreasing in x, we have a relatively simple U-process, but still, the argument was incomplete.

---

#### Some notes on location and scatter functionals

Recall that a sequence  $Q_k$  of laws (probability measures), here on  $\mathbb{R}^d$ , is said to converge weakly to a law Q if  $\int f dQ_k \to \int f dQ$  for every bounded continuous function f. There exists a metric  $\rho$  on the set of all laws on  $\mathbb{R}^d$  which metrizes weak convergence, in other words  $Q_k \to Q$  weakly if and only if  $\rho(Q_k, Q) \to 0$ , e.g. Dudley (2002, Sec. 11.3). A set U of laws is called weakly open if and only if whenever  $Q \in U$  and  $Q_k \to Q$  weakly we have  $Q_k \in U$  for all k large enough. Equivalently, for each  $Q \in U$ , there is an r > 0 such that whenever  $\rho(Q, P) < r$  we have  $P \in U$ .

Much of robustness theory emphasizes mixture laws

$$P = (1 - \lambda)F_0 + \lambda Q \tag{1}$$

where Q is an arbitrary "contaminating" distribution,  $F_0$  is a special distribution with a density, say for definiteness a normal, and  $0 \le \lambda < 1/2$ , e.g. Huber [20, pp. 86, 89]. Despite the generality of Q, the contamination model (1) doesn't include some, perhaps the majority, of laws P treated as normal to an acceptable approximation in practice, such as laws P on  $\mathbb{R}$  with  $P([0,\infty))=1$ , and laws discretized by rounding to finitely many decimal places. The latter laws also cannot be obtained by replacement of up to half a normal or other continuous law, but can be quite close to normal laws in metrics for the weak topology. Huber [20, p. 3] says that "in the physical sciences typical 'good data' samples appear to be well modeled by an error law" (1) with  $0.01 \le \lambda \le 0.1$ . But, "modeled" seems to allow a further approximation and "error" seems to exclude many, perhaps most, data sets.

Another basic notion in robustness theory is that of breakdown point. Before giving some definitions of them, here are remarks on *Notations with*  $\delta$ : below, " $\delta$ " is used in the following three ways:  $\delta_x$  (without any superscript) denotes the law which is a point mass at x;  $\delta^*$  with varying subscripts will be breakdown points, to be defined; and  $\delta$  with neither subscript nor superscript will be a (small) number, usually introduced by "for any  $\delta > 0$ " or the like.

Some definitions of breakdown points are for estimators  $T_n$  defined on a finite sample of size n under replacement of a fraction k/n of the observations by arbitrary values, or by adjoining k new such values to the data. Then the asymptotics of the breakdown point (largest k/n for replacement, or

k/(n+k) for adjunction, such that  $T_n$  doesn't escape from all compact sets) as  $n \to \infty$  are considered. Another type of definition is for functionals T defined on laws P, which yield estimators when applied to empirical measures  $P_n$ . In a functional definition one has a set of neighborhoods  $N_{\varepsilon}(P)$  of P indexed by  $\varepsilon > 0$ . These may be defined by a metric d on laws through  $N_{\varepsilon}(P) := N_{\varepsilon,d}(P) := \{Q : d(Q,P) < \varepsilon\}$ , or in most of the literature, as contamination neighborhoods, for  $0 < \varepsilon \le 1$  (nearly always  $\varepsilon \le 1/2$ ),

$$N_{\varepsilon}^{C}(P) := \{Q = (1 - \lambda)P + \lambda \rho : 0 \le \lambda \le \varepsilon, \ \rho \text{ any law}\}.$$

The total variation distance between two laws P and Q on a sample space  $(X, \mathcal{B})$  is

$$d_1(P,Q) := \sup_{A \in \mathcal{B}} |(P-Q)(A)| = \sup_{A \in \mathcal{B}} (P-Q)(A) = \sup_{B \in \mathcal{B}} (Q-P)(B)$$

by the Hahn-Jordan decomposition, e.g. Dudley (2002, Theorem 5.6.1). Total variation for laws corresponds approximately to replacement for finite samples. If  $\mathcal{P} := \mathcal{P}(X,\mathcal{B})$  is the set of all laws on a sample space  $(X,\mathcal{B})$ , and for each  $P \in \mathcal{P}$ ,  $\{N_{\varepsilon}(P)\}_{0 \leq \varepsilon < \infty}$  is a collection of subsets of  $\mathcal{P}$ , then  $\{N_{\varepsilon}(P): 0 \leq \varepsilon < \infty, P \in \mathcal{P}\}$  will be called a *suitable set of neighborhoods* iff for all  $P \in \mathcal{P}$ , (a)  $N_0(P) = \{P\}$ , (b) For  $0 \leq \varepsilon < \varepsilon'$ ,  $N_{\varepsilon}(P) \subset N_{\varepsilon'}(P)$ , and (c) For  $\varepsilon > 0$ ,  $\varepsilon' > 0$ ,  $Q \in N_{\varepsilon}(P)$ , and  $\rho \in N_{\varepsilon'}(Q)$ , we have  $\rho \in N_{\varepsilon+\varepsilon'}(P)$ .

These conditions clearly hold for neighborhoods defined by metrics. They also hold for contamination neighborhoods if we define  $N_{\varepsilon}^{C}(P) := N_{1}^{C}(P) = \mathcal{P}$  for  $\varepsilon > 1$ .

In most definitions found in the literature, T takes values in a parameter space  $\Theta$  with a topology and for  $\varepsilon > \varepsilon^*(T, P)$ , the breakdown point at P, there is no proper compact subset  $K \subset \Theta$  such that T on  $N_{\varepsilon}(P)$  takes values in K. (For non-compact parameter spaces, as in these notes, "proper" is redundant.)

A set of n points in  $\mathbb{R}^d$  are said to be in *general position* if for  $k = 0, 1, \ldots, d-1$ , no k-dimensional hyperplane contains k+2 or more of the points.

Many authors consider breakdown points of functionals in the contamination sense at laws P on  $\mathbb{R}^d$  such that P(H) = 0 for any hyperplane H of dimension d-1. I.i.d. samples from such laws are almost surely in general position. On finite samples, breakdown (in the replacement or contamination

sense) is usually considered for samples in general position. At other laws or samples, the breakdown points may be lower.

Another issue is: for  $0 < \varepsilon < \varepsilon^*$ , is T required to be uniquely defined at all  $Q \in N_{\varepsilon}(P)$ ? Different answers might be deduced from the literature. On the "no" side, the Rousseeuw minimum-volume-ellipsoid (MVE) functional, to be defined after Proposition 2, has been generally agreed to have breakdown point 1/2 at suitable P although it had only been shown to be uniquely defined at symmetric, unimodal distributions satisfying further restrictions, as in Tatsuoka and Tyler [35]; this set is not dense in  $N_{\varepsilon}(P)$  for any  $\varepsilon > 0$ , for any of the families of neighborhoods mentioned so far. On the "yes" side, proofs of upper bounds for the breakdown points of some M-functionals (Hampel, Ronchetti, Rousseeuw and Stahel [17, §5.5(a) p. 298]; Tyler [36]) assume that the functionals are defined on contamination neighborhoods of a normal law, or of finite samples in general position, respectively. Since each answer is of independent interest, separate definitions will be given.

**Definition**. Let  $\Theta$  be a topological space,  $(X, \mathcal{B})$  a sample space, and  $\{N_{\varepsilon}(P), 0 \leq \varepsilon < \infty, P \in \mathcal{P} := \mathcal{P}(X, \mathcal{B})\}$  a suitable set of neighborhoods. Let T be a functional defined uniquely on a domain  $\mathcal{D} \subset \mathcal{P}$  with values in  $\Theta$ . Then for each  $P \in \mathcal{D}$ , the *explosion breakdown point* of T at P is

$$\varepsilon^*(T,P) := \varepsilon^*(T,P,\{N_\varepsilon\}_{0 \le \varepsilon < \infty},\Theta) := \inf\{\varepsilon \in [0,1] :$$

for each compact  $K \subset \Theta$ ,  $T(Q) \notin K$  for some  $Q \in \mathcal{D} \cap N_{\varepsilon}(P)$ .

If there is no such  $\varepsilon$ , set  $\varepsilon^* := 1$ . Let  $\varepsilon_C^*(T, P)$  denote the explosion breakdown point for contamination neighborhoods, and  $\varepsilon_d^*(T, P)$  the one for d-neighborhoods.

The next definition, of  $\delta^*$ , requires T to be uniquely defined on some neighborhoods. Sometimes T becomes undefined only just after escaping from compact sets, so that  $\delta^* = \varepsilon^*$ .

**Definition**. Let  $\delta^*(T, P)$ , the definition-explosion breakdown point of T at P, be defined as the supremum of  $\varepsilon$  with  $0 < \varepsilon < \varepsilon^*(T, P)$  such that  $N_{\varepsilon}(P) \subset \mathcal{D}$ , or 0 if there is no such  $\varepsilon$ . Define  $\delta_C^*$  and  $\delta_d^*$  by analogy with  $\varepsilon_C^*$  and  $\varepsilon_d^*$ .

Here is a further definition, of  $r^*$ . It will not be called a breakdown point since discontinuity has not generally been considered as breakdown.

**Definition**. Let  $r^*(T, P)$ , the radius of continuity of T at P, be defined as  $\delta^*(T, P)$  with the additional requirement that  $T(\cdot)$  is weakly continuous at Q for all  $Q \in N_{\varepsilon}(P)$ . Define  $r_C^*$  and  $r_d^*$  again analogously.

If neighborhoods  $N_{\varepsilon}$  are defined by the total variation (replacement) distance  $d_1$  then the corresponding breakdown points and radii will be written as  $\varepsilon_R^* := \varepsilon_{d_1}^*$ . If  $Q = (1 - \lambda)P + \lambda \rho$  for any law  $\rho$  then clearly  $d_1(P,Q) \leq \lambda$ , with equality if  $\rho$  is singular with respect to P. Thus  $\varepsilon_R^* \leq \varepsilon_C^*$  and likewise for  $\delta^*$  and  $r^*$ .

Notions of "location" and "scale" or multidimensional "scatter" functional will be defined in terms of equivariance, as follows.

**Definitions.** Let  $\mathcal{N}_d$  be the set of symmetric nonnegative definite  $d \times d$  matrices and  $\mathcal{P}_d$  its subset of strictly positive definite matrices. Let  $Q \mapsto \mu(Q) \in \mathbb{R}^d$ , resp.  $\Sigma(Q) \in \mathcal{N}_d$ , be a functional defined on a set  $\mathcal{D}$  of laws Q on  $\mathbb{R}^d$ . Then  $\mu$  (resp.  $\Sigma$ ) is called an affinely equivariant location (resp. scatter) functional iff for any nonsingular  $d \times d$  matrix A and  $v \in \mathbb{R}^d$ , with f(x) := Ax + v, and any law  $Q \in \mathcal{D}$ , the image measure  $P := Q \circ f^{-1} \in \mathcal{D}$  also, with  $\mu(P) = A\mu(Q) + v$  or, respectively,  $\Sigma(P) = A\Sigma(Q)A'$ . For d = 1,  $\sigma(\cdot)$  with  $0 \le \sigma < \infty$  will be called an affinely equivariant scale functional iff  $\sigma^2$  satisfies the definition of affinely equivariant scatter functional. If we have affinely equivariant location and scatter functionals  $\mu$  and  $\Sigma$  on the same domain  $\mathcal{D}$  then  $(\mu, \Sigma)$  will be called an affinely equivariant location-scatter functional on  $\mathcal{D}$ , and likewise for a location-scale functional  $(\mu, \sigma)$ .

Dispersion often occurs in the literature as a synonym for "scatter." Clearly, for laws Q with finite second moments, the mean  $\mu(Q)$  and covariance matrix  $\Sigma(Q)$  give affinely equivariant location and scatter functionals.

The median is an affinely equivariant location functional with  $\delta_C^* = 1/2$  at any law. The MAD is an affinely equivariant scale functional with  $\delta_C^*(\text{MAD}, P) \equiv 1/2$  also if the scale parameter space is taken as  $0 \le \sigma < \infty$ . If  $\sigma > 0$  is required, however, the MAD is not defined at laws P with  $p := \sup\{P(\{t\}) : t \in \mathbb{R}\} > 1/2$  and at other laws P has  $\delta_C^*(\text{MAD}, P) = \beta = (\frac{1}{2} - p)/(1 - p)$ , with  $\beta = 1/2$  only for continuous laws P. Such a dependence on  $\Theta$  naturally also occurs for other scale functionals, e.g. the interquartile range.

Let T be an affinely equivariant location or scatter functional. Then  $\varepsilon_C^*$ ,  $\delta_C^*$ , and  $r_C^*$  are all affinely invariant and 1/2 as a target maximal value for

 $\varepsilon_C^*$  has been much emphasized in the literature. As will be seen, however, striving for  $\varepsilon_C^* = 1/2$  has led to some functionals for which  $\delta_C^* = 0$  or  $r_d^*$  may be 0 (even at laws with smooth densities).

For metrics d that metrize that weak topology and so are not affinely invariant (e.g. the Prohorov metric, Dudley, 2002, Sec. 11.3),  $\varepsilon_d^*$ ,  $\delta_d^*$  and  $r_d^*$  may still be affinely invariant (if they are constant!), e.g. for T the median and d the Prohorov metric,  $\varepsilon_d^*(T,P) = \delta_d^*(T,P) \equiv 1/2 > 0 \equiv r_d^*(T,P)$  for all P. But e.g. for T = MAD and  $\Theta = (0,\infty)$ ,  $\varepsilon_d^* = \delta_d^*$  is not affinely invariant. On the other hand the sets where  $\varepsilon_d^* > 0$ ,  $\delta_d^* > 0$  and  $r_d^* > 0$  are affinely invariant. Thus, one may seek T for which these sets are as large as possible, rather than making the values of  $\varepsilon^*$  as large as possible.

Location functionals which in some respects improve on the median and still have  $\delta_C^* = 1/2$  at all laws have been proposed, especially by Huber, e.g. [20, pp. 52-53, (5.22) p. 86]. Such functionals can be adjusted for scale, e.g. using the MAD, to make them equivariant [20, §§6.4-6.7], and can be defined when the scale functional  $\sigma = 0$ , as we saw in earlier handouts.

The requirement of affine equivariance seems to be especially natural for laws on  $\mathbb{R}$ . In  $\mathbb{R}^d$  for  $d \geq 1$ , the *spatial median* for a random vector X or its law is an m that minimizes E(|X-m|-|X|). For d=1, m satisfies this iff it is a median of X. For  $d \geq 2$  the spatial median is unique except for distributions concentrated in lines with non-unique medians there [28], as also shown in a handout. The spatial median is equivariant under Euclidean transformations where A is an orthogonal transformation, or a constant multiple of one, but not under general affine transformations for d > 1.

The following easy fact gives consequences of affine equivariance without any further assumptions.

**Theorem 1.** Let  $\mu(\cdot)$  be an affinely equivariant location functional defined on a class  $\mathcal{D}$  of laws on  $\mathbb{R}^d$ , and let  $\mathcal{A}$  be a set of non-singular affine transformations of  $\mathbb{R}^d$ . Let  $P \in \mathcal{D}$  be such that  $P \circ A^{-1} = P$  for each  $A \in \mathcal{A}$ . Then

- (a)  $\mu(P) \in S_{\mathcal{A}} := \{ x \in \mathbb{R}^d : Ax = x \text{ for all } A \in \mathcal{A} \}.$
- (b) If  $S_A$  is a singleton  $\{x_A\}$ , then  $\mu(P) = x_A$ .
- (c) If for some  $v \in \mathbb{R}^d$ ,  $\mathcal{A}$  consists of the one map  $x \mapsto 2v x$ , then  $\mu(P) = v$ .
- (d) Let  $2 \le n \le d+1$ . Let V be a set of n points of  $\mathbb{R}^d$  in general position. Then for any of the n! permutations  $\pi$  of the points of V, there is a non-singular affine  $A_{\pi}$ , uniquely determined on the unique (n-1)-dimensional

hyperplane H including V, with  $A_{\pi}(v) = \pi(v)$  for each  $v \in V$ . If the hypotheses on P hold for A equal to the set of all these  $A_{\pi}$ , and P(H) = 1, then  $\mu(P) = n^{-1} \sum_{v \in V} v$ .

(e) In part (d), suppose n = d + 1 and the points of V are the vertices of a regular simplex. Let  $\Sigma$  be an affinely equivariant scatter functional. Then  $\Sigma(P) = cI$  for some  $c \geq 0$  where I is the  $d \times d$  identity matrix.

**Proof.** Part (a) follows directly from the definition of equivariant location functional. Then part (b) follows from part (a). For part (c), note that  $x \mapsto 2v - x$  has a unique fixed point v, so (c) follows from (b); here P is symmetric around v.

For part (d), let  $x_1, ..., x_n$  be the points of V. Since they are in general position, the vectors  $v_j = x_j - x_1$  for j = 2, ..., n are linearly independent. Let  $y_1, ..., y_n$  be the vertices of a regular (n-1)-dimensional simplex with all edges of equal length. Then clearly  $y_1, ..., y_n$  are also in general position and  $w_j = y_j - y_1$  for j = 2, ..., n are linearly independent. Thus there is a nonsingular linear transformation (matrix) B with  $Bv_j = w_j$  for j = 2, ..., n. Defining a non-singular affine transformation by  $Ax = B(x - x_1) + y_1 = Bx + (y_1 - Bx_1)$  we have  $Ax_j = y_j$  for j = 1, ..., n, so we can assume that  $x_j$  are the vertices of a regular simplex.

Recall from group theory that any permutation can be obtained by composing transpositions, so given any two points u, v of V we need to find an affine A with Au = v, Av = u, and Aw = w for all  $w \in V$  other than u and v. For V the set of vertices of a regular simplex, we can take A as reflection in the (d-1)-dimensional hyperplane perpendicular to u-v and through the midpoint of the line segment from u to v, so the affine transformations  $A_{\pi}$  exist.

Let  $W:=\{\sum_{i=2}^n s_i(x_i-x_1): s_i\in\mathbb{R},\ i=2,...,n\}$ , an (n-1)-dimensional linear subspace of  $\mathbb{R}^d$ . Then  $W=\{\sum_{i=1}^n t_ix_i:\ t_i\in\mathbb{R},\ i=1,...,n,\sum_{j=1}^n t_j=0\}$ , as is seen by the relations  $t_i=s_i$  for i=2,...,n and  $t_1=-\sum_{j=2}^n s_j$ . For a given point of W, the numbers  $s_i$  or  $t_i$  are uniquely determined. It's easily seen that  $H=x_1+W=\{x_1+w:\ w\in W\}$ . Then  $H=\{\sum_{j=1}^n \lambda_j x_j:\ \lambda_j\in\mathbb{R},\ j=1,...,n,\ \sum_{j=1}^n \lambda_j=1\}$ , where  $\lambda_1=1+t_1$  and  $\lambda_j=t_j$  for j=2,...,n, and the  $\lambda_j$  are uniquely determined. If A is any affine transformation of  $\mathbb{R}^d$ , then for any  $\{\lambda_j\}_{j=1}^n\in\mathbb{R}^n$  with  $\sum_{j=1}^n \lambda_j=1,\ A\left(\sum_{j=1}^n \lambda_j x_j\right)=\sum_{j=1}^n \lambda_j A(x_j)$ . If A leaves each  $x_j$  fixed, it follows that A leaves fixed each point of H, so A is uniquely determined on H as stated.

There is an affine transformation  $A_H$  of  $\mathbb{R}^d$  such that  $A_H x = x$  for all x in H and  $A_H y \neq y$  for all y not in H. Then  $A_H$  induces the identity permutatation of V, and we can assume it is the affine transformation chosen to do so since P(H) = 1 and so  $P \circ A_H^{-1} = P$ . Thus by part (a),  $\mu(P) \in H$ .

Let  $\pi$  be a permutation interchanging  $x_i$  and  $x_j$  for some  $i \neq j$  and  $A_{\pi}$  the corresponding affine transformation. We have  $\mu(P) = \sum_{j=1}^{n} \lambda_j x_j$  for some real  $\lambda_j$  with sum 1, and  $\mu(P) = A_{\pi}\mu(P) = \mu(P) + (\lambda_i - \lambda_j)(x_j - x_i)$ , so  $\lambda_i = \lambda_j$ , and  $\lambda_i = 1/n$  for all i, so  $\mu(P) = n^{-1} \sum_{v \in V} v$ , proving (d).

For part (e), we can assume  $\sum_{v \in V} v = 0$ . Let  $v \neq w$  in V and let  $S := V \setminus \{v, w\}$ . Let A be the linear transformation interchanging v and w and leaving each  $s \in S$  fixed. Then A is the reflection in the linear subspace spanned by S, which contains (v + w)/2. By affine equivariance it follows that v - w is an eigenvector of  $\Sigma(P) \in \mathcal{N}_d$ . Eigenvectors with distinct eigenvalues are orthogonal, but for  $v \neq u \neq w$  in V, v - w and v - u are not orthogonal, so they must have the same eigenvalue. Iterating, we find that all such eigenvectors have the same eigenvalue  $c \geq 0$ . Since they span  $\mathbb{R}^d$ ,  $\Sigma(P) = cI$  follows.  $\square$ 

In part (c), of course, not all symmetric distributions P are necessarily in the domain  $\mathcal{D}$  on which  $\mu(\cdot)$  is (uniquely) defined. To put all symmetric distributions in  $\mathcal{D}$  could violate some other useful property of  $\mu(\cdot)$ , as Tatsuoka and Tyler [35, p. 1235]) note. One can look for  $\mu(\cdot)$  with good properties defined on as many symmetric laws as possible.

The simplest special case of Theorem 1 part (d) is that P puts mass 1/n in each point of V. That case is natural in that any simplex is affinely equivalent to a regular simplex with all vertices equidistant, whose centroid is the obvious location. Yet, if n-1 observations are close together and the nth moves far away, it retains its non-robust influence. By nesting multiple such simplices for n=d+1, Donoho and Gasko [10] illustrate why the breakdown point of a purportedly robust estimator is as low as 1/(d+1), a bound which, apparently for different reasons, they also found for another class of estimators, as Maronna [26] did earlier for equivariant M-estimators of location and scatter.

Here is a related consequence of Theorem 1, not directly about breakdown points:

**Proposition 2.** For d = 1, 2, ..., there is a sequence  $\{Q_m\}_{m \geq 3}$  of laws on  $\mathbb{R}^d$  having densities such that for a compact set  $K \subset \mathbb{R}^d$ , for all  $m \geq 3$ ,

 $Q_m(K) = d/(d+1)$  and there exist  $\mu_m \in \mathbb{R}^d$  such that for every affinely equivariant location functional  $\mu(\cdot)$  defined at  $Q_m$ ,  $\mu(Q_m) = \mu_m$ , and  $|\mu_m| \to \infty$  as  $m \to \infty$ .

**Proof.** Let V be the set of d+1 vertices of a regular simplex S such that  $e_1:=(1,0,\ldots,0)'\in V$ , the other d vertices all are in the subspace where  $x_1=0$ , and the centroid of S is  $e_1/(d+1)$ . All points of V are within a distance 1 of 0. Let  $P_{d+1}:=\frac{1}{d+1}\sum_{v\in V}\delta_v$ . For any r>0 let  $U_r$  be the uniform distribution on the ball in  $\mathbb{R}^d$  with center 0 and radius r. Let  $\rho_r:=P_{d+1}*U_r$ , which has a density. For  $\mathcal{A}$  as in Theorem 1(e) and (d), since each  $A\in\mathcal{A}$  is an orthogonal transformation preserving  $U_r$ , we have  $\rho_r\circ A^{-1}=\rho_r$ . Let  $\mu(\cdot)$  be an affinely equivariant location functional defined at  $\rho_r$ . Then  $\mu(\rho_r)=e_1/(d+1)$ . Let  $M_a((x_1,\ldots,x_d)'):=(ax_1,x_2,\ldots,x_d)'$  for any a>0 and  $\tau_r:=\rho_r\circ M_{1/r}^{-1}$ . Then for  $r\leq 1/3$ ,  $\tau_r$  has probability 1/(d+1) in the half-space  $x_1\geq (1/r)-1$  and d/(d+1) in the ball  $K:=\{x:|x|\leq 2\}$ , with  $|\mu(\tau_r)|=1/[r(d+1)]$  if  $\mu(\tau_r)$  is defined. Letting  $Q_m:=\tau_{1/m}$  for  $m\geq 3$  gives the conclusion.  $\square$ 

Rousseeuw [30] defined the minimum-volume ellipsoid (MVE) locationscatter estimator whose functional form is as follows. Given a law P on  $\mathbb{R}^d$ , suppose there is a unique ellipsoid  $E = \{x : (x - \mu)'C^{-1}(x - \mu) \leq 1\}$  of smallest d-dimensional volume with  $P(E) \geq 1/2$ , where x and  $\mu$  are column vectors in  $\mathbb{R}^d$  and C is a positive definite symmetric  $d \times d$  matrix. Dividing Cby a constant  $c_d > 0$  depending on d we can write  $E = \{x : (x - \mu)'\Sigma^{-1}(x - \mu) \leq c_d\}$ , where  $c_d$  is chosen so that if P is a normal distribution,  $\Sigma$  is its covariance matrix. Then  $\mu$  and  $\Sigma$  are affinely equivariant location and scatter functionals of P respectively, because any affine transformation Awith  $Ax \equiv Bx + v$  takes ellipsoids to ellipsoids and multiplies all volumes by the same (Jacobian) factor det B.

For a finite sample of size n, if  $\lfloor x \rfloor$  denotes the largest integer  $\leq x$ , the MVE was originally defined in terms of the ellipsoid of smallest volume containing  $\lfloor n/2 \rfloor + 1$  of the sample points. Later, this was adjusted to require E to contain  $\lfloor (n+d+1)/2 \rfloor$  points, with the aim of maximizing the finite-sample breakdown point. In either case, asymptotically as  $n \to \infty$ , one gets the minimum-volume ellipsoid with probability  $\geq 1/2$ , if it is unique.

Location-scatter functionals with  $\varepsilon_C^* = 1/2$  (at continuous distributions) for all d have been proposed, including the Rousseeuw minimum-volume-

ellipsoid estimator just defined ([30], [5]), but  $\delta_C^*$  for it is 0 as shown in Section 3 below.

Proposition 2 showed that mass 1/(d+1) escaping to  $\infty$  can cause breakdown of quite general equivariant location functionals provided that the remaining d/(d+1) of the mass, while remaining in a compact set, approaches some restricted limit (the limit apparently cannot have a density). In the given proof, the limit is concentrated in a union of d line segments parallel to the  $x_1$  axis and so gives mass k/(d+1) to some k-dimensional hyperplanes for  $k=1,\ldots,d-1$ .

Proposition 6 will show that any affinely equivariant location functional  $\mu(\cdot)$  on  $\mathbb{R}$ , if it has  $\delta_C^* = 1/2$  at one or more laws, cannot be extended to be weakly continuous at the law  $Q = \frac{1}{2}(\delta_0 + \delta_1)$ . For a nonparametric location functional this is a drawback since by Theorem 1(c),  $\mu(Q)$  naturally would be defined as 1/2. On the other hand there do exist location and scale functionals  $\mu$  and  $\sigma$ , defined and weakly continuous on all laws on  $\mathbb{R}$  and affinely equivariant, with  $\delta_C^* = \alpha$  at every law, for any  $\alpha$  with  $0 < \alpha < 1/2$ , via trimming (Section 3). Thus the notion of 1/2 as "optimal" breakdown point, often stated in the literature, may not apply from a nonparametric viewpoint.

# 1 Nonexistence facts in dimension 2 or higher

Call a location functional  $\mu(\cdot)$  or a scatter functional  $\Sigma(\cdot)$  singularly affine equivariant if in the definition of affine equivariance A can be any matrix, possibly singular. It's easily seen that if a functional is defined on all laws, affinely equivariant, and weakly continuous, then it is singularly affine equivariant. For empirical measures  $P_n = n^{-1}(\delta_{X_1} + \cdots + \delta_{X_n})$ , the classical sample mean and covariance are evidently singularly affine equivariant. It turns out that in dimension  $d \geq 2$ , there are essentially no other singularly affine equivariant location and scatter functionals, and so weak continuity at all laws is not possible. First the known fact for location will be recalled, then an at least partially known fact for scatter will be stated and proved.

Let X be a  $d \times n$  data matrix whose jth column is  $X_j \in \mathbb{R}^d$ . Let  $X^i$  be the ith row of X. Let  $1_n$  be the  $n \times 1$  vector with all components 1. Let  $\overline{X} = \int x dP_n$  be the sample mean vector in  $\mathbb{R}^d$ , so that  $X - \overline{X}1'_n$  is the centered data matrix. Note that  $P_n$ , and thus  $\overline{X}$  and  $\Sigma(X)$ , are preserved

by any permutation of the columns of X. The next fact was proved in detail in the handout "Non-existence of some affinely equivariant functionals in dimension  $d \geq 2$ ."

**Theorem 3.** (a) If  $\mu(\cdot)$  is a singularly affine equivariant location functional (estimator) defined for all  $P_n$  on  $\mathbb{R}^d$  for  $d \geq 2$  and a fixed n, then  $\mu(P_n) \equiv \int x dP_n$ , the sample mean.

(b) If in addition  $\mu(\cdot)$  is defined for all n and all  $P_n$  on  $\mathbb{R}^d$ , then as n varies,  $\mu(\cdot)$  is not weakly continuous. Thus, there is no affinely equivariant, weakly continuous location functional defined on all laws on  $\mathbb{R}^d$  for  $d \geq 2$ .

**Proof.** Part (a) follows from a result and proof of Obenchain [29, Lemma 1] and permutation invariance, as noted in an unpublished paper of Donoho and by Rousseeuw [30], [31, Proposition 2]. Then (b) follows directly, for  $x_1 = n, x_2 = \cdots = x_n = 0, n \to \infty$ .  $\square$ 

Next is a related fact about scatter functionals. Davies [7, p. 1879] made a statement closely related to part (b), strong but not quite in the same generality, and very briefly indicated a proof by saying that the fact "corresponds" to one for location functionals, as in the preceding theorem. I don't know a reference for part (a), so a proof will be given.

**Theorem 4.** (a) Let  $\Sigma(\cdot)$  be a singularly affine equivariant scatter functional defined on all empirical measures  $P_n$  on  $\mathbb{R}^d$  for  $d \geq 2$  and some fixed  $n \geq 2$ . Write  $\Sigma(X) := \Sigma(P_n)$ . Then there is a constant  $c_n \geq 0$ , depending on  $\Sigma(\cdot)$ , such that for any X,  $\Sigma(X-\overline{X}1'_n) = c_n(X-\overline{X}1'_n)(X-\overline{X}1'_n)'$ . In other words, applied to centered data matrices,  $\Sigma$  is proportional to the sample covariance matrix.

(b) If  $\Sigma(\cdot)$  is an affinely equivariant scatter functional defined for all n and  $P_n$  on  $\mathbb{R}^d$  for  $d \geq 2$ , weakly continuous as a function of  $P_n$ , then  $\Sigma \equiv 0$ .

**Proof.** (a) We have  $\Sigma(BX) = B\Sigma(X)B'$  for any  $d \times d$  matrix B. For any  $U, V \in \mathbb{R}^n$  let  $X^1 = U'$ ,  $X^2 = V'$ , and  $(U, V) := \Sigma_{12}(X)$ . Then  $(\cdot, \cdot)$  is well-defined, letting  $B_{11} = B_{22} = 1$  and  $B_{ij} = 0$  otherwise. It will be shown that  $(\cdot, \cdot)$  is a semi-inner product. We have  $(U, V) \equiv (V, U)$  via B with  $B_{12} = B_{21} = 1$  and  $B_{ij} = 0$  otherwise, since  $\Sigma$  is symmetric. For  $B_{11} = B_{21} = 1$  and  $B_{ij} = 0$  otherwise we get for any  $U \in \mathbb{R}^n$  that

$$(U,U) = \Sigma_{12}(BX) = (B\Sigma(X)B')_{12} = \Sigma_{11}(X) \ge 0.$$
 (2)

For constants a and b,  $(aU, bV) \equiv ab(U, V)$  follows for  $B_{11} = a$ ,  $B_{22} = b$ , and  $B_{ij} = 0$  otherwise. It remains to prove biadditivity  $(U, V + W) \equiv (U, V) + (U, W)$ . For  $d \geq 3$  this is easy, letting  $X^3 = W$ ,  $B_{11} = B_{22} = B_{23} = 1$ , and  $B_{ij} = 0$  otherwise. For d = 2, we first get (U + V, V) = (U, V) + (V, V) from  $B = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$ . Symmetrically, (U, U + V) = (U, U) + (U, V). Then from  $B = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$  we get

$$(U+V,U+V) = (U,U) + 2(U,V) + (V,V).$$
(3)

Letting  $||W||^2 := (W, W)$  for any  $W \in \mathbb{R}^n$  we get the parallelogram law  $||U + V||^2 + ||U - V||^2 \equiv 2||U||^2 + 2||V||^2$ . Applying this repeatedly we get for any W, Y, and  $Z \in \mathbb{R}^n$  that

$$||W+Y+Z||^2 - ||W-Y-Z||^2 = ||W+Y||^2 - ||W-Y||^2 + ||W+Z||^2 - ||W-Z||^2,$$

letting first U=W+Y, V=Z, then U=W-Z, V=Y, then U=W, V=Z, and lastly U=W, V=Y. Applying (3) and dividing by 4 gives  $(W,Y+Z)\equiv (W,Y)+(W,Z)$ , the desired biadditivity. So  $(\cdot,\cdot)$  is indeed a semi-inner product, in other words there is a  $C(n)\in\mathcal{N}_n$  such that  $(U,V)\equiv U'C(n)V$ . By the permutation invariance, there are numbers  $a_n\geq 0$  and  $b_n$  such that  $C(n)_{ii}=a_n$  for all  $i=1,\ldots,n$  and  $C(n)_{ij}=b_n$  for all  $i\neq j$ . Let  $c_n:=a_n-b_n$ .

Let  $e_i \in \mathbb{R}^n$  be the *i*th standard unit vector. For each  $y \in \mathbb{R}^n$  let  $y = \sum_{i=1}^n y_i e_i$ . Let  $\overline{y} := \frac{1}{n} \sum_{i=1}^n y_i$ , so that  $y - \overline{y} 1_n = \sum_{i=1}^n (y_i - \overline{y}) e_i$ . Then for any  $z \in \mathbb{R}^n$ ,

$$(y-\overline{y}1_n,z-\overline{z}1_n) = \sum_{i,j=1}^n C(n)_{ij}(y_i-\overline{y})(z_j-\overline{z}) = c_n(y-\overline{y}1_n)'(z-\overline{z}1_n).$$

For  $1 \leq j \leq k \leq d$ , let  $B_{ir} := \delta_{r\pi(i)}$  for a function  $\pi$  from  $\{1, 2, \ldots, d\}$  into itself with  $\pi(1) = j$  and  $\pi(2) = k$ . Then  $(BX)^1 = X^j$  and  $(BX)^2 = X^k$ . Thus  $(X^j, X^k) = \Sigma_{12}(BX) = \Sigma_{jk}(X)$ , recalling (2) for j = k.

Let  $\overline{X} \in \mathbb{R}^d$  have ith component  $\overline{X}^i$  and  $Y^j := (X^j)'$ . Then

$$\Sigma_{jk}(X - \overline{X}1'_n) = (Y^j - \overline{X}^j 1_n, Y^k - \overline{X}^k 1_n) = c_n (Y^j - \overline{X}^j 1_n)' (Y^k - \overline{X}^k 1_n),$$

where  $c_n \ge 0$  is seen when j = k and the coefficient of  $c_n$  is strictly positive, as it can be since  $n \ge 2$ . Thus part (a) is proved.

For part (b), consider empirical measures  $P_n = P_{mn}$ , so that each  $X_j$  in  $P_n$  is repeated m times in  $P_{mn}$ . Since the  $\overline{X}$ 's and  $\Sigma$ s for  $P_n$  and  $P_{mn}$  must be the same, we get that  $c_{mn} = c_n/m$  which likewise equals  $c_m/n$ . Thus there is a constant  $c_1$  such that  $c_n = c_1/n$  for all n.

Let  $X_{11} := -X_{12} := \sqrt{n}$ , let  $X_{ij} = 0$  for all other i, j and let  $n \to \infty$ . Then  $\overline{X} \equiv 0$ ,  $P_n \to \delta_0$  weakly, and  $\Sigma(\delta_0)$  is the 0 matrix by singular affine equivariance with B = 0, but  $\Sigma(P_n)$  don't converge to 0 unless  $c_1 = 0$  and so  $c_n = 0$  for all n, proving (b).  $\square$ 

So, the three properties of T: (a) affine equivariance, (b) weak continuity on its domain  $\mathcal{D}$ , and (c) being everywhere defined, cannot all hold for location or scatter functionals on  $\mathbb{R}^d$  for  $d \geq 2$  although they can for d = 1. Which one(s) should be given up? Some functionals, such as the median and MAD, fail (b), but for d > 1, it seems that known functionals tend to fail (c). Specifically, if  $\Sigma$  is required to be strictly positive definite, then at a law concentrated in a proper hyperplane,  $\Sigma$  cannot be defined and affinely equivariant.

One can then ask: on how large a domain  $\mathcal{D}$  of laws can (a) and (b) hold? Consider replacing (c) by:

(c')  $\mathcal{D}$  is open and dense for the weak topology in the set of all laws on  $\mathbb{R}^d$ .

If (c') holds then the functional is undefined only on some nowhere dense and thus topologically small set. Let d metrize weak convergence. Then both  $\mathcal{D}$  is open and (b) holds if and only if for each  $P \in \mathcal{D}$ ,  $r_d^*(T, P) > 0$ . Then, almost surely the empirical measures  $P_n$  will also be in  $\mathcal{D}$  for n large enough and  $T(P_n) \to T(P)$ .

An open domain  $\mathcal{D}$  offers the possibility that continuity can be improved to Fréchet differentiability of some order or all orders with respect to some norm metrizing weak convergence.

For some location and scatter functionals or estimators T on  $\mathbb{R}^d$  for  $d \geq 2$ , there are  $\eta_k$  with  $0 \leq \eta_0 \leq \eta_1 \leq \cdots \leq \eta_{d-1} < 1$  and  $\eta_{d-1} > 0$  such that T(P) is undefined only for some P such that there is a hyperplane H of dimension  $k = 0, 1, \ldots$ , or d - 1, with  $P(H) \geq \eta_k$ . Such P form a closed, nowhere dense set F for any  $\eta_k$  as described, so T restricted to the complement of F satisfies (c'). For example, this holds for the Stahel-Donoho functional based on the median and MAD, cf. e.g. [27], with  $\eta_{d-1} = 1/2 > \eta_{d-2} = 0$ , and for the M-functionals based on  $t_{\nu}$  distributions for  $d \geq 2$  and  $\nu > 1$  (Kent and

Tyler [21], for finite samples), with  $\eta_k = (\nu + k)/(\nu + d)$ .

On the other hand the median and MAD (for d=1) are discontinuous on weakly dense sets and so do not satisfy (b) on any open (still less dense open) domain. This makes it hard, perhaps impossible, to verify (b) on open domains for other functionals based on the MAD or other scale functionals with the same discontinuity property, for example in scale-adjusted M-estimates of location for d=1 (Huber [20, §§6.5,6.6], Rousseeuw and Croux [32]) or for d>1 in the Stahel-Donoho functional, where univariate functionals  $\mu$ ,  $\sigma$  with more continuity can be used, specifically,  $t_{\nu}$ -functionals (Tyler [38], Maronna and Yohai [27]).

Rousseeuw's minimum-volume-ellipsoid (MVE) functional can be defined for laws with P(H) close to or even equal to 1 for a hyperplane H of dimension k < d, by restricting to H and using k-dimensional volume, as Lopuhaä and Rousseeuw [25, p. 235] suggested. But, for any  $d \ge 1$ ,  $\delta_C^*(\text{MVE}, P) = 0$  at laws P with densities, by Proposition 8.

## 2 Collapse points

The following notion of "collapse point" is specific to scatter functionals. It and the "implosion breakdown point" defined e.g. by Rousseeuw and Croux [32], both involve mass converging toward lower-dimensional hyperplanes. But the collapse point is not defined in terms of neighborhoods  $N_{\varepsilon}$  (contamination or other).

**Definition.** If a functional  $\Sigma(\cdot)$  defined on a non-empty set  $\mathcal{D}$  of laws on  $\mathbb{R}^d$  has values in  $\mathcal{N}_d$ , the collapse point  $\kappa(\Sigma)$  is the infimum of all  $y \in [0,1]$  such that there is a law Q on  $\mathbb{R}^d$  with  $Q(H) \leq y$  for every (d-1)-dimensional hyperplane H, and there exist laws  $Q_k \in \mathcal{D}$  converging to Q weakly with  $\det \Sigma(Q_k) \to 0$ . If there is no such y set  $\kappa(\Sigma) := 1$ . For d = 1, the collapse and breakdown points of a scale functional  $\sigma(\cdot)$  are defined as those of the scatter functional  $\sigma^2(\cdot)$ .

**Remarks**. For an affinely equivariant scatter functional on a non-empty domain  $\mathcal{D}$ , the "no such y" case cannot occur. Hampel, Ronchetti, Rousseeuw, and Stahel [17, §5.5 (a) p. 298] gave a proof that suggested those of the present section. For a comparison of statements, see the paragraph before Theorem 7.

For d=1 and the classical standard deviation functional  $\sigma(Q):=(\int x^2dQ-(\int xdQ)^2)^{1/2}$ , defined on the set  $\mathcal{D}$  of laws Q with  $\int x^2dQ<\infty$ , it's well known and easy to check that  $\varepsilon_C^*\equiv 0$ . It's also easy to see that the collapse point of  $\sigma$  is 1. For the MAD, with parameter space  $[0,\infty)$ , recall that  $\delta_C^*=\varepsilon_C^*=1/2$  at any law; the collapse point is also 1/2.

It is well known that if a law Q puts high probability p in a hyperplane of dimension < d, and a scatter functional  $\Sigma$  is required to take values in  $\mathcal{P}_d$ , so that  $\det \Sigma > 0$ , then  $\Sigma$  can be undefined at such Q, e.g. Kent and Tyler [21], and thus have low breakdown point at laws with somewhat smaller values of p. The following shows that even allowing  $\det \Sigma = 0$ , there is still a tradeoff between (definition-explosion) breakdown and collapse points.

**Theorem 5.** Let  $\Sigma$  be any affinely equivariant scatter functional with values in  $\Theta = \mathcal{N}_d$  defined on a non-empty family  $\mathcal{D}$  of laws on  $\mathbb{R}^d$ . Define its (maximum explosion-definition) breakdown point as  $\delta_C^*(\Sigma) := \sup\{\delta_C^*(\Sigma, P) : P \in \mathcal{D}\}$ . Then  $\delta_C^*(\Sigma) + \kappa(\Sigma) \leq 1$ . Moreover, for any  $\lambda$  with  $0 < \lambda < \delta_C^*(\Sigma)$ , there is a law  $\zeta$  with  $\zeta(H) = 1 - \lambda$  where H is a (d-1)-dimensional vector subspace and a sequence of laws  $\zeta_k \to \zeta$  weakly with  $\Sigma(\zeta_k)$  converging to a matrix with range included in H and  $\det \Sigma(\zeta_k) \to 0$ .

**Proof.** If  $\delta_C^*(\Sigma) = 0$  the conclusion holds since  $\kappa(\Sigma) \leq 1$  by definition. So we can assume that for some law P and  $0 < \varepsilon < \delta_C^*(\Sigma, P) \leq 1$ , for  $0 < \lambda < \varepsilon$  and any law Q, we have  $\rho := (1-\lambda)P + \lambda Q \in \mathcal{D}$  and  $\Sigma(\rho)$  remains bounded as Q varies. For any a > 0 let  $M_a(x) := (ax_1, x_2, \ldots, x_d)'$ . For any law G on  $\mathbb{R}^d$  and  $k = 1, 2, \ldots$ , let  $\rho_k := (1 - \lambda)P + \lambda(G \circ M_k^{-1})$ , so  $\rho_k \in \mathcal{D}$ , and

$$\zeta_k := \rho_k \circ M_{1/k}^{-1} = (1 - \lambda)(P \circ M_{1/k}^{-1}) + \lambda G.$$

Then by affine equivariance,  $\zeta_k \in \mathcal{D}$  and  $\det \Sigma(\zeta_k) = \det \Sigma(\rho_k)/k^2 \to 0$ . Also,  $\zeta_k$  converge weakly to  $\zeta := (1-\lambda)\tau + \lambda G$  where  $\tau$  is a law concentrated in the hyperplane  $H := \{x_1 = 0\}$ . Since G is arbitrary, now let it have a density. Then clearly  $\zeta(J) \leq 1 - \lambda$  for every (d-1)-dimensional hyperplane J. It follows that  $\kappa(\Sigma) \leq 1 - \lambda$ . Letting  $\lambda \uparrow \varepsilon \uparrow \delta_C^*(\Sigma)$ , we get  $(\kappa + \delta_C^*)(\Sigma) \leq 1$ . In  $\Sigma(\zeta_k)$ , the entries in the first row and first column go to 0 and the rest remain bounded. Thus, taking a subsequence, we can get convergence of  $\Sigma(\zeta_k)$  to a limit as claimed.  $\square$ 

By a similar proof we get a conclusion about location functionals:

**Proposition 6.** Let  $\mu(\cdot)$  be an affinely equivariant location functional defined on a non-empty family of laws on  $\mathbb{R}$  and suppose that  $\delta_C^*(\mu(\cdot)) = 1/2$ . Then the domain of  $\mu(\cdot)$  cannot be extended to contain any law  $\frac{1}{2}(\delta_a + \delta_b)$  with  $a \neq b$  and be weakly continuous at such a law.

**Proof.** We can take a=0 and b=1. By part of the proof of Theorem 5 with  $G:=\delta_1$ , for any  $m=1,2,\ldots$  and  $\lambda_m:=\frac{1}{2}-\frac{1}{m}$ , there is a sequence  $\zeta_{m,k}$  of laws converging weakly as  $k\to\infty$  to  $(1-\lambda_m)\delta_0+\lambda_m\delta_1$  with  $\mu(\zeta_{m,k})\to 0$ . Since weak convergence is metrizable, e.g. [11, Theorem 11.3.3], there exist  $k(m)\to\infty$  as  $m\to\infty$  such that as  $m\to\infty$ ,  $\zeta_{m,k(m)}\to\frac{1}{2}(\delta_0+\delta_1)$  weakly and  $\mu(\zeta_{m,k(m)})\to 0$ . But symmetrically and by affine equivariance, there also exist laws  $\eta_m\to\frac{1}{2}(\delta_0+\delta_1)$  weakly with  $\mu(\eta_m)\to 1$ . The conclusion follows.  $\square$ 

A law on  $\mathbb{R}^d$  will be called  $\alpha$ -degenerate for  $\alpha > 0$  if it puts mass at least  $\alpha$  on some (d-1)-dimensional hyperplane. The first conclusion of the next theorem bounds the less-studied replacement (total variation) breakdown point at a  $(1-\gamma)$ -degenerate law where  $0 < \gamma < 1$ . The second conclusion bounds the usual contamination breakdown point at a general law  $F_0$ , e.g. a normal law, assuming the functional T is defined and continuous at a related  $(1-\gamma)$ -degenerate law. Such an assumption seems not to hold for many location and scatter functionals given in the literature for  $\gamma \leq 1/2$ , although only then is the conclusion  $\varepsilon^* < \gamma$  of any interest. The assumption holds for M-functionals defined by t distributions with  $\nu$  degrees of freedom where  $\nu$  is large if  $\gamma$  is small, see Kent and Tyler [21], Dümbgen and Tyler [14]. Hampel et al. [17, §5.5] made such an assumption about a ((d-1)/d)-degenerate law in proving an upper bound 1/d for the breakdown point of M-functionals of location and scatter. For M-functionals of scatter Maronna [26] stated an upper bound 1/(d+1); Tyler [36], using results in Tyler [37], gave a proof, without any assumption about  $\alpha$ -degenerate laws. The following statement extends that of Hampel et al. (but not those of Maronna and Tyler) in that it holds for any  $\gamma$ ,  $0 < \gamma < 1$ , does not use any M-functional property, and has a form applying to functionals of location alone.

**Theorem 7.** Let T be an affinely equivariant location functional  $\mu$  or scatter functional  $\Sigma$  defined on a domain  $\mathcal{D}$  of laws on  $\mathbb{R}^d$ . For  $0 \leq a < \infty$  let  $M_a$  map  $\mathbb{R}^d$  into itself via  $x \mapsto (ax_1, x_2, \dots, x_d)'$ . Let  $F_0$  be any law on  $\mathbb{R}^d$  and  $\tilde{F}_0$  its projection into the linear subspace  $H := \{x : x_1 = 0\}$  via  $M_0$ . Suppose

that for some  $\gamma \in (0,1)$  and law  $\rho$  on  $\mathbb{R}^d$ , the law  $P := (1-\gamma)\tilde{F}_0 + \gamma \rho \in \mathcal{D}$  and if  $T = \Sigma$ ,  $\Sigma(P)$  is non-singular, or if  $T = \mu$ ,  $\mu(P) \notin H$ . Then  $\varepsilon_R^*(T,P) \leq \gamma$ . If in addition,  $T(\cdot)$  is weakly continuous at P on  $\mathcal{D}$ , and if for all a > 0,  $(1-\gamma)F_0 + \gamma \rho \circ M_a^{-1} \in \mathcal{D}$ , then  $\varepsilon_C^*(T,F_0) \leq \gamma$ .

**Proof.** By affine equivariance,  $P_a := P \circ M_a^{-1} = (1 - \gamma)\tilde{F}_0 + \gamma \rho \circ M_a^{-1} \in \mathcal{D}$  for each a > 0, and if  $T = \Sigma$ ,  $\det \Sigma(P_a) = a^2 \det \Sigma(P) \to +\infty$  or if  $T = \mu$ ,  $|\mu(P_a)| \to +\infty$  as  $a \to +\infty$ . Thus, we get breakdown of T at P by replacing  $\gamma \rho$  by  $\gamma \rho \circ M_a^{-1}$ , remaining in  $\mathcal{D}$ , so the first conclusion follows.

Under the further hypotheses, we have  $Q_a := (1-\gamma)F_0 \circ M_{1/a}^{-1} + \gamma \rho \to P$  weakly as  $a \to +\infty$ , so  $T(Q_a) \to T(P)$ . Thus, for  $T = \Sigma$ ,

$$\det\left(\Sigma\left((1-\gamma)F_0+\gamma\rho\circ M_a^{-1}\right)\right)=\det\Sigma(Q_a\circ M_a^{-1})\to+\infty.$$

For  $T = \mu$ ,  $|\mu(Q_a \circ M_a^{-1})| \to +\infty$ , and the second conclusion follows.  $\square$ 

For  $\gamma = 1/(d+1)$ , the hypothesis  $\mu(P) \notin H$  of Theorem 7 holds by Theorem 1(d) with n = d+1 and  $P = P_{d+1}$  an empirical measure if  $P \in \mathcal{D}$ .

## 3 Univariate trimming and the shorth

Let J be a probability density function on [0,1] such that  $J(y) \equiv J(1-y)$  for  $0 \le y \le 1$  and for some  $\alpha > 0$ , J(y) > 0 if and only if  $\alpha < y < 1 - \alpha$ . Let  $\mathcal{J}$  be the law on  $[\alpha, 1-\alpha]$  with density J. Most often  $\mathcal{J}$  has been taken as the uniform distribution  $U[\alpha, 1-\alpha]$ , but J can be taken to be continuous (and so continuous a.e. for each law, e.g. Stigler [34]) or as smooth as desired (e.g. Helmers [18]).

Let Q be any law on  $\mathbb{R}$  and F its distribution function. For 0 < y < 1 let  $F^{\leftarrow}(y) := \inf\{x : F(x) \geq y\}$ . Let  $Q_J$  be the image measure  $\mathcal{J} \circ (F^{\leftarrow})^{-1}$ . Then  $Q_J$  has support in the bounded interval  $[F^{\leftarrow}(\alpha), F^{\leftarrow}(1-\alpha)]$ , so the J-trimmed mean of Q, i.e. the mean of  $Q_J$ ,

$$\mu_J(Q) := \int_{-\infty}^{\infty} x dQ_J(x) = \int_0^1 F^{\leftarrow}(y) J(y) dy$$

and the *J-trimmed variance* of Q, i.e. the variance of  $Q_J$ ,

$$\sigma_J^2(Q) := \int_{-\infty}^{\infty} x^2 dQ_J(x) - \mu_J(Q)^2$$

exist and are finite. One may multiply  $\sigma_J^2(Q)$  if desired by a constant c > 1 so that if Q is the standard normal distribution then  $c\sigma_J^2(Q) = 1$ . It is straightforward to verify that with or without such a multiplication, the two functionals are defined for an arbitrary law Q on  $\mathbb{R}$  and are affinely equivariant location and scatter functionals respectively, weakly continuous at all laws. The median of  $Q_J$  is always the same as the median of Q.

For the t-functionals to be considered beginning in the next section, weak continuity at all laws also holds (after an extension to allow  $\sigma = 0$ ) but seems considerably harder to prove. So let's consider some other properties.

The functionals  $\mu_J$  and  $\sigma_J^2$  both have  $\delta_C^* = \alpha$ . The collapse point of  $\sigma_J^2$  is easily seen to be  $1 - 2\alpha$ . For  $\alpha$  close to 1/2,  $Q_J$  is determined by Q in a small interval around its median (if the median is unique), which seems undesirable, as evidenced by the collapse point being close to 0. If  $\alpha > 1/4$ , the collapse point is less than 1/2, which still seems unfortunate.

In some related methods of trimming,  $U[\alpha, 1-\alpha]$  is replaced by  $U[\beta, 1-\gamma]$  where  $\beta, \gamma \geq 0$  and  $\beta + \gamma = 2\alpha$ . Here  $\beta$  and  $\gamma$  can be chosen to minimize the variance of the resulting distribution [3], the distance of points in its support from the median [23], or otherwise. Location and scale functionals based on such trimming will still give collapse point  $1-2\alpha$  and can increase  $\delta_C^*$  to  $2\alpha$ , for  $\alpha < 1/4$ . Asymmetric trimming works well to prune asymmetric outlier contamination from a symmetric true distribution [23], but apparently not so well for an asymmetric true distribution.

There are various multivariate extensions of trimming, e.g. Donoho and Gasko [10] and Liu, Parelius and Singh [24]. But, by Theorem 1(d) and Theorem 3(b), no method can have the same complete success in defining a location functional as in one dimension.

The shorth and LMS functionals. Let  $0 < \alpha < 1$ . Let P be a law on  $\mathbb{R}$  and  $\sigma_{\mathrm{Sh},\alpha}(P) := \inf\{b-a: P([a,b]) \geq \alpha\}$ . Then there are always some a,b with  $P([a,b]) \geq \alpha$  and  $b-a=h:=\sigma_{\mathrm{Sh},\alpha}(P)$ . Let  $I_{\alpha}(P)$  be the set of such intervals [a,b]. Note that for each such [a,b] and  $\varepsilon > 0$ ,  $P([a,a+\varepsilon]) > 0$  and  $P([b-\varepsilon,b]) > 0$ . Let  $K_{\alpha}(P)$  denote the set of all conditional means  $\int_a^b x dP/P([a,b])$  for  $[a,b] \in I_{\alpha}(P)$  and  $M_{\alpha}(P)$  the set of midpoints (a+b)/2. Then  $K_{\alpha}(P)$  and  $M_{\alpha}(P)$  are compact, nonempty sets. If  $I_{\alpha}(P)$  consists of just one interval [a,b], let  $\mu_{\mathrm{Sh},\alpha}(P) := \mu$  and  $m_{\mathrm{Sh},\alpha}(P) := (a+b)/2$ , which for  $\alpha = 1/2$  Davies [7, p. 1856] calls the "middle of the shortest half" functional; Rousseeuw and Leroy [33, p. 169] call it the "least median of

squares" (LMS) functional, specializing a form of regression. Also,  $\mu_{\mathrm{Sh},\alpha}(P)$  is called the  $\alpha$ -shorth of P and  $\mu_{\mathrm{Sh}}(P) := \mu_{\mathrm{Sh},1/2}(P)$  is the shorth of P.

The LMS location functional  $m_{\mathrm{Sh},1/2}$  is the location part of the functional limit of the univariate case of Rousseeuw's [30] minimum-volume ellipsoid (MVE) location-scatter estimator  $(\mu, \Sigma)$ , which for a finite sample of size n in  $\mathbb{R}^d$ , finds an ellipsoid  $\{x: (x-\mu)'\Sigma^{-1}(x-\mu) \leq c\}$  of smallest volume containing [n/2]+1 of the observations (or, [(n+d+1)/2] observations, to maximize the finite-sample breakdown point, e.g. Rousseeuw and Leroy [33, p. 264]). Davies [5] briefly notes that although an MVE can be selected uniquely from its set of possible values, there is a dense set of laws for which the MVE is not unique and "no affine equivariant choice can be made." The following fact, then, is to some degree known, but it gives strong forms of denseness. Parts (a) and (c) of the following give contamination neighborhoods  $N_{\varepsilon}^{C}(P)$ , which are included in total variation neighborhoods and in turn in neighborhoods for weak convergence.

**Proposition 8.** (a) For any law P on  $\mathbb{R}$  having a continuous density f and any  $\varepsilon > 0$ , there is a law  $\zeta \in N_{\varepsilon}^{C}(P)$ , also with a continuous density, for which  $I_{1/2}(\zeta)$  contains more than one interval and so  $\mu_{Sh}(\zeta)$  and  $m_{Sh,1/2}(\zeta)$  are not defined. Thus  $\delta_{C}^{*}(m_{Sh,1/2},P) = 0$ , also if contamination neighborhoods are replaced by any larger neighborhoods.

- (b) For any  $\alpha$  with  $0 < \alpha < 1$  there exist laws P symmetric about a point  $m \notin K_{\alpha}(P)$ . For such P there is no way to select  $\mu^{(\alpha)} \in K_{\alpha}(P)$ , nor as a midpoint of any  $[a,b] \in I_{\alpha}(P)$ , to get an affine equivariant location functional  $\mu^{(\alpha)}(\cdot)$ .
- (c) Let  $F_0$  be any distribution on  $\mathbb{R}$  having a strictly unimodal density  $f_0$  with  $f_0(-x) \equiv f_0(x)$ . Then for any  $\lambda > 0$  there is a  $P \in N_{\lambda}^C(F_0)$  satisfying (b) for  $\alpha = 1/2$ .

**Proof.** (a) Let P have a continuous density f. If  $I_{1/2}(P)$  contains more than one interval we are done, so suppose  $I_{1/2}(P)$  contains just one interval [a,b], which we can assume is [0,1]. Thus  $\int_x^{x+1} f(u) du < 1/2$  for  $x \neq 0$ . Take any  $\delta$  with  $0 < \delta < 1$ . Another continuous density g will be defined as follows. Let g(x) = 1/2 for  $0 \leq x \leq 1$  and  $h_{\delta} := (1 - \delta)f + \delta g$ . Then  $\int_0^1 h_{\delta}(x) dx = 1/2$ . For x > 0 let

$$g_{\delta}(x) := \frac{1-\delta}{\delta}[f(x) - f(x+1)] + \frac{1}{2}.$$

We have  $(d/dx) \int_x^{x+1} f(u) du = f(x+1) - f(x) = 0$  when x = 0, so f(0) = f(1). There is a  $\gamma > 0$  such that  $\gamma < 1/2$  and  $(1-\delta)[f(u+1) - f(u)] \le \delta/2$  for  $0 \le u \le \gamma$ . Choose a  $\beta > 0$  small enough so that  $g_{\delta}(u) > 0$  for  $0 \le u \le \beta$  and  $\int_1^{1+\beta} g_{\delta}(u-1) du < \gamma/2$ . Define  $g(1+x) := g_{\delta}(x)$  for  $0 < x \le \beta/2$ ,  $g(1+x) := 2(\beta-x)\beta^{-1}g_{\delta}(x) < g_{\delta}(x)$  for  $\beta/2 < x \le \beta$ , and g(1+x) := 0 for  $x > \beta$ . For  $0 < x < \beta/2$  we have

$$\frac{d}{dx} \int_{x}^{1+x} h_{\delta}(u) du = (1-\delta)[f(x+1) - f(x)] + \delta \left[g_{\delta}(x) - \frac{1}{2}\right] = 0,$$

so  $\int_x^{1+x} h_{\delta}(u) du = 1/2$  for  $0 \le x \le \beta/2$ . For  $\beta/2 < x \le \beta$  we then have by definition of g(1+x)

$$\int_{x}^{1+x} h_{\delta}(u)du < 1/2. \tag{4}$$

For  $x > \gamma$ ,  $\int_x^{1+x} g(u) du < 1/2$  (for  $x \le 1$  or x > 1), so (4) holds. To prove (4) for  $\beta < x \le \gamma$  it suffices to show  $\int_x^{1+x} h_\delta(u) du \le \int_\beta^{1+\beta} h_\delta(u) du$ , or  $[\int_\beta^x - \int_{1+\beta}^{1+x} ]h_\delta(u) \ge 0$ , or  $\int_\beta^x (1-\delta)[f(u)-f(1+u)] + \frac{\delta}{2} du \ge 0$ , which holds by choice of  $\gamma$ .

Since  $\int_0^\infty g(u)du = \int_0^{1+\beta} g(u)du < 3/4$  by choice of  $\beta$  and  $\gamma$ , we can and do define g(u) for u < 0 to be nonnegative and continuous at 0 with g(u) < 1/2 for all u < 0 such that  $\int_{-\infty}^\infty g(u)du = 1$ . Then g and  $h_\delta$  are both probability densities. For any x < 0,  $\int_x^{1+x} h_\delta(u)du < \frac{1}{2}(1-\delta+\delta)$ . So (4) holds for all  $x \notin [0, \beta/2]$  while  $\int_x^{1+x} h_\delta(u)du = 1/2$  for  $0 \le x \le \beta/2$ . Thus for  $\zeta$  with density  $h_\delta$ , we have  $\sigma_{\text{Sh},1/2}(\zeta) = 1$  and  $I_{1/2}(\zeta) = \{[x, x+1] : 0 \le x \le \beta/2\}$ . Now  $\int_x^{1+x} uh_\delta(u)du / \int_x^{1+x} h_\delta(u)du = 2 \int_x^{1+x} uh_\delta(u)du$  is a strictly increasing function of x for  $0 \le x \le \beta/2$ , so (a) is proved.

For (b), if P exists, the conclusions follow from Theorem 1(c). To show P exists, for  $0 < \alpha \le 1/2$ , let  $P = \frac{1}{2}(U[0,1] + U[3,4])$ . For  $1/2 < \alpha < 1$ , let  $P = (2\alpha - 1)\delta_0 + (1 - \alpha)(\delta_{-1} + \delta_1)$ . Then m = 0,  $\sigma_{\text{Sh},\alpha}(P) = 1$ , and  $0 \notin K_{\alpha}(P) = \{\pm (1 - \alpha)\}$ , proving (b).

For (c),  $I_{1/2}(F_0)$  contains just one interval, namely  $[-\xi,\xi]$ , where  $\xi$  is the upper quartile of  $F_0$ . For any  $\delta>0$  let  $Q_\delta$  be the law with density  $f_\delta$  where  $f_\delta(-x)\equiv f_\delta(x),\ f_\delta(\xi+t)=t/\delta^2$  for  $0\leq t\leq \delta$  and  $f_\delta(x)=0$  for all other x>0. For fixed  $\lambda\in(0,1)$  and  $P_\delta:=(1-\lambda)F_0+\lambda Q_\delta$ , the unique interval  $[-\eta,\eta]$  with  $P_\delta([-\eta,\eta])=1/2$  has length  $2\xi+\sqrt{2}\delta+o(\delta)$  as  $\delta\downarrow 0$ . But  $P_\delta([-\xi,\xi+\delta])>1/2$  for a shorter interval, proving (c) and the proposition.  $\square$ 

#### References

- [1] Bassett, G. W. (1991). Equivariant, monotonic, 50% breakdown estimators. *American Statistician* **45**, 135-137.
- [2] Bickel, P. J., and Lehmann, E. L. (1975). Descriptive statistics for nonparametric models. I, Introduction; II, location. Ann. Statist. 3, 1038-1044, 1045-1069.
- [3] Butler, R. W. (1982). Nonparametric interval and point prediction using data trimmed by a Grubbs-type outlier rule. *Ann. Statist.* **10**, 197-204.
- [4] Clarke, B. R. (1983). Uniqueness and Fréchet differentiability of functional solutions to maximum likelihood type equations. *Ann. Statist.* 11, 1196-1205.
- [5] Davies, [P.] L. (1992a). The asymptotics of Rousseeuw's minimum volume ellipsoid estimator. *Ann. Statist.* **20**, 1828-1843.
- [6] Davies, [P.] L. (1992b). An efficient Fréchet differentiable high breakdown location and dispersion estimator. J. Multivariate Analysis 40, 311-327.
- [7] Davies, P. L. (1993). Aspects of robust linear regression. *Ann. Statist.* 21, 1843-1899.
- [8] Davies, [P.] L. (1994). Desirable properties, breakdown and efficiency in the linear regression model. *Statistics and Probability Letters* **19**, 361-370.
- [9] Davies, P. L. (1998). On locally uniformly linearizable high breakdown location and scale functionals. *Ann. Statist.* **26**, 1103-1125.
- [10] Donoho, D. L., and Gasko, M. (1992). Breakdown properties of location estimates based on halfspace depth and projected outlyingness. Ann. Statist. 20, 1803-1827.
- [11] Dudley, R. M. (2002). *Real Analysis and Probability*, 2d ed. Cambridge University Press.

- [12] Dümbgen, L. (1997). The asymptotic behavior of Tyler's M-estimator of scatter in high dimension. Preprint.
- [13] Dümbgen, L. (1998). On Tyler's M-functional of scatter in high dimension. *Ann. Inst. Statist. Math.* **50**, 471-491.
- [14] Dümbgen, L., and Tyler, D. (2004). On the breakdown properties of some multivariate M-functionals. Preprint.
- [15] Ferguson, T. S. (1978). Maximum likelihood estimates of the parameters of the Cauchy distribution for samples of size 3 and 4. *J. Amer. Statist. Assoc.* **73**, 211-213.
- [16] Hampel, F. R. (1971). A general qualitative definition of robustness. Ann. Math. Statist. 42, 1887-1896.
- [17] Hampel, F. R., Ronchetti, E. M., Rousseeuw, P. J., and Stahel, W. A. (1986). Robust Statistics: The Approach Based on Influence Functions. Wiley, New York.
- [18] Helmers, R. (1980). Edgeworth expansions for linear combinations of order statistics with smooth weight functions. *Ann. Statist.* **8**, 1361-1374.
- [19] Huber, P. J. (1967). The behavior of maximum likelihood estimates under nonstandard conditions. *Proc. Fifth Berkeley Symp. Math. Statist. Probability* 1, 221-233. University of California Press, Berkeley and Los Angeles.
- [20] Huber, P. J. (1981). *Robust Statistics*. Wiley, New York. Reprinted, 2004.
- [21] Kent, J. T., and Tyler, D. E. (1991). Redescending *M*-estimates of multivariate location and scatter. *Ann. Statist.* **19**, 2102-2119.
- [22] Kent, J. T., Tyler, D. E., and Vardi, Y. (1994). A curious likelihood identity for the multivariate t-distribution. Commun. Statist.—Simula. 23, 441-453.
- [23] Kim, Seong-Ju (1992). The metrically trimmed mean as a robust estimator of location. *Ann. Statist.* **20**, 1534-1547.

- [24] Liu, R. Y., Parelius, J. M., and Singh, K. (1999). Multivariate analysis by data depth: descriptive statistics, graphics and inference (with discussion). *Ann. Statist.* **27**, 783-858.
- [25] Lopuhaä, H. P., and Rousseeuw, P. J. (1991). Breakdown points of affine equivariant estimators of multivariate location and covariance matrices. *Ann. Statist.* **19**, 229-248.
- [26] Maronna, R. A. (1976). Robust *M*-estimators of multivariate location and scatter. *Ann. Statist.* 4, 51-67.
- [27] Maronna, R. A., and Yohai, V. J. (1995). The behavior of the Stahel-Donoho robust multivariate estimator. J. Amer. Statist. Assoc. 90, 330-341.
- [28] Milasevic, P. and Ducharme, G. R. (1987). Uniqueness of the spatial median. *Ann. Statist.* **15**, 1332-1333.
- [29] Obenchain, R. L. (1971). Multivariate procedures invariant under linear transformations. *Ann. Math. Statist.* **42**, 1569-1578.
- [30] Rousseeuw, P. J. (1986). Multivariate estimation with high breakdown point. In *Mathematical Statistics and Applications*, Vol. B (W. Grossmann, G. Pflug, I. Vincze, and W. Wertz, eds.). Dordrecht, Reidel.\*
- [31] Rousseeuw, P. J. (1994). Unconventional features of positive-break-down estimators. Statistics and Probability Letters 19, 417-431.
- [32] Rousseeuw, P. J., and Croux, C. (1993). Alternatives to the median absolute deviation. J. Amer. Statist. Assoc. 88, 1273-1283.
- [33] Rousseeuw, P. J., and Leroy, A. Robust Regression and Outlier Detection. Wiley, New York.
- [34] Stigler, S. M. (1974). Linear functions of order statistics with smooth weight functions. *Ann. Statist.* **2**, 676-693; corr. *ibid.* **7** (1979), 466.
- [35] Tatsuoka, K. S., and Tyler, D. E. (2000). On the uniqueness of Sfunctionals and M-functionals under nonelliptical distributions. Ann. Statist. 28, 1219-1243.

- [36] Tyler, D. E. (1986). Breakdown properties of the *M*-estimators of multivariate scatter. Technical Report, Rutgers University.
- [37] Tyler, D. E. (1988). Some results on the existence, uniqueness, and computation of the M-estimates of multivariate location and scatter. SIAM J. on Scientific and Statistical Computing 9, 354-362.
- [38] Tyler, D. E. (1994). Finite sample breakdown points of projection based multivariate location and scatter statistics. *Ann. Statist.* **22**, 1024-1044.

<sup>\*</sup> The author has seen the Rousseeuw (1986) item cited in secondary sources but not in the original.

---

## INTRODUCTION TO ROBUSTNESS: BREAKDOWN POINTS

Let  $X=(X_1,...,X_n)$  and  $Z=(Z_1,...,Z_n)$  be samples of real numbers. For j=1,...,n let  $X=_j Z$  mean that  $X_i=Z_i$  except for at most j values of i. More specifically, for  $y=(y_1,...,y_j)$  let  $X=_{j,y}Z$  mean that for some integers  $i_r$  with  $1 \le i_1 < i_2 < ... < i_j \le n$ ,  $Z_{i_r}=y_r$  for r=1,...,j and  $Z_i=X_i$  if  $i \ne i_r$  for r=1,...,j. The idea is that  $X_i$  are i.i.d. from a nice distribution like a normal and  $y_r$  are errors or "bad" data. So the sample Z contains n-j good data points and j errors. A robust statistical procedure will be one that doesn't behave too badly if j is not too large compared to n.

"Breakdown point" is one of the main ideas in robustness. Let  $T = T(Z_1, ..., Z_n)$  be a statistic taking values in a parameter space  $\Theta$ , a locally compact metric space. The main examples of parameter spaces to be considered here for real data are:

- (a) The location parameter space of all  $\mu$  such that  $-\infty < \mu < \infty$  (the real line). Examples of statistics taking values in this space are the sample mean  $\overline{Z}$  and the sample median.
- (b) The scale parameter space containing 0, of all  $\sigma$  such that  $0 \le \sigma < \infty$ . Examples of statistics with values in  $[0, \infty)$  are (i) the sample standard deviation and (ii) the median of all  $|X_i m|$  where m is the sample median. A variant of the scale parameter space is the open half-line  $0 < \sigma < \infty$ . Both examples (i) and (ii) can take the value 0 for some samples, so on such samples, these statistics are undefined if the scale parameter space is  $(0, \infty)$ .
- (c) Often parameter spaces are considered, when location and scale are estimated simultaneously, of pairs  $(\mu, \sigma)$  where  $-\infty < \mu < \infty$  and  $0 \le \sigma < \infty$  or alternately where  $0 < \sigma < \infty$ .

The closure of a set  $A \subset \Theta$  will be denoted  $\overline{A}$ . If  $\Theta$  is a Euclidean space or a closed subset of one, such as the closed half-line  $0 \leq \sigma < \infty$ , then a set  $A \subset \Theta$  has compact closure if and only if  $\sup\{|x|: x \in A\} < \infty$ . In the open half-line  $0 < \sigma < \infty$ , a subset A is compact if and only if it is bounded away from both 0 and  $+\infty$ , in other words for some  $\delta > 0$  and  $M < \infty$ ,  $\delta \leq \sigma \leq M$  for all  $\sigma \in A$ .

The breakdown point of T at X is defined as

$$\varepsilon^*(T,X) = \varepsilon^*(T;X_1,...,X_n) = \frac{1}{n} \max\{j : \overline{\{T(Z) : Z =_j X\}} \text{ is compact}\}.$$

In other words  $\varepsilon^*(T, X) = j/n$  for the largest j for which there is some compact set  $K \subset \Theta$  such that  $T(Z) \in K$  whenever  $Z =_j X$ . If  $\varepsilon^*(T, X)$  doesn't depend on X, which is often the case, then let  $\varepsilon^*(T) := \varepsilon^*(T, X)$  for all X.

Some authors define the breakdown point instead in terms of the smallest number of replaced observations that can cause T(Z) not to remain in any compact set. Such a definition adds 1/n to  $\varepsilon^*(T,X)$  and makes no difference asymptotically as  $n \to \infty$ .

If a fraction of the data less than or equal to the breakdown point is bad (subject to arbitrarily large errors), the statistic doesn't change too much (it remains in a compact set), otherwise it can escape from all compact sets (in a Euclidean space, or by definition in other locally compact spaces, it can go to infinity). There are a number of definitions

of breakdown point. The one just given is called the "finite sample" breakdown point (Hampel et al., 1986, p. 98, for a real-valued statistic).

Since j in the definition is an integer, the possible values of the breakdown point for samples of size n are 0, 1/n, 2/n, ..., 1. A statistic with a breakdown point of 0 is (by definition) not robust. Larger values of the breakdown point indicate more robustness, up to breakdown point = 1/2 which is the maximum attainable in some problems.

**Examples.** (i) For the sample mean  $T = \bar{Z} = (Z_1 + ... + Z_n)/n$ , the breakdown point is 0 for any  $Z_j$  since for j = 1, if we let  $y_1 \to \infty$  then  $\bar{Z} \to \infty$  (for n fixed).

(ii) Let  $T = Z_{(1)}$ , the smallest number in the sample. Then the breakdown point of T is again 0 for any  $Z_i$  since for j = 1, as  $y_1 \to -\infty$  we have  $Z_{(1)} \to -\infty$ . Likewise the maximum  $Z_{(n)}$  of the sample has breakdown point 0.

So the statistics  $\bar{Z}$ ,  $Z_{(1)}$ ,  $Z_{(n)}$  are not robust. Other order statistics have some robustness (for fixed finite n):

**Theorem 1.** For sample size n, and each j=1,...,n, the order statistic  $T=Z_{(j)}$  has breakdown point  $\varepsilon^*(T)=\frac{1}{n}\min(j-1,n-j)$ .

**Proof.** At any sample  $X=(X_1,...,X_n)$ , we have  $\inf\{T(Z): Z=_j X\}=-\infty$  (let  $y_1,...,y_j$  all go to  $-\infty$ ). Likewise  $\sup\{T(Z): Z=_{n-j+1} X\}=+\infty$  (let  $y_1,...,y_{n-j+1}\to +\infty$ ). It follows that  $\varepsilon^*(T,X)\leq \frac{1}{n}\min(j-1,n-j)$ .

If  $Z =_{j-1} X$  then the smallest possible value of  $Z_{(j)}$  occurs when  $y_i < X_k$  for all i and k and for at least one r such that  $X_r = X_{(1)}$ ,  $X_r$  is not replaced, so  $Z_{(j)} \ge X_{(1)}$ . Similarly, if  $Z =_{n-j} X$  the largest possible value of  $Z_{(j)}$  satisfies  $Z_{(j)} \le X_{(n)}$ . So if  $k = \min(j-1, n-j)$  and  $Z =_k X$ , then  $X_{(1)} \le Z_{(j)} \le X_{(n)}$  so  $Z_{(j)}$  is bounded and  $\varepsilon^*(T,X) = \frac{1}{n}\min(j-1,n-j)$  as claimed. Since this is true for an arbitrary X, the theorem is proved.

If j=1 or n, the breakdown point of  $X_{(j)}$  is 0 as noted in the Examples above. If n is odd, so n=2k+1 for an integer k, then the sample median  $X_{(k+1)}$  has breakdown point  $\frac{1}{2}-\frac{1}{2n}=\frac{k}{n}$ . If n=2k for an integer k, then the two endpoints of the interval of medians,  $Z_{(k)}$  and  $Z_{(k+1)}$ , each have breakdown point  $\frac{1}{2}-\frac{1}{n}$ . So any median has breakdown point at least  $\frac{1}{2}-\frac{1}{n}\to\frac{1}{2}$  as  $n\to\infty$ . From Theorem 1, no other order statistic has any larger breakdown point than the median, so  $\varepsilon^*(X_{(j)})<1/2$  for all j. This is typical behavior for interesting estimators. But, larger breakdown points are possible. If T has bounded values, then it trivially has breakdown point 1 by our definition. Or, let  $T=\min_j |Z_j|$ . Then one can check that T has breakdown point  $1-\frac{1}{n}$ .

For real-valued observations  $Z_1, \ldots, Z_n$ , a real-valued statistic  $T = T(Z_1, \ldots, Z_n)$  will be called *equivariant for location* if for all real  $\theta$ , and letting  $Z = (Z_1, \ldots, Z_n)$  and  $Z + \theta = (Z_1 + \theta, \ldots, Z_n + \theta)$ ,

$$T(Z + \theta) = T(Z) + \theta$$

for all *n*-vectors Z of real numbers and all real  $\theta$ .

For example, the order statistics  $Z_{(j)}$  and the sample mean  $\bar{Z}$  are clearly equivariant for location.

**Theorem 2.** For any real-valued statistic T equivariant for location, the breakdown point is < 1/2 at any  $X = (X_1, ..., X_n)$ .

**Proof.** Let the breakdown point of T at X be j/n. Then there is an  $M < \infty$  such that

(3) 
$$|T(Z)| \leq M$$
 whenever  $Z =_j X$ .

Let  $\theta = 3M$ . Now  $Z = Y + \theta$  for some Y with  $Y =_j X$  if and only if  $Z =_j X + \theta$ . Then  $T(Z) = T(Y) + \theta$ . So

(4) 
$$|T(Z) - \theta| \le M$$
 whenever  $Z =_j X + \theta$ , and then  $2M \le T(Z) \le 4M$ .

But if  $j \ge n/2$  there is a Z with  $Z =_j X$  and also  $Z =_j X + \theta$ . For such a Z, (3) and (4) give a contradiction, proving Theorem 2.

## REFERENCES

Frank R. Hampel, Peter J. Rousseeuw, Elvezio M. Ronchetti, and Werner A. Stahel (1986). *Robust Statistics: The Approach based on Influence Functions*. Wiley, New York. Peter J. Huber (1981) *Robust Statistics*. Wiley, New York.

---

## M-estimators and their consistency

This handout is adapted from Section 3.3 of 18.466 lecture notes on mathematical statistics, available on OCW.

A sequence of estimators  $T_n$ , one for each sample size n, possibly only defined for n large enough, is called *consistent* if for  $X_1, X_2, \ldots$ , i.i.d.  $(P_\theta)$ ,  $T_n = T_n(X_1, \ldots, X_n)$  converges in probability as  $n \to \infty$  to a function  $g(\theta)$  being estimated. We will consider consistency of estimators more general than maximum likelihood estimators in two ways, first that the function being maximized may not be a likelihood, and second that it only needs to be approximately maximized.

It will be assumed that the parameter space  $\Theta$  is a locally compact separable metric space with a metric d, such as an open or closed subset of a Euclidean space.  $(X, \mathcal{A}, P)$  will be any probability space, and  $h = h(\theta, x)$  is a measurable function on  $\Theta \times X$  with values in the extended real number system  $[-\infty, \infty]$ . One example will be the negative of a log likelihood function,  $h(\theta, x) \equiv -\log f(\theta, x)$ . This will be called the log likelihood case. Let  $X_1, X_2, \ldots$  be independent random variables with values in X and distribution P, specifically, coordinates on the countable product  $(X^\infty, \mathcal{A}^\infty, P^\infty)$  of copies of  $(X, \mathcal{A}, P)$  (RAP, Sec. 8.2). A statistic  $T_n = T_n(X_1, ..., X_n)$  with values in  $\Theta$  will be called an M-estimator if

$$\frac{1}{n} \sum_{i=1}^{n} h(T_n, X_i) = \inf_{\theta \in \Theta} \frac{1}{n} \sum_{i=1}^{n} h(\theta, X_i).$$

Thus, in the log likelihood case, an M-estimator is a maximum likelihood estimator. The outer probability  $P^*(C)$  of a not necessarily measurable set C is defined by

$$P^*(C) := \inf\{P(A) : A \supset C, A \text{ measurable}\}.$$

Let  $f_n$  be a sequence of not necessarily measurable functions from a probability space into a metric space S with metric d. Then  $f_n$  is said to converge to  $f_0$  almost uniformly if for every  $\varepsilon > 0$ ,  $P^*(\sup_{m \ge n} d(f_m, f_0) > \varepsilon) \to 0$  as  $n \to \infty$ . If  $d(f_m, f_0)$  is a measurable random variable, as it will be in nearly all actual applications, then almost uniform convergence is the same as almost sure convergence.

Statistics  $T_n = T_n(X_1, ..., X_n)$  with values in  $\Theta$  will be called a sequence of approximate M-estimators if as  $n \to \infty$ ,

(3.3.1) 
$$\frac{1}{n} \sum_{i=1}^{n} h(T_n, X_i) - \inf_{\theta \in \Theta} \frac{1}{n} \sum_{i=1}^{n} h(\theta, X_i) \to 0$$

almost uniformly.

It will be proved that  $T_n$  converges almost uniformly to some  $\theta_0$  under a list of assumptions as follows.

(A-1)  $h(\theta, x)$  is a separable stochastic process, meaning that there is a set  $A \subset X$  with P(A) = 0 and a countable subset  $S \subset \Theta$  such that for every open set  $U \subset \Theta$  and every closed set  $J \subset [-\infty, \infty]$ ,

$$\{x:\ h(\theta,x)\in J\ \text{ for all }\ \theta\in S\cap U\}\subset A\cup \{x:\ h(\theta,x)\in J\ \text{ for all }\ \theta\in U\}.$$

This will be true with A empty if each function  $h(\cdot, x)$  is continuous on  $\Theta$  and S is dense in  $\Theta$ , but the assumption is valid in more general situations. An alternate, equivalent formulation of separability is that for some countable S and almost all x, the graph of  $h(\cdot, x)$  restricted to S is dense in the whole graph. For example, if  $\Theta$  is an interval in  $\mathbb{R}$ , and for almost all x,  $h(\cdot, x)$  is either left-continuous or right-continuous at each  $\theta$ , then  $h(\cdot, \cdot)$  is a separable process.

It is known that by changing  $h(\theta, x)$  only for x in a set of probability 0 (depending on  $\theta$ ), one can assume that h is separable (by a theorem of Doob, proved in Appendix C, Theorem C.2 of the 18.466 notes). But in statistics, where the probability P is unknown, the separability is more clearly attainable in case h has at least a one-sided continuity property as just mentioned.

Instead of continuity, here is a weaker assumption:

(A-2) For each x in X, the function  $h(\cdot, x)$  is lower semicontinuous on  $\Theta$ , meaning that  $h(\theta, x) \leq \liminf_{\phi \to \theta} h(\phi, x)$  for all  $\theta$ .

Often, but not always, the functions  $h(\cdot, x)$  will be continuous on  $\Theta$ . Consider for example the uniform distributions  $U[\theta, \theta + 1]$  on  $\mathbb{R}$  for  $\theta \in \mathbb{R}$ . The density  $f(\theta, x) := 1_{[\theta, \theta + 1]}(x)$  is not continuous in  $\theta$ , but it is upper semicontinuous,

$$f(\theta, x) \ge \limsup_{\phi \to \theta} f(\phi, x).$$

It follows that the functions  $h(\theta, x) = -\log f(\theta, x)$  are lower semicontinuous (they have values  $+\infty$  for  $x \notin [\theta, \theta + 1]$ ). This is a reason for choosing the densities to be indicator functions of closed intervals; if we had taken  $f(\theta, x) = 1_{(\theta, \theta + 1)}(x)$ , then  $h(\theta, x)$  would no longer be lower semicontinuous.

For any real function f, as usual let  $f^+ := \max(f, 0)$  and  $f^- := -\min(f, 0)$ . A function  $h(\cdot, \cdot)$  of  $\theta$  and x will be called *adjusted* for P if

(3.3.2) 
$$Eh(\theta, x)^{-} < \infty \text{ for all } \theta \in \Theta, \text{ and }$$

(3.3.3) 
$$Eh(\theta, x)^{+} < \infty \text{ for some } \theta \in \Theta.$$

To say that h is adjusted is equivalent to saying that  $Eh(\theta, \cdot)$  is well-defined (possibly  $+\infty$ ) and not  $-\infty$  for all  $\theta$ , and for some  $\theta$ , also  $Eh(\theta, \cdot) < +\infty$ , so it is some finite real number.

If  $a(\cdot)$  is a measurable real-valued function on X such that  $h(\theta, x) - a(x)$  is adjusted for P, then  $h(\cdot, \cdot)$  will be called *adjustable* for P and  $a(\cdot)$  will be called an *adjustment function* for h and P. The next assumption is:

(A-3)  $h(\cdot,\cdot)$  is adjustable for P.

From here on, if  $h(\theta, x)$  is adjustable but not adjusted, let  $\gamma(\theta) := \gamma_a(\theta) := E[h(\theta, x) - a(x)]$  for a suitable adjustment function  $a(\cdot)$ . As an example, let  $h(\theta, x) := |x - \theta|$  for  $\theta, x \in \mathbb{R}$ . If P is a law on  $\mathbb{R}$ , such as the Cauchy distribution with density  $(\pi(1 + x^2))^{-1}$ , with  $\int |x| dP(x) = +\infty$ , then h itself is not adjusted and an adjustment function is needed. Let a(x) := |x| in this case. Then for each  $\theta, |x - \theta| - |x|$  is bounded in absolute value (by  $|\theta|$ ), so  $\gamma(\theta)$  is defined and finite for all  $\theta$ . Thus |x| is in fact an adjustment function for any P.

The example illustrates an idea of Huber (1967,1981) who seems to have invented the notion of adjustment. An estimator is defined by minimizing or approximately minimizing  $\frac{1}{n}\sum_{i=1}^{n}h(\theta,X_i)$ . If  $\int h(\theta,x)dP(x)$  is finite, it is the limit of the sample averages by the strong law of large numbers. But if it isn't finite, it may be made finite by subtracting an adjustment function a(x) from h. Since  $a(\cdot)$  doesn't depend on  $\theta$ , this change doesn't affect the minimization for each n. Thus, such estimators can be treated for more general probability measures P which on the real line, for example, can have long tails, allowing robust estimation. In fact, in the last example, P can be an arbitrary (and so arbitrarily heavy-tailed) distribution on  $\mathbb{R}$ .

**3.3.4 Proposition**. If  $a_1$  is an adjustment function for  $h(\cdot, \cdot)$  and P, then another measurable real-valued function  $a_2(\cdot)$  on X is also an adjustment function if and only if  $a_1 - a_2$  is integrable for P, and  $\{\theta : \gamma(\theta) \in \mathbb{R}\}$  does not depend on the choice of adjustment function  $a(\cdot)$ .

**Proof.** "If" is clear. To prove "only if," we have  $E((h(\theta,x)-a_i(x))^-)<\infty$  for all  $\theta$  and i=1,2, while  $E((h(\theta_i,x)-a_i(x))^+)<\infty$  for some  $\theta_i$  and i=1,2. We can write for  $\theta=\theta_1$  or  $\theta_2$ ,

$$(a_1 - a_2)(x) = h(\theta, x) - a_2(x) - [h(\theta, x) - a_1(x)]$$

for P-almost all x. To check this we need to take account that h can have values  $\pm \infty$ . For any  $\theta$ ,  $h(\theta, x) > -\infty$  for P-almost all x since h is adjustable. We have  $h(\theta_1, x) < +\infty$  and  $h(\theta_2, x) < +\infty$  for P-almost all x. Thus the given expression for  $(a_1 - a_2)(x)$  is well-defined for P-almost all x and  $\theta = \theta_1$  or  $\theta_2$ . We then have

$$E((a_1 - a_2)^+) \le E[(h(\theta_2, x) - a_2(x))^+] + E[(h(\theta_2, x) - a_1(x))^-] < \infty,$$

$$E((a_1 - a_2)^-) \le E[(h(\theta_1, x) - a_2(x))^-] + E[(h(\theta_1, x) - a_1(x))^+] < \infty,$$

so  $E|a_1 - a_2| < \infty$  as stated. Thus, the sets of  $\theta$  for which  $E((h(\theta, x) - a_i(x))^+) < \infty$ , or equivalently  $E|h(\theta, x) - a_i(x)| < \infty$ , don't depend on i, as stated. This finishes the proof of the proposition.

The next assumption is:

(A-4) There is a  $\theta_0 \in \Theta$  such that  $\gamma(\theta) > \gamma(\theta_0)$  for all  $\theta \neq \theta_0$ .

Here  $\theta_0$  is called the *M-functional* of P. In the log likelihood case it is sometimes called the *pseudo-true* value of  $\theta$ . Then  $h(\theta, x) = -\log f(\theta, x)$  where for fixed  $\theta$ , f is a density or probability mass function for a probability measure  $P_{\theta}$ . The distribution P of the observations may not be in the parametric family of laws  $P_{\theta}$ , and if not, no true value of  $\theta$  exists, but often a pseudo-true value exists.

By Proposition 3.3.4,  $\theta_0$  does not depend on the choice of adjustment function. After some more assumptions, it will be shown that  $T_n$  converges to  $\theta_0$ .

If  $\Theta$  is not compact, let  $\infty$  be the point adjoined in its one-point compactification (RAP, 2.8.1) and let  $\liminf_{\theta\to\infty}$  mean  $\sup_K\inf_{\theta\notin K}$  where the supremum is over all compact K. The next assumption is

(A-5) For some adjustment function  $a(\cdot)$ , there is a continuous function  $b(\cdot) > 0$  on  $\Theta$  such that

$$\inf\{(h(\theta, x) - a(x))/b(\theta) : \theta \in \Theta\} \ge -u(x)$$

for some integrable function  $u(\cdot) \geq 0$ , and if  $\Theta$  is not compact, then

(3.3.6) 
$$\liminf_{\theta \to \infty} b(\theta) > \gamma_a(\theta_0)$$
 and

$$(3.3.7) E\{\liminf_{\theta \to \infty} (h(\theta, x) - a(x))/b(\theta)\} \ge 1.$$

This completes the list of assumptions. Here (3.3.5) and (3.3.7) may depend on the choice of adjustment function. In the example where  $X = \Theta = \mathbb{R}$ ,  $h(\theta, x) = |x - \theta|$  and a(x) := |x|, all the assumptions hold if  $b(\theta) := |\theta| + 1$  and P is any law on  $\mathbb{R}$  with a unique median. Consistency, to be proved below, will imply that sample medians converge to the true median in this case.

Some consequences of the assumptions will be developed. The first one follows directly from Proposition 3.3.4 and the definitions:

**3.3.8 Lemma.** For any adjustable  $h(\cdot, \cdot)$  and adjustment function  $a(\cdot)$  for it, and any  $\theta \in \Theta$  for which  $\gamma_a(\theta) \in \mathbb{R}$ ,  $h(\theta, \cdot)$  is also an adjustment function.

A sequence of sets  $U_k \subset \Theta$  will be said to converge to a point  $\theta$  if  $\sup\{d(\theta, \phi) : \phi \in U_k\} \to 0$  as  $k \to \infty$ . Next, we have

**3.3.9 Lemma.** If (A-1), (A-2), and (A-3) hold and  $a(\cdot)$  is an adjustment function for which (3.3.5) holds, with  $b(\cdot)$  continuous, then

(A-2') for any  $\theta$ , as an open neighborhood  $U_k$  of  $\theta$  converges to  $\{\theta\}$ ,

$$E(\inf\{h(\phi, x) - a(x) : \phi \in U_k\}) \rightarrow \gamma(\theta) \le +\infty.$$

**Proof.** Separability (A-1) applied to sets  $J = [q, +\infty)$  for all rational q and joint measurability of  $h(\cdot, \cdot)$  imply that the infimum in (A-2') is equal almost surely to a measurable function of x. By (A-2), the integrand on the left converges to  $h(\theta, x) - a(x)$ , and it is larger for smaller neighborhoods  $U_k$ , so in this sense the convergence is monotone. Since  $b(\cdot)$  is continuous and positive, it is bounded on any neighborhood  $U_k$  with compact closure, say  $0 < b(\phi) \le M$  for all  $\phi \in U_k$ . Then by (3.3.5),  $h(\phi, x) - a(x) \ge -Mu(x)$  for all  $\phi \in U_k$  and all x. Thus the stated convergence holds by monotone convergence (RAP, 4.3.2) for a fixed sequence of neighborhoods of  $\theta$  such as  $\{\phi: d(\phi, \theta) < 1/n\}$  where d is a metric for the topology of  $\Theta$ . So, for any  $\varepsilon > 0$ , there is a neighborhood  $U_k$  of  $\theta$  such that the expression being shown to converge is larger than  $\gamma(\theta) - \varepsilon$  if  $\gamma(\theta)$  is finite, or larger than  $1/\varepsilon$  if  $\gamma(\theta) = +\infty$ , and the same will hold for any smaller neighborhood.

Note that (3.3.1), the definition of approximate M-estimator, is not affected by subtracting a(x) from  $h(\theta, x)$ .

By the alternate formulation given for separability (A-1),  $h(\theta, x) - a(x)$  is separable and since  $b(\theta)$  is continuous and strictly positive,  $(h(\theta, x) - a(x))/b(\theta)$  is also separable.

For any adjustable  $h(\cdot,\cdot)$  and adjustment function  $a(\cdot)$  for it, let  $h_a(\theta,x) := h(\theta,x) - a(x)$ . If (A-5) holds, this notation will mean that  $a(\cdot)$  has been chosen so that it holds.

**3.3.10 Lemma**. If (A-1), (A-3), (A-4), and (A-5) hold, then there is a compact set  $C \subset \Theta$  such that for every sequence  $T_n$  of approximate M-estimators, almost surely there will be some  $n_0$  such that  $T_n \in C$  for all  $n \geq n_0$ , in the sense that

(3.3.11) 
$$1_{\{T_n \in C\}} \to 1$$
 almost uniformly as  $n \to \infty$ .

**Proof.** If  $\Theta$  is compact there is no problem. Otherwise, by (3.3.6) there is a compact C and an  $\varepsilon$  with  $0 < \varepsilon < 1$  such that

$$\inf\{b(\theta): \theta \notin C\} \geq (\gamma(\theta_0) + \varepsilon)/(1 - \varepsilon).$$

(Note: the  $1 - \varepsilon$  in the denominator is useful when  $\gamma(\theta_0) + \varepsilon > 0$  and otherwise makes little difference as  $\varepsilon \downarrow 0$ .) By (3.3.5), (3.3.7), (A-1), and monotone convergence as in the last proof, C can be chosen large enough so that

$$E(\inf\{h_a(\theta,x)/b(\theta): \theta \notin C\}) \geq 1-\varepsilon/2.$$

Then by the strong law of large numbers (RAP, Sec. 8.3), where a function with expectation  $+\infty$  can be replaced by a smaller function with large positive expectation, a.s. for n large enough

$$\frac{1}{n}\inf\{\sum_{i=1}^n h_a(\theta, X_i)/b(\theta): \theta \notin C\} \geq \frac{1}{n}\sum_{i=1}^n\inf\{h_a(\theta, X_i)/b(\theta): \theta \notin C\} > 1 - \varepsilon.$$

Note that the infima are measurable since by separability of  $h(\cdot, \cdot)$ , measurability of  $a(\cdot)$  and continuity of  $b(\cdot)$ , they can be restricted to a countable (dense) set in the complement of C. Then for any  $\theta \notin C$ ,

$$\frac{1}{n} \sum_{i=1}^{n} h_a(\theta, X_i) \geq (1 - \varepsilon)b(\theta) \geq \gamma(\theta_0) + \varepsilon.$$

On the other hand, for n large enough

$$\inf_{\theta} \frac{1}{n} \sum_{i=1}^{n} h_a(\theta, X_i) \leq \frac{1}{n} \sum_{i=1}^{n} h_a(\theta_0, X_i) \leq \gamma(\theta_0) + \varepsilon/2,$$

so as soon as the expression in (3.3.1) is less than  $\varepsilon/2$ , the same will hold for  $h_a$  since terms  $a(X_i)$  cancel, and  $T_n \in C$ .

**3.3.13 Theorem**. Let  $\{T_n\}$  be a sequence of approximate M-estimators. Assume either (a) (A-1) through (A-5) hold, or (b) (A-1), (A-2'), (A-3) and (A-4) hold, and for some compact C, (3.3.11) holds. Then  $T_n \to \theta_0$  almost uniformly.

**Proof.** Assumptions (a) imply (A-2') by Lemma 3.3.9, and (3.3.11) by Lemma 3.3.10. So assumptions (b) hold in either case. By (3.3.11),  $\Theta$  can be assumed to be a compact set C: take any point  $\psi$  of C and when  $T_n$  takes a value outside of C, redefine it as  $\psi$ . It can also be assumed that  $\theta_0 \in C$  by adjoining it if necessary, and the proof below will show that  $\theta_0$  had to be in C.

Let U be an open neighborhood of  $\theta_0$ . It follows from (A-2') that  $\gamma(\cdot)$  is lower semicontinuous. Thus its infimum on the compact set  $C \setminus U$  is attained: let  $\theta_k$  be a sequence in  $C \setminus U$  on which  $\gamma$  converges to its infimum; we can assume that  $\theta_k$  converges to some  $\theta_{\infty}$ , and then  $\gamma$  attains its minimum on  $C \setminus U$  at  $\theta_{\infty}$ . By (A-4),  $\inf_{C \setminus U} \gamma = \gamma(\theta_{\infty}) > \gamma(\theta_0)$ . Let  $\varepsilon := (\gamma(\theta_{\infty}) - \gamma(\theta_{0}))/4$ , or if  $\gamma(\theta_{\infty}) = +\infty$  let  $\varepsilon := 1$ . By (A-2'), each  $\theta \in C \setminus U$  has an open neighborhood  $U_{\theta}$  such that

$$E(\inf\{h_a(\phi, x): \phi \in U_\theta\}) \geq \gamma(\theta_0) + 3\varepsilon.$$

Again, the infimum is measurable since by separability it can be restricted to a countable dense set in  $U_{\theta}$ . Take finitely many points  $\theta(j)$ , j = 1, ..., N, such that the neighborhoods  $U_j := U_{\theta(j)}$  cover  $C \setminus U$ . By the strong law of large numbers, as in the proof of Lemma 3.3.10, we have a.s. for n large enough and each j = 1, ..., N,

$$\inf\left\{\frac{1}{n}\sum_{i=1}^{n}h_{a}(\phi,X_{i}): \phi \in U_{j}\right\} \geq \frac{1}{n}\sum_{i=1}^{n}\inf\left\{h_{a}(\phi,X_{i}): \phi \in U_{j}\right\} \geq \gamma(\theta_{0}) + 2\varepsilon$$
and  $n^{-1}\sum_{i=1}^{n}h_{a}(\theta_{0},X_{i}) \leq \gamma(\theta_{0}) + \varepsilon$ . It follows that
$$\inf\left\{\frac{1}{n}\sum_{i=1}^{n}h_{a}(\theta,X_{i}): \theta \in C \setminus U\right\} \geq \frac{1}{n}\sum_{i=1}^{n}h_{a}(\theta_{0},X_{i}) + \varepsilon$$

$$(3.3.14)$$

$$\geq \inf\left\{\frac{1}{n}\sum_{i=1}^{n}h_{a}(\theta,X_{i}): \theta \in U\right\} + \varepsilon,$$

so  $\Pr\{T_n \in U \text{ for all } n \text{ large enough}\} = 1$ . This completes the proof.

Next let's recall the notion of likelihood ratio. Let P and Q be two probability measures on the same sample space S. Then there always exists some measure  $\mu$  such that both P and Q have densities with respect to  $\mu$ , where  $\mu$  is a  $\sigma$ -finite measure, in other words there is a countable sequence of sets  $A_n$  whose union is all of S with  $\mu(A_n) < \infty$  for each n. For example, if the sample space is a Euclidean space  $\mathbb{R}^d$  and P and Q both have densities, then we can take  $\mu$  to be Lebesgue measure (volume),  $d\mu(x) = dx_1 dx_2 \cdots dx_d$ . If P and Q are both discrete probabilities concentrated on a countable set S such as the nonnegative integers, we can take  $\mu$  to be counting measure on S, where  $\mu(A)$  is the number of elements in A for any  $A \subset S$ . In complete generality, we can always take  $\mu = P + Q$ , by the Radon-Nikodym theorem in measure theory.

Suppose then that P has a density  $f = dP/d\mu$  and Q has a density  $g = dQ/d\mu$  with respect to  $\mu$ . Then the likelihood ratio of Q to P is defined as  $R_{Q/P}(x) = g(x)/f(x)$ , or as  $+\infty$  if g(x) > f(x) = 0, or as 0 if g(x) = f(x) = 0. Then the likelihood ratio is well-defined and unique in the sense that if R and S are two functions with the properties of  $R_{Q/P}$ , possibly defined for different  $\mu$ 's, then R = S except possibly on some set A with P(A) = Q(A) = 0. This is shown in Appendix A of the 18.466 Mathematical Statistics notes on the MIT OCW site.

To apply Theorem 3.3.13 to the case of maximum likelihood estimation the following will help. Let P and Q be two laws on a sample space  $(X, \mathcal{B})$ . Let

$$I(P,Q) := \int \log(R_{P/Q}) dP = -\int \log(R_{Q/P}) dP,$$

called the Kullback-Leibler information of P with respect to Q. Here we have  $R_{P/Q} \equiv 1/R_{Q/P}$  with  $1/0 := +\infty$  and  $1/+\infty := 0$ .

**3.3.15 Theorem.** Let  $(X, \mathcal{B})$  be a sample space and P, Q any two laws on it. Then  $I(P,Q) \geq 0$  and I(P,Q) = 0 if and only if P = Q.

**Proof.** By derivatives, it's easy to check that  $\log x \le x - 1$  for all  $x \ge 0$ , with  $\log x = x - 1$  if and only if x = 1. Thus

$$I(P,Q) = \int -\log(R_{Q/P})dP \ge \int 1 - R_{Q/P}dP \ge 0,$$

with equality if and only if  $R_{Q/P} = 1$  a.s. for P, and then Q = P.

Although I(P,Q) is sometimes called a metric or distance, it is not symmetric in P and Q, nor does it satisfy the triangle inequality.

Consistency of approximate maximum likelihood estimators, under suitable conditions, does follow from Theorem 3.3.13, and assumption (A-3), and (A-4) for the true  $\theta_0$ , will follow from Theorem 3.3.15 rather than having to be assumed:

**3.3.16 Theorem**. Assume (A-1) holds in the log likelihood case, for a measurable family  $\{P_{\theta}, \theta \in \Theta\}$  dominated by a  $\sigma$ -finite measure v, with  $(dP_{\theta}/dv)(x) = f(\theta, x)$ , so that  $h(\theta, x) := -\log f(\theta, x)$ . Also suppose  $P = P_{\theta_0}$  for some  $\theta_0 \in \Theta$  and  $P_{\theta_0} \neq P_{\theta}$  for any  $\theta \neq \theta_0$ . Then (A-3) holds and (A-4) holds for the given  $\theta_0$ . Assume  $T_n$  are approximate maximum likelihood estimators, i.e. approximate M-estimators in this case. If (A-2) and (A-5) also hold, or (A-2') and (3.3.11), then the  $T_n$  are consistent.

**Proof.** If (A-1) through (A-5) hold then (A-2') and (3.3.11) hold by Lemmas 3.3.9 and 3.3.10, and then Theorem 3.3.13 applies. So just (A-3) and (A-4) need to be proved. Let  $a(x) := -\log f(\theta_0, x)$ . We have  $0 < f(\theta_0, x) < \infty$  a.s. for P, and so  $-\infty < \log f(\theta_0, x) < \infty$ . Thus  $h(\theta, x) - a(x)$  is well-defined a.s. and equals

$$-\log(f(\theta, x)/f(\theta_0, x)) = -\log R_{P_{\theta}/P_{\theta_0}}$$

as shown in Appendix A of the 18.466 OCW notes. Thus for all  $\theta$ ,

$$\gamma(\theta) := E[h(\theta, x) - a(x)] = I(P_{\theta_0}, P_{\theta}) \ge 0 > -\infty$$

by Theorem 3.3.15 and  $\gamma(\theta_0) = 0$ , so (A-3) holds. Also by Theorem 3.3.15,  $\gamma(\theta) = 0$  only for  $\theta = \theta_0$ , so (A-4) also holds.

## **PROBLEMS**

- 1. Let  $h(\theta, x) = (x \theta)^2$  for  $x, \theta \in \mathbb{R}$ .
  - (a) Show that h is adjustable for a law P if and only if  $\int |x| dP(x) < \infty$ .
  - (b) Show that then (A-4) holds and evaluate  $\theta_0$ .
  - (c) Show that for some  $a(\cdot)$ , (A-5) holds in this case for  $b(\theta) = \theta^2 + 1$ .
- 2. Recall that for a law P on  $\mathbb{R}$ , a point m is a median of P iff both  $P((-\infty, x]) \geq 1/2$  and  $P([x, +\infty)) \geq 1/2$ . Thus if P is a continuous distribution without atoms, m is a median if and only if  $P((-\infty, m]) = 1/2$ . If P is any law on  $\mathbb{R}$  having a unique median  $\theta_0$  and  $h(\theta, x) := |x \theta|$ , show that conditions (A-1) through (A-5) hold for some  $a(\cdot)$  and  $b(\cdot)$  (suggested in the text).

## NOTES

An early result relating to consistency of maximum likelihood estimators was given by Cramér (1946), §33.3, namely, that under some hypotheses, there exist roots of the likelihood equation(s) converging in probability to the true value  $\theta_0$ . If there are multiple roots, it was not clear how to select roots that would converge, but in case there was a unique root and it gave a maximum of the likelihood (as with exponential families), Cramér's theorem gave consistency of maximum likelihood estimates under his conditions.

Wald (1949) proved consistency of maximum likelihood estimates under some conditions. The present forms of the theorems and proofs through 3.3.13 are essentially as in Huber (1967). Dudley (1998) gave an extension, replacing the local compactness assumption by a uniform law of large numbers assumption. Kullback and Leibler (1951) defined their information and gave Theorem 3.3.15. Kullback (1983) gives an update.

## REFERENCES

- Cramér, Harald (1945). *Mathematical Methods of Statistics*. Almqvist & Wicksells, Uppsala, Sweden; Princeton University Press, 1946; 10th printing 1963.
- Dudley, R. M. (1998). Consistency of M-estimators and one-sided bracketing. In High Dimensional Probability, Progress in Probability 43, Birkhäuser, Basel.
- Haughton, D. M.-A. (1983). On the choice of a model to fit data from an exponential family. Ph. D. dissertation, Mathematics, M.I.T.
- Haughton, D. M.-A. (1988). On the choice of a model to fit data from an exponential family. *Ann. Statist.* **16**, 342-355.
- Hoffman, K. (1975). Analysis in Euclidean Space. Prentice-Hall, Englewood Cliffs, NJ.
- Huber, P. J. (1967). The behavior of maximum likelihood estimates under nonstandard conditions. *Proc. Fifth Berkeley Symp. Math. Statist. Probab.* 1 (Univ. of Calif. Press, Berkeley and Los Angeles), 221-233.
- Huber, P. J. (1981). Robust Statistics. Wiley, New York.
- Kullback, S. (1983). Kullback information. In *Encyclopedia of Statistical Sciences* 4, pp. 421-425, Eds. S. Kotz, N. L. Johnson. Wiley, New York.
- Kullback, S., and Leibler, R. A. (1951). On information and sufficiency. *Ann. Math. Statist.* **22**, 79-86.
- Wald, A. (1949). Note on the consistency of the maximum likelihood estimate. *Ann. Math. Statist.* **20**, 595-601.

---

A rough definition of an outlier is that it's an observation far away from the bulk of the data. There may be multiple outliers in a given data set, especially if it's large. For example, Bill Gates's wealth would be an outlier among those of all individuals.

One of the main ideas of robustness is to use statistical procedures that are not sensitive to outliers. If there are outliers in a data set  $X_1, ..., X_n$ , then at least one of the extreme order statistics  $X_{(1)}$  or  $X_{(n)}$  must be an outlier.

The ordinary sample mean  $\overline{X}$  and sample variance  $s_X^2 = \frac{1}{n-1} \sum_{j=1}^n (X_j - \overline{X})^2$  are not robust because  $\overline{X}$  and, even more,  $s_X^2$  are sensitive to outliers. If just one large observation  $X_{(n)}$  becomes arbitrarily large, then both  $\overline{X}$  and  $s_X^2$  go to  $+\infty$ .

On the other hand, nonparametric methods based on ranks, such as the Wilcoxon rank-sum test and the runs test, are not at all sensitive to outliers. If  $X_{(n)}$  is made larger it still keeps the same rank, n, so the values of the nonparametric statistics don't change at all. The same is true if  $X_{(1)} \to -\infty$ , when it keeps the same rank 1.

But, what is an outlier? It turns out to be even harder to give a precise definition than for a sample quantile. Some books give examples of outliers and a few try to give specific rules for identifying them.

An example, given in a book by D. Freedman, Pisani, and R. Purves, is that an observation 5 standard deviations away from the mean would be an outlier. For a normal distribution, the probability of such an observation is less than  $6 \cdot 10^{-7}$ , so from a truly normal distribution, such a thing wouldn't happen except very rarely or in a large data set. Put another way, normal distributions don't tend to produce outliers: as n gets large,  $X_{(n)}$  tends to grow, but only slowly, of the order of  $\sqrt{\log n}$ , so  $X_{(n)}$  won't be much larger than  $X_{(n-1)}$ , and so on. Or, if one thinks one has a normal distribution but gets an observation 5 standard deviations from the mean, in a sample with not too large n, say n < 10,000, that observation must not really be from the normal distribution, it must be from some other distribution, sometimes called a contaminating distribution. It might have resulted from some error, or a wrong normality assumption.

There's a problem though with defining outliers in terms of standard deviations if the standard deviation is estimated from the sample, because the sample standard deviation is itself so much influenced by the outlier. Specifically, just looking at the formula for sample variance, to have an observation  $X_j$  five or more sample standard deviations away from the sample mean,  $|X_j - \overline{X}| \geq 5s_X$ , requires a sample size easily seen to be at least 26 (since 26-1=25) and in fact at least 27. But we can recognize outliers in smaller samples than that. If you take Bill Gates's wealth, together with that of 9 other people chosen at random from the population to form a sample of size 10, you will see that Gates's wealth is an outlier by the rough definition.

Other people have tried to define outliers precisely as follows. Define the lower quartile of the sample  $q_1$  as the 1/4 quantile and the upper quartile  $q_3$  as the 3/4 quantile (recalling however that for samples, quantiles have slightly varying definitions). The interquartile range IQR is defined as  $q_3 - q_1$ . That's a scale statistic that's robust, not sensitive to outliers: if we move data in the lower quarter or upper quarter of the order statistics outward, it won't change the IQR. An attempted definition of outlier is an observation that's distant by at least 3IQR from the interval  $[q_1, q_3]$ .

But here's an example where that definition doesn't work well. Let  $X_j$  be observations on amount of precipitation (rain, or water equivalent of snow) per day over a year. Suppose that on at least 3/4 of all days in the year, there is no measurable rain or snow at a given location (maybe, a relatively dry one, but not all that dry). Then  $q_1$  and  $q_3$  will both be 0, so IQR = 0. So by the attempted definition, any precipitation at all would be called an outlier, which doesn't seem right.

If there was precipitation on more than 1/4 of all days, but less than half, it could be that  $q_3$ , although positive, is quite small and so IQR, which equals  $q_3$  in this case, is small. So we'd be calling amounts of rain "outliers" if they were larger than  $4q_3$  which might still not be that large.

By the way, the median rainfall per day in either case would be 0, which is very uninformative about rainfall.

It seems that we might only want to call a daily amount of rain or snow an outlier if we compared it to for example the 10 or 20 days with most rain in a typical year. So the choice of what to call an outlier may depend on what kind of data we're looking at, not on any universal numerical rule.

---

$18.465 \ \mathrm{notes}, \ \mathrm{March} \ 29, \ 2005, \ \mathrm{revised} \ \mathrm{May} \ 2$  The spatial median

In one dimension, for any probability distribution function F with a finite first moment, the medians are exactly the values of m for which  $\int |x-m|dF(x)$  is minimized, using a definition allowing an interval of medians on which the distribution function F equals 1/2. This characterization allows the definition of median to be extended to more than one dimension. The spatial median was apparently defined and used in the 1930's by Gini and others.

Let  $|\cdot|$  be the usual Euclidean norm on  $\mathbb{R}^d$ ,  $|x| = (x_1^2 + ... + x_d^2)^{1/2}$ . For any  $d \ge 1$  and probability measure P on  $\mathbb{R}^d$ , and any fixed  $s_0 \in \mathbb{R}^d$ , a spatial median of P is defined as any s such that

$$M(s, P, s_0) := \int |s - x| - |s_0 - x| dP(x)$$

is minimized. Note that if  $\int |x| dP(x) < \infty$ , a spatial median is any s such that  $\int |s-x| dP(x)$  is minimized.

A set C in a Euclidean space  $\mathbb{R}^d$  is called convex if and only if for any  $x,y\in C$  and  $0\leq \lambda\leq 1$  we have  $\lambda x+(1-\lambda)y\in C$ . A real-valued function f on a convex set C is called convex if and only if for all such x,y and  $\lambda$  we have  $f(\lambda x+(1-\lambda)y)\leq \lambda f(x)+(1-\lambda)f(y)$ . Here f will be called strictly convex if whenever  $x\neq y\in C$  and  $0<\lambda<1$  we have  $f(\lambda x+(1-\lambda)y)<\lambda f(x)+(1-\lambda)f(y)$ . It's easily seen that a function f on an interval is convex if its second derivative is nonnegative and strictly convex if its second derivative is strictly positive. For example, on  $\mathbb{R}^1$ ,  $f(x)=x^2$  is strictly convex and f(x)=|x| is convex but not strictly convex. (On convex functions see e.g. reference RAP, Chapter 6.)

In the next fact the harder part to prove, the uniqueness, is essentially due to J. B. S. Haldane (1948).

**Theorem**. For any probability measure P on  $\mathbb{R}^d$ , a spatial median always exists and doesn't depend on  $s_0$ . If P is not concentrated in any line, then its spatial median is unique.

**Remark**. So, the spatial median has a better uniqueness property in higher dimensions than in one dimension. On the other hand in one dimension the median is equivariant under monotone increasing continuous transformations — at least when the median is unique, as for odd sample size, or if we take the interval of all medians when it isn't. In  $\mathbb{R}^d$  for  $d \geq 2$  the spatial median is equivariant under Euclidean transformations such as rotations, reflections and translations, and under constant multiples, but not under general affine transformations.

**Proof.** Since

$$m(s, x, s_0) := |s - x| - |s_0 - x| \le |s - s_0|,$$

 $g(s) := M(s, P, s_0)$  is always finite. Clearly, it's continuous in s, and goes to  $\infty$  as  $s \to \infty$  for fixed  $s_0$ . Thus the infimum of  $M(s, P, s_0)$  is attained, and a spatial median always exists. Changing  $s_0$  only adds a constant to the integral, so the minimization doesn't depend on  $s_0$ .

For any fixed x and  $s_0$ ,  $s \mapsto m(s, x, s_0)$  is a convex function of s. For s in a bounded set,  $m(s, x, s_0)$  is bounded uniformly in x. It follows that  $M(s, P, s_0)$  is a convex function of s for fixed P and  $s_0$ .

Now suppose P is not concentrated in a line. To prove that the spatial median is unique, suppose it is not. Let g have its minimum value at two points  $s \neq t$ . Since g is convex, it has the same value at all points of the closed line segment joining s to t. On the other hand,  $m(\lambda s + (1 - \lambda)t, x, s_0)$  is a convex function of  $\lambda$ , strictly convex if x is not on the line through s and t. Since the set of such x has positive P-probability,  $M(\lambda s + (1 - \lambda)t, P, s_0)$  is a strictly convex function of  $\lambda$ , a contradiction, so the minimum is unique.

**Notes.** Haldane (1948) proved uniqueness of the spatial median in  $\mathbb{R}^k$ ,  $k \geq 2$ . (In Haldane's proof, note that  $d^2R/dx^2 > 0$  unless  $y_r = 0$  for all r, in which case all the observations are on a line.) Haldane gives the proof in detail for a finite sample (empirical measure).

The device of taking  $|s - x| - |s_0 - x|$  in place of |s - x|, so as to define the spatial median for arbitrary laws (which may not have a first moment), is mentioned for example in Huber (1981, p. 44).

## REFERENCES

Haldane, J. B. S. (1948). Note on the median of a multivariate distribution. *Biometrika* **35**, 414-415.

Huber, P. J. (1981). *Robust Statistics*. Wiley, New York. Reprinted, 2004, Wiley-Interscience.

RAP = Dudley, R. M. (1993). *Real Analysis and Probability*. 2d ed., Cambridge University Press, 2002.

---

## Breakdown points of some 1-dimensional location estimators

Recall that a set C in a real vector space is called *convex* if for any x, y in C and  $0 \le \lambda \le 1$  we have  $\lambda x + (1 - \lambda)y \in C$ . In the real line, a convex set is just an interval, a half-line or the whole line. At a finite endpoint it may be open or closed. A real-valued function f on the convex set C is called *convex* if for each x, y, and  $\lambda$  as before, we have  $f(\lambda x + (1 - \lambda)y) \le \lambda f(x) + (1 - \lambda)f(y)$ . Here f is called *strictly convex* if whenever  $x \ne y$  and  $0 < \lambda < 1$ , " $\le$ " is replaced by "<" in the definition of convex function.

For example, the function  $f(x) = x^2$  on  $\mathbb{R}$  is strictly convex. The function f(x) = |x| is convex, but not strictly convex.

A non-constant function  $\rho(\theta, x)$  for x and  $\theta$  real will be called a wide-sense Huber function if  $\rho(\theta, x) \equiv \rho(|x - \theta|)$  where  $\rho(x) \equiv \rho(-x)$ ,  $\rho$  is convex, and  $\rho(x)/|x|$  is bounded as  $|x| \to \infty$ . The convexity and symmetry properties imply that  $\rho$  attains its absolute minimum at 0 (and perhaps elsewhere). Examples of wide-sense Huber functions include

- (a)  $\rho(x) := |x|,$
- (b)  $\rho(x) := (c^2 + x^2)^{1/2} c$  for any real c > 0, and
- (c)  $\rho(x) := x^2$  for  $|x| \le b$  and  $\rho(x) := c|x| d$  for |x| > b where b > 0 and the other constants are chosen to make  $\rho$  continuously differentiable. Then  $cb d = b^2$  and 2b = c, so  $d = b^2$  and for |x| > b,  $\rho(x) = b(2|x| b)$ .

Since Huber especially studied functions defined by (c), they might be called "narrow-sense Huber functions."

The functions in (b) and (c) are strictly convex in neighborhoods of 0, and the ones in (b) are strictly convex everywhere. Note that if  $\rho$  is convex, then the sum  $\sum_{i=1}^{n} \rho(X_i - \theta)$  is convex in  $\theta$  for any  $X_i$ . Also, if  $\rho$  is strictly convex for  $|x| \leq b$ , then the sum is strictly convex in a neighborhood of  $\theta$  for any  $\theta$  such that  $|X_i - \theta| < b$  for some i. For n large and b not too small, the set of such  $\theta$  will often include the set on which the sum takes its smallest values, so that the minimum will be unique. We will always have uniqueness if  $\rho$  is strictly convex everywhere, as  $(c^2 + x^2)^{1/2}$  is.

Let  $\psi$  be a real-valued function of a real variable which is odd (meaning  $\psi(-x) \equiv -\psi(x)$ ), nondecreasing, nonconstant, and bounded. Then  $\psi(-t) \leq 0 = \psi(0) \leq \psi(t)$  for all  $t \geq 0$  and  $\psi(-t) < 0 < \psi(t)$  for some t > 0 since  $\psi$  is nonconstant. We will have  $\psi(t) \to A$  as  $t \to +\infty$  for some A > 0. Examples of such functions  $\psi$  include the derivatives  $\rho'(x)$  of wide-sense Huber functions, where such derivatives are defined, with suitable choices where they are not defined, specifically,  $\psi(0) = 0$  in all cases,  $\psi(x) := \rho'(x+) := \lim_{h\downarrow 0} (\rho(x+h) - \rho(x))/h$  and  $\psi(-x) := -\psi(x)$  for x > 0. Then for location, the psi function of two variables is defined by  $\psi(\theta, x) := \psi(x-\theta)$ , which is nonincreasing in  $\theta$ . Given a sample  $(X_1, \ldots, X_n)$ , let

$$\theta^* := \theta^*(X_1, ..., X_n) := \sup \left\{ \theta : \sum_{i=1}^n \psi(X_i - \theta) > 0 \right\}.$$

This is finite since the sum is  $\leq 0$  for  $\theta \geq X_{(n)}$  and also > 0 when  $\theta \leq X_{(1)} - t$  for some t

such that  $\psi(t) > 0$ . Analogously, define

$$\theta^{**} := \theta^{**}(X_1, \dots, X_n) := \inf \left\{ \theta : \sum_{i=1}^n \psi(X_i - \theta) < 0 \right\},$$

which is also finite since the sum is  $\geq 0$  for  $\theta \leq X_{(1)}$  and < 0 for  $\theta \geq X_{(n)} + t$ . We have  $\theta^* \leq \theta^{**}$  because of the monotonicity of  $\psi$ . In order to have a unique estimator, the (location) *M*-estimator for the sample (based on  $\psi$ ) will be defined, as for the sample median, by

$$\hat{\theta} := \hat{\theta}(X_1, \dots, X_n) := \frac{1}{2}(\theta^* + \theta^{**})(X_1, \dots, X_n).$$

It will shown that such estimators have the same (finite sample) breakdown points as the median, converging to 1/2 as  $n \to \infty$  and as large as possible. Consider also scale-adjusted M-estimators, where instead of  $\sum_{i=1}^{n} \psi(X_i - \theta)$  we have  $\sum_{i=1}^{n} \psi((X_i - \theta)/S)$  and S is a scale estimator, with nonnegative values (a specific scale estimator will be given below). The resulting estimator will be called  $\hat{\theta}_S$ . If S = 0, then by definition set

$$\psi((X_i - \theta)/S) := \begin{cases} A, & X_i > \theta \\ 0, & X_i = \theta \\ -A, & X_i < \theta. \end{cases}$$

It's easily seen that if S=0 then the M-estimator  $\hat{\theta}_S$  based on the above definitions is exactly the median.

For a particular choice of S, let M be the median of the sample, defined as  $X_{(k+1)}$  if n=2k+1 is odd, and  $(X_{(k)}+X_{(k+1)})/2$  if n=2k is even. Let MAD denote the median absolute deviation, namely the median of  $|X_i-M|$ , and  $S=\mathrm{MAD}/.6745$ , where the constant 0.6745 is (to the given accuracy) the median of |Z| for a standard normal variable Z, and thus, S estimates the standard deviation  $\sigma$  for normally distributed data. as in Randles and Wolfe, Sec. 7.4.

The following fact and proof are adapted from Huber (1981), pp. 52-53.

**Theorem.** Let  $\psi$  be a function from  $\mathbb{R}$  into  $\mathbb{R}$ , which is odd, nondecreasing, nonconstant, and bounded. Then the M-estimator  $\hat{\theta}$  defined by  $\psi$  has breakdown point  $\frac{1}{2} - \frac{1}{n}$  if n is even and  $\frac{1}{2} - \frac{1}{2n}$  if n is odd. The same holds for the scale-adjusted M-estimator  $\hat{\theta}_S$  where we consider  $\psi((X_i - \theta)/S)$  for the S just defined.

**Proof.** As  $t \to \infty$  we have  $\psi(t) \uparrow A$ . For  $0 < \varepsilon < 1$  there is a  $\kappa < \infty$  such that  $\psi(\kappa) \geq (1-\varepsilon)A$ . Then  $\sum_{i=1}^n \psi(X_{(i)} - \theta) < 0$  if  $X_{(i)} - \theta < -\kappa$  for j values of i where  $-j(1-\varepsilon)A + (n-j)A < 0$ , or equivalently  $j > n/(2-\varepsilon)$ . Now  $\theta > X_{(i)} + \kappa$  for at least j values of i is equivalent to  $\theta > X_{(j)} + \kappa$ . So we have  $\theta^{**} \leq X_{(j)} + \kappa$  where j is the smallest integer  $> n/(2-\varepsilon)$ .

Now if  $Y_i = X_i$  for at least j values of i = 1, ..., n, we have  $Y_{(j)} \leq X_{(n)}$ , so  $\theta^{**}(Y_1, ..., Y_n) \leq X_{(n)} + \kappa$  and  $\theta^{**}$  remains bounded above under the given conditions. Symmetrically,  $\theta^*$  stays bounded below. It follows that  $\hat{\theta}$  stays bounded, so the breakdown point of  $\hat{\theta}$  is at least 1 - j/n.

If i > n/2, then for some  $\varepsilon > 0$ ,  $i > n/(2-\varepsilon)$ , so we can take j as the smallest integer greater than n/2. Then for n = 2m even, or for n = 2m + 1 odd, we have j = m + 1. It follows that the breakdown point of  $\hat{\theta}$  is at least as large as stated for each sample size.

 $\hat{\theta}$  is a location equivariant estimator, so its breakdown point is less than 1/2, by Theorem 2 of the handout "Introduction to robustness: breakdown points." So the breakdown point is no larger than for the median and is the same as for the median, proving the first statement in the theorem.

Next, consider the scale-adjusted case and first, the breakdown point of S. If j is again the smallest integer > n/2, and  $Y =_{n-j} X$ , so that  $Y_i = X_i$  for at least j values of i, then  $X_{(1)} \leq Y_i \leq X_{(n)}$  for at least j values of i. Thus as noted above

$$(1) Y_{(j)} \le X_{(n)}$$

and if  $M_Y$  is the median of  $Y_1, ..., Y_n$ , then  $X_{(1)} \leq M_Y \leq X_{(n)}$ . Also,  $|Y_i - M_Y| \leq X_{(n)} - X_{(1)}$  for at least j values of i, so MAD<sub>Y</sub>, the median of  $|Y_i - M_Y|$ , satisfies MAD<sub>Y</sub>  $\leq X_{(n)} - X_{(1)}$  and

(2) 
$$S_Y := S(Y_1, ..., Y_n) \le K_X := (X_{(n)} - X_{(1)})/0.6745.$$

On the other hand if  $Y =_k X$  for  $k \ge n/2$  we can have  $M_Y$  unbounded and also  $MAD_Y$  unbounded. So the MAD and S have the same breakdown point as the median itself.

It's possible that S=0 if there are enough tied observations. As noted above, the M-estimator  $\hat{\theta}_S$  equals the sample median in that case.

Returning to the case where j is the smallest integer > n/2 and  $Y =_{n-j} X$ , take  $\varepsilon > 0$  small enough so that  $j > n/(2-\varepsilon)$  and choose  $\kappa$  accordingly. Then we will have  $\sum_{i=1}^{n} \psi((Y_i - \theta)/S_Y) < 0$  if  $Y_i - \theta < -\kappa S_Y$  for at least j values of i, in other words if  $Y_{(j)} - \theta < -\kappa S_Y$  or  $\theta > Y_{(j)} + \kappa S_Y$ . This will hold if  $\theta > X_{(n)} + \kappa K_X$  by (1) and (2). So

$$\theta^{**}(Y_1, ..., Y_n) \le X_{(n)} + \kappa K_X.$$

Symmetrically, we have

$$\theta^*(Y_1, ..., Y_n) \ge X_{(1)} - \kappa K_X.$$

So  $\hat{\theta}(Y_1, ..., Y_n)$  remains bounded for  $Y =_{n-j} X$  and the breakdown point of  $\hat{\theta}$  is at least as large as for the median. If S = 0, this doesn't cause breakdown of the M-estimator because the median of a sample  $Y_1, ..., Y_n$  containing more than n/2 of the original observations  $X_1, ..., X_n$  must be between  $X_{(1)}$  and  $X_{(n)}$  and so can't become unbounded.

Since  $\hat{\theta}_S$  is also location equivariant, its breakdown point is also < 1/2 and so equals that of the median, as stated in the Theorem.

## REFERENCE

Huber, P. J. (1981). Robust Statistics. Wiley, New York.

---

Let X be a real random variable with distribution function F, so that  $F(x) = P(X \le x)$  for all x. Let 0 . Then a number x is called a pth quantile of F, or of X, if <math>F(x) = p, or more generally if  $F(x) \ge p$  and  $P(X \ge x) \ge 1 - p$ . The definition with F(x) = p applies to all continuous distributions. The more general definition is needed for discrete distributions where there may be no x with F(x) = p.

If a pth quantile x is uniquely determined, as it is if F is strictly increasing in a neighborhood of x, it is called the pth quantile of F or X and can be written as  $x_p$ . For a lot of distributions used in statistics such as  $\chi^2$  and F distributions, specific quantiles are tabulated such as the 0.95, 0.975, and 0.99 quantiles.

A median is a 1/2 quantile. If it is not unique, there is an interval of medians and the median is defined as the midpoint of this interval.

Now let's consider how to define pth quantiles  $\xi_p$  of a finite sample  $X_1, ..., X_n$ . A rough definition is that a fraction p of the observations should be less than (or equal)  $\xi_p$  and a fraction 1-p should be larger than (or equal) to  $\xi_p$ . If np is not an integer then we seem to be talking about a non-integer count of number of observations which is not well-defined.

There is a generally agreed-on definition of the 1/2 sample quantile, the sample median, namely if n=2k+1 odd, it's the middle order statistic  $X_{(k+1)}$ . If n=2k even, then it's  $(X_{(k)}+X_{(k+1)})/2$ . But it seems that for  $p \neq 1/2$  there is no such agreed definition. The next most often mentioned quantiles for finite samples are the quartiles, where p=1/4 (lower quartile) and p=3/4 (upper quartile). Possible summary statistics for a class's exam scores are to give the median and the upper and lower quartiles.

Other quantiles sometimes mentioned are percentiles, often used about scores for an individual on a standardized exam. The pth quantile is the same as the 100pth percentile.

I looked at several statistics books searching for precise definitions of sample quantiles. Many books have no words beginning with q in their subject indices. Other books including Randles and Wolfe (our text) mention quantiles only for probability distributions, not for samples.

I found precise definitions of sample pth quantiles for  $p \neq 1/2$  in four books. The four definitions were all different. I will list them, but there will not be regular problems assigned about these, just maybe some extra-credit problem(s). So, don't memorize them or pay very much attention to them. Just notice that from the rough definition, we'd expect  $\xi_p$  to be something like  $X_{(np)}$ , but np is often not an integer. To formulate the definitions, here is some notation. Let  $\lfloor x \rfloor$ , the integer part of x, be the largest integer  $\leq x$ . Let  $\{x\}$ , the fractional part of x, be  $x - \lfloor x \rfloor$ . Let  $x \in \mathbb{R}$  be the smallest integer  $x \in \mathbb{R}$ . Let  $x \in \mathbb{R}$  be  $x \in \mathbb{R}$  rounded to the nearest integer, rounded up if  $x \in \mathbb{R}$  is

Here are the definitions in alphabetical order by first author of the textbook. The pth quantile of a sample of n numbers with order statistics  $X_{(1)} \leq ... \leq X_{(n)}$  is:

- 1.  $X_{(r(np))}$  if p < 1/2,  $X_{(n+1-r(n(1-p)))}$  if p > 1/2, the sample median if p = 1/2 (Casella and Berger, Statistical Inference, 1990).
- 2.  $X_{(\lfloor (n+1)p\rfloor)} + \{(n+1)p\} (X_{(\lceil (n+1)p\rceil)} X_{(\lfloor (n+1)p\rfloor)})$ : R. Hogg and E. Tanis, *Probability and Statistical Inference*, Sixth Ed.

- 3.  $X_{(\lceil np \rceil)}$  if np is not an integer, or if it is,  $(X_{(np)} + X_{(np+1)})/2$ : R. A. Johnson, Miller and Freund's Probability and Statistics for Engineers 5th ed., 1994.
- 4.  $X_{(r((n+1)p))}$ , given just for p = 1/4 or 3/4 (would be undefined if (n+1)p < 1/2 or  $\geq n + (1/2)$ ): Mendenhall and Sincich, Statistics for Engineering and the Sciences.

Some of the apparent complexity of some definitions is motivated by a consideration of symmetry: if all  $X_i$  are replaced by  $-X_i$ , reversing the order of the order statistics while also changing their signs, one would like  $\xi_p$  for the  $-X_i$  to be  $-\xi_{1-p}$  for the  $X_i$ .

Since there is no agreement on a precise definition of sample quantiles other than the sample median, one can just keep in mind the rough definition.

---

Non-existence of some affinely equivariant location functionals in dimension  $d \geq 2$ 

An affine transformation from  $\mathbb{R}^d$  to itself is one of the form Ax = Bx + v for all  $x \in \mathbb{R}^d$  where B is a linear transformation  $(d \times d \text{ matrix})$  and v is a fixed vector. Then A will be called non-singular if and only if B is. Here x and v are  $d \times 1$  column vectors.

For any probability measure P and random variable X, which may be vector-valued, we have another probability measure  $P \circ X^{-1}$ , the distribution of X or image measure of P by X. For example, if P is defined on  $\mathbb{R}^d$  and  $x_j$  is the jth coordinate function on  $\mathbb{R}^d$ , then  $P \circ x_j^{-1}$  is the jth marginal of P, on  $\mathbb{R}$ .

Let  $\mathcal{P}$  be a collection of probability measures on  $\mathbb{R}^d$  and m a function from  $\mathcal{P}$  into  $\mathbb{R}^d$ . Then m will be called an *affinely equivariant location functional* on  $\mathcal{P}$  iff whenever  $P \in \mathcal{P}$  and A is a non-singular affine transformation, we have  $P \circ A^{-1} \in \mathcal{P}$  and  $m(P \circ A^{-1}) = Am(P)$ . Also,  $m(\cdot)$  will be called *singularly affine(ly) equivariant* if the same holds when A may be singular.

When d=1, the median is a singularly affine equivariant location functional defined on the class of all probability measures on  $\mathbb{R}$ . For d=1, a singular linear transformation B is just multiplication by 0, and so for any  $P, P \circ A^{-1}$  is concentrated in the point v. It turns out not to be restrictive to say that for such a distribution m should equal v. For  $d \geq 2$ , however, there are more singular matrices, and we will see that singular affine equivariance becomes very restrictive.

Recall that  $\delta_x(A) := 1_A(x) := 1$  if  $x \in A$  and 0 otherwise. For n = 1, 2, ..., and d = 1, 2, ..., let  $\mathcal{P}_{n,d}$  be the class of all empirical measures  $P_n = \frac{1}{n} \sum_{j=1}^n \delta_{x_j}$  on  $\mathbb{R}^d$  where each  $x_j = (x_{1j}, ..., x_{dj})' \in \mathbb{R}^d$ . Clearly, for any transformation A from  $\mathbb{R}^d$  into itself (affine or not) and  $P_n$  as given,  $P_n \circ A^{-1} = \frac{1}{n} \sum_{j=1}^n \delta_{A(x_j)} \in \mathcal{P}_{n,d}$ . Here is the main fact in this handout:

**Theorem** (Obenchain, 1971). Let  $d \geq 2$  and suppose m is a singularly affine equivariant location functional defined on  $\mathcal{P}_{n,d}$  for a given n. Then  $m(P_n) = \int x dP_n = \overline{x} = \sum_{j=1}^n x_j/n$  for all  $P_n \in \mathcal{P}_{n,d}$ .

**Remark**. For d=1 there are some robust singularly affine equivariant location functionals such as the median (and trimmed means, e.g. Randles and Wolfe, problem 7.4.2 pp. 246-247). But the sample mean  $\overline{x}$  has breakdown point 0 for all n, so a singularly affine equivariant location functional on  $\mathcal{P}_{n,d}$  for  $d \geq 2$  can't have any robustness. Thus, researchers consider affinely (not singularly) equivariant functionals, not defined on all of  $\mathcal{P}_{n,d}$ , e.g. not defined on  $P_n \circ A^{-1}$  for A singular.

**Proof.** For  $X_j \in \mathbb{R}^d$ , j = 1, ..., n, with  $X_j = (X_{1j}, ..., X_{dj})'$ , let X be the  $d \times n$  data matrix  $X_{ij}$  for i = 1, ..., d and j = 1, ..., n, so that  $X_j$  is the jth column of X. Let  $P_n := \frac{1}{n} \sum_{j=1}^n \delta_{X_j} \in \mathcal{P}_{n,d}$ . Then  $m(P_n)$  is a function of X, say  $m(P_n) \equiv M(X)$ . Let B be any  $d \times d$  matrix. Then the data matrix for  $BX_1, ..., BX_n$  is  $BX_j$ , i.e. the jth column of BX is  $BX_j$ , so

$$M(BX) = m(P_n \circ B^{-1}) = Bm(P_n) = BM(X)$$

by singular affine equivariance.

Some special choices of B will be made. First, for each u=1,...,d, let  $B_{ir}^{(u)}=0$  if  $i\geq 2$  or if i=1 and  $r\neq u$ , with  $B_{1u}^{(u)}:=1$ . Let  $X^{(u)}$  denote the uth row of X, so that  $(X^{(u)})_j\equiv X_{uj}$  for j=1,...,n. For any  $1\times n$  vector V, let  $\tilde{V}$  be the  $d\times n$  matrix whose first row is V and whose other rows are all 0's. Then  $B^{(u)}X=\tilde{X}^{(u)}$ , so

$$M(\tilde{X}^{(u)}) = M(B^{(u)}X) = B^{(u)}M(X) = (M_u(X), 0, ..., 0)',$$

where  $M(X) = (M_1(X), ..., M_d(X))'$ . Thus

$$(1) M_1(\tilde{X}^{(u)}) \equiv M_u(X).$$

Next, for any real numbers a and b, define a  $d \times d$  matrix  $B^{a,b}$  by  $B_{11}^{a,b} := a$ ,  $B_{12}^{a,b} := b$ , and  $B_{ij}^{a,b} := 0$  for all other i and j, i.e. for  $i \ge 2$  or  $j \ge 3$ . Then  $B^{a,b}X = (aX^{(1)} + bX^{(2)})^{\sim}$ , so

(2) 
$$M([aX^{(1)} + bX^{(2)}]^{\sim}) = M(B^{a,b}X) = B^{a,b}M(X) = (aM_1(X) + bM_2(X), 0, ..., 0)'.$$

By (1),  $M_1(X) = M_1(\tilde{X}^{(1)})$  and  $M_2(X) = M_1(\tilde{X}^{(2)})$ . Equating first components in (2) gives

 $aM_1(\tilde{X}^{(1)}) + bM_1(\tilde{X}^{(2)}) = M_1(a\tilde{X}^{(1)} + b\tilde{X}^{(2)}).$ 

For any (row vector  $(y \in \mathbb{R}^n)$ , we have a map  $y \mapsto L(y) := M_1(\tilde{y})$  which is linear since  $X^{(1)}$  and  $X^{(2)}$  can be any two  $1 \times n$  vectors and a, b any two real numbers. Thus  $M_1(\tilde{y}) \equiv yz$  for some column vector  $z \in \mathbb{R}^n$ .

Now for any data matrix X, we have by (1)

$$M(X) = (M_1(X), ..., M_d(X))' = (M_1(\tilde{X}^{(1)}), ..., M_1(\tilde{X}^{(d)}))'$$
$$= (X^{(1)}z, ..., X^{(d)}z)' = Xz.$$

Next, any permutation of the columns  $X_j$  of X gives the same  $P_n$  and thus the same  $M(X) = m(P_n)$ , so the components of z are all equal,  $z = (z_1, ..., z_1)'$ . Thus  $M(X) \equiv nz_1\overline{X}$ .

Now suppose all  $X_j$  equal some  $v \neq 0$  and let  $Ax \equiv 2x - v$ . Then Av = v, so  $M(AX) = M(X) = nz_1v = AM(X) = 2nz_1v - v$ . It follows that  $z_1 = 1/n$  and  $M(X) \equiv \overline{X}$ , proving the theorem.

**Remarks**. If an affinely invariant location functional m is defined on all of  $\mathcal{P}_{n,d}$  and M is continuous as a function of  $X_1, ..., X_n$ , then m must be singularly affine equivariant and so is equal to  $\overline{X}$ .

Recall that a sequence  $Q_n$  of probability measures is said to converge weakly to  $Q_0$  if  $\int f dQ_n \to \int f dQ_0$  for every bounded continuous function f. (This form of convergence is used in the central limit theorem, for example.) Let  $Q_n = (n-1)\delta_0/n + \delta_n/n$ . Suppose m is an affinely equivariant location functional defined on  $\mathcal{P}_{n,d}$  for all n for a given  $d \geq 2$  and that m is continuous for weak convergence. Then it is continuous in  $X_1, ..., X_n$  for fixed n, so it is singularly affine equivariant, and by Obenchain's theorem,  $m(Q_n) = \int x dQ_n = 1$ 

for all n. But  $Q_n$  converge weakly to  $\delta_0$ , for which  $m(\delta_0) = 0$ , contradicting the weak continuity, so no such m exists.

**Note**. The theorem is essentially contained in the statement and proof of Obenchain (1971, Lemma 1).

## REFERENCE

Obenchain, R. L. (1971). Multivariate procedures invariant under linear transformations. *Ann. Math. Statist.* **42**, 1569-1578.

---

Combining the run and Mann-Whitney-Wilcoxon tests

If two tests of the same hypothesis  $H_0$  are done at level  $\alpha$ , and just one of the tests rejects  $H_0$ , then by a simple Bonferroni correction we could say  $H_0$  is rejected at level  $2\alpha$ . If the two test statistics are independent under  $H_0$ , then the precise level is  $2\alpha - \alpha^2$ , which is close to  $2\alpha$  since  $\alpha$  is small.

For the test (called the MWW test) based on the Wilcoxon two-sample rank-sum statistic  $W_{RS}$  and the run(s) test based on the number R of runs in the combined sample, R and  $W_{RS}$  are not independent. Here  $W_{RS}$  is the sum of the ranks of the n Y's in the combined sample and there are m X's. Then R has its smallest possible value 2 if and only if  $W_{RS}$  has either its smallest possible value n(n+1)/2 or its largest possible value [(m+n)(m+n+1)-m(m+1)]/2. For other values, there is dependence although not as strong. Odd values of R tend to make  $W_{RS}$  closer to its mean and even values tend to make it farther away as seen especially for R=2.

A combined test will be described which is the run test supplemented by the MWW test, to avoid the Bonferroni correction and keep level  $\alpha$ , while also keeping the main advantages of both the runs and MWW tests.

Recall that the run test rejects the hypotheses  $H_0$  that the  $X_i$  and  $Y_j$  are all i.i.d. with the same continuous distribution F = G, for small values of R. Let  $P_0$  denote probabilities and  $E_0$  expectations, assuming  $H_0$  is true. For given m, n, and  $\alpha$  with  $0 < \alpha < 1$  (for definiteness,  $\alpha = 0.05$ ), let  $r_0$  be the borderline value of R for the runs test at level  $\alpha$ , in the sense that  $P_0(R < r_0) < \alpha \le P_0(R \le r_0)$ . If  $R < r_0$ , or in the special case that both  $R = r_0$  and  $\alpha = P_0(R \le r_0)$ , we will reject  $H_0$  by the runs test at level  $\alpha$ . If  $H_0$  is rejected, we can then apply the two-sided MWW test just to decide whether the data give evidence for a location alternative, with the X's tending to be less than the Y's or vice versa. If the MWW test would not have rejected  $H_0$ , and if R is odd, especially if R = 3, we can decide that whichever variables (X's or Y's) are in the first and last runs are more dispersed than the others (Y's or X's, respectively).

If  $R > r_0$ ,  $H_0$  is not rejected by the runs or combined test.

The remaining case is where  $R = r_0$ , the borderline value, and  $\alpha < P_0(R \le r_0)$ . For example, if m = n = 6, we have

$$P_0(R \le 3) = 0.0130 < 0.05 < P_0(R \le 4) = 0.0671.$$

The run statistic R has only 11 possible values in this case, in general 2n-1 if m=n or  $2\min(m,n)$  otherwise.  $W_{RS}$  has mn+1 possible values. So R is coarse-grained with large atoms of probability, as just seen with the rather big atom  $P_0(R=4)=0.052$ . We can break such atoms into finer parts and get test levels closer to  $\alpha$  using the MWW test.

If  $R = r_0$ , the combined test being defined here calls for next doing an MWW test. Let w be the observed value of  $W_{RS}$ . Let  $\mu = E_0 W_{RS} = n(m+n+1)/2$ . The combined test will reject  $H_0$  if  $R = r_0$  and

$$P(m, n, w | r_0) \equiv P_0 (|W_{RS} - \mu| \ge |w - \mu| | R = r_0) \le (\alpha - P_0(R < r_0)) / P(R = r_0).$$

If w is not far enough from  $\mu$  for the above inequality to hold, then  $H_0$  is not rejected when  $R = r_0$ . The resulting combined test has level between  $P(R < r_0)$  and  $\alpha$  and is usually much closer to  $\alpha$  than  $P(R < r_0)$  is.

The conditional probabilities  $P(m,n,w|r_0)$ , as functions of four variables, would need to be found by a computer as needed. The unconditional probabilities  $P(m,n,w) = P_0(|W_{RS} - \mu| \ge |w - \mu|)$  are available from tables for some w and existing computer packages for general w. The upper bound  $P(m,n,w|r_0) \le P(m,n,w)/P(R=r_0)$  may be helpful: we can reject  $H_0$  if  $P(m,n,w) \le \alpha - P_0(R < r_0)$ .

In the example with m=n=6,  $\alpha=0.05$ , and  $r_0=4$ ,  $H_0$  will be rejected if R=4 and  $|w-\mu| \geq 8$ , as found by hand calculation. Here  $\mu=39$ . The resulting combined test will have level quite close to  $\alpha$ . About alternatives, the (unconditional) two-sided MWW test for m=n=6 will reject  $H_0$  at level  $\alpha=0.05$  only if  $|w-39| \geq 13$ . If that happens we can decide for a location alternative when R=4. Otherwise, if R=4 and  $8 \leq |w-39| < 13$ , we reject  $H_0$  without specifying a type of alternative, because we've done it with the runs and MWW tests combined, not with either one separately.
