6.006 pre-requisite:

Data structures such as heaps, trees, graphs
Algorithms for sorting, shortest paths,
graph search, dynamic programming

Jeveral modules:

Divide & longuer - FFT, randomized algs Ophmization - greedy, dynamic prog Intractability (and dealing with it) Sublinear algorithms, approximation algs Advanced topics

Read course information 7 objectives on Stellar Read course information for 6.046 (if you haven't and forta section already)

Register on stellar forta section already)

Pay particular attention to course collaboration policy!

PCNP

but is P=NP?

Very similar problems can have very different complexity.

Recall: P: class of problems solvable in polynomial time. O(nk) for some constant k Shortest paths in a graph O(v2) e.g.

NP: class of problems verifiable in polynomial time.

Hamiltonian cycle a directed graph

G(V,E) is a simple cycle that contains

pach vorters in 1/

Determining whether a graph has a Determining whether a graph has a hamiltonian is easy. Verifying that a cycle is hamiltonian is easy.

NP-complete: problem is in NP and is as hard as any problem in NP. If any NPC problem can be solved in poly time, then every problem in NP has a poly time solution.

```
Resources & requests
Requests 1,..., n, single resource
   Sli) start time, fli) finish time Sli) < fli)
Two requests i & j are compatible if
 they don't overlap, i.e., fli) < s(j)
  or fly) < s(i)
      3 compatible requests
hoal: select a compatible subset of maximum size.
```

Claim: We can solve this using a greedy algorithm.

A greedy algorithm is a myopic algorithm that processes the input algorithm that processes the input one piece at a time with no apparent look shead

- 1. Use a simple rule to select a request i.
- 2. Reject all requests incompatible with i.
  3. Repeat until all requests are processed.

Possible rules?

1. Select request that starts earliest, i.e., minimum S(i)

let me I II I earliest.

- 2. Select request that is smallest, i.e., minimum f(i) - s(i)
- 3. For each request find # incompatibles. Select the one with minimum # incompatibles.

bad selection!

4. Select request with earliest finish time, i.e., minimum f(i)

Claim: Greedy algorithm outputs a list of intervals  $(\langle S(ii), f(i_1) \rangle, \langle S(i_2), f(i_2) \rangle, ..., \langle S(i_R), f(i_R) \rangle)$ such that  $S(i_1) < f(i_1) < S(i_2) < f(i_2) ... < S(i_R) < f(i_R)$ 

Proof: If f(ij) > S(ij+1) interval j+1 j
Intersect. Contradicts Step 2 of algorithm.

Claim: Given list of intervals L, greedy algorithm with earliest finish time produces kx intervals, where kx is optimal.

Proof: Induction on ko Base case: k==1. Any interval works. Suppose claim holds for k' and we are given a list of intervals whose optimal schedule has k'+1 intervals, namely

 $S^* [1, 2, ..., k^* + 1] = \langle s(j_1), f(j_2), ..., \langle s(j_{k^*+1}), f(j_{k^*+1}) \rangle$ 

```
Say that S[1,...k] = (S(i_1)_2 f(i_2)), ... (S(i_k)_3 f(i_k))
     is what the greedy algorithm gives.
 By construction f(i_1) \leq f(i_1) \leftarrow \text{earliest finish time}
(reste schedule (this is valid!)
      S^{**} = \langle S(i_1), f(i_1) \rangle, \langle S(j_2), f(j_2) \rangle, \dots \langle S(j_{k^*+1}), f(j_{k^*+1}) \rangle
     This is also optimal.
Define L' = set of intervals with s(i) > f(i1)
 Since 5xx is optimal for L. 5xx [2, ..., k'+1] is
   optimal for L'.
 00 optimal schedule for L'has k' size.
By inductive hypothesis, running greedy algorithm on L' should produce a schedule of size k,
 By construction, running greedy algorithm on L'
gives us S[2,...k]
This means k-1=k' or k=k'+1
    and S[1,..k] is optimal.
```

## Weighted Interval Scheduling

Each request i has weight w(i)

Schedule subset of requests with

maximum weight. | w=1 | w=1 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=3 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=3 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |
| w=1 | w=1 |

## Dynamic Programming

Subproblems are

R\* = { request j ∈ R | S(j) >> x}

If we set x = f(i) then R\* is

The set of requests later than request i

the set of requests later than request

n different subproblems, one for each request

Only heed to solve each subproblem once &

memoize

Try each request i as a possible First

If we pick request as the first request

then remaining requests are Rf(i)

then remaining requests compatible with i that

Note: There may be requests compatible with i that

are not in Rf(i) but we are picking i

are not in Rf(i) but we are going in order

as the first request (i.e., we are going in order

opt(R) = max (wi + opt(Rf(i)))

Running time? O(n2)

Exercise: Use sorting initially & reduce

DP complexity to O(n). Overall

complexity will be O(n logn)

requests 1,...n, s(i), f(i) as before m machine types  $T = \{T_1, ..., T_m\}$ weight of 1 for each request. Q(i)  $\subseteq P$  is set of machines that request i can be serviced on. Maximize the number of jobs that can be scheduled on the m machines. NP of Johs with machine assymments is legal.

(an k ≤ n requests be scheduled? NP-complete Maximum requests should be scheduled. NP-hard.

## Dealing with Intractability

- 1) Approximation algorithms: Guerantee

  1) Within some factor of optimed in poly time.

  2) Pruning heuristics to reduce (possibly exp)

  2) runtime on "real-world" examples

  2) Constitute of "I have a simple of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the
- 3) Greedy or other suboptimal heuristics that work well in practice no guarantees

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Divide & longuer

- Paradigm
  - (onvex Hull
  - Median finding

#### Paradigm

Given a problem of Size n

Divide it into a subproblems of size  $\frac{n}{b}$ Rolve each subproblem recursively

Solve each subproblems to

Combine get overall solution

T(n) = a T( $\frac{n}{b}$ ) + [work for merge]

Convex Hull [Ref & 33.3] Given n points in plane S = { (xe yi) | i=1,2,...n} assume no two have same x coord, no two have Same y coord, and no three in a line for convenience (onvex Hull: smallest polygon containing all CH(S) If points are nails, then CH(S) Is shape of rubber band around all the nails CH(S) represented by the sequence of points on the boundary in order clockwise as doubly linked list pengenressent

# Brute force for Convex Hull

Test each line, segment to see if it makes up an edge of the convex hull -> If the rest of the points are on one side of the segment, the segment above is on the convex hull -> else the segment is not --- $O(n^2)$  edges, O(n) tests  $\Rightarrow O(n^3)$  (omplexity Can we do better?

## for Convex Hull DEC Sort points by x roord (once & for all, O(nlogn)) For input set S of points: . Divide into left-half A 1 right half B · (ompute (H(A) t LH(B) halves (mergestep) . (ombine (H's of two halves (mergestep) . by x coords · compute CH(A) { CH(B) HOW TO MERGE? B (a4, b2, b3,a 91 a2 93 upper tangent (ai, bj) lower tangent (ak, bm) (93, b3) L.T.

Cut & park in time  $\theta(n)$  (a1, a2, a3, a4, a5) (b1, b2, b3) ai to bj, go down b list till you see bon and link bon to ax Continue along the a list until you return to ai

```
by minimizes x within (H(A) (a1, a2, ap)
by minimizes x within (H(B) (b), b2, bq)
Assume
     L is the vertical line separating A&B
    Define Y(i,j) as y-wordinate of pt of intersection
                           between L l segment (ai, bj)
CLAIM: (ai, bj) is uppertangent iff if maximizes ylisi)

If y(i,j) is not maximum, there will be points on both sides of (ai, bj) and it can't be a tangent.
Algorithm: Obvious O(n2) algorithm looks at all

ai, bj pairs T(n) = 2T(n/2) + O(n2)

= O(n2)
      J=1 (y(i,j+1) > y(i,j) or y(i-1,j) > y(i,j)):
               if y(i, j+1) > y(i,j): move right finger?

J=J+1 (mod q)
\nelse: i=L-1 (mod p) move left finger)
      return (ai, bj) as upper tangent
```

Similarly for lower tangent T(n) = 2T(=) + O(n) Master Theorem gives O(n/ogn)

# Intuition for why Merge works

ai. bi are right most & leftmost points. We move antidockwise from a, clockwee from bi. ar, .. ag is a convex hall, as is bi, b2, .. by If ai, bj is such that moving from either ai or bj decreases y (isj) there are no points above the (acity) line.

The primal proof is quite involved and won't be covered.

```
Median Finding
[Ref. § 9.3]
 hiven set of n numbers, define rank(x) as number of numbers in the set that are < x
 Find element of rank [n+1]: lower median
                          \lceil \frac{n+1}{2} \rceil: upper median
(or element of rank i)
Clearly sorting works in time of (nlogn)

(an we do better?
Select (S, i) x E S (cleverly) <
       . Compute k= rank(x)
              B= {y es| y <x3
             C= {yes|y>x}
```

• If k=i: return x else if k>i: return select (B,i)\nelse if k < i: return Select (C, i-k)

Need to pick x so rank(x) is not extreme.

- · Arrange S into columns of size 5 (\(\frac{n}{5}\) (ols)

  · Sort each column (big elements on top) (linear time)
- · Find "median of medians" as X

How many elements are guaranteed to be >x?

Half of the M5 groups contribute at least 3 elements >x except for 1 group with less than 5 elements & 1 group that contains x

At least 3 (Mio7-2) elements are > X

Kecurrence:

#### Solving the Recurrence

Master theorem does not apply Prove  $T(n) \leq c \cdot h$  by induction, for Some large enough C  $\frac{TNTVITION:}{5+\frac{7n}{10}} < n$ . True for  $n \leq 140$  by choosing large C•  $T(n) \leq C \cdot \lceil n \rceil 5 \rceil + C \left( \frac{7n}{10} + 6 \right) + q \cdot n$ (a needs to be large enough tocover o(n) term) < \(\frac{\cn}{5} + C + \frac{7nc}{10} + 6c + an\)  $= Cn + \left(\frac{-cn}{10} + 7C + an\right)$ if this is so, we are done C 7 700 +100 0k for n 7, 140 & C 7, 209

# EXAMPLE az, bi is upper tangent ay>than az 92 62 7 61 ai, by is lower tangent az 2 a1 b4 < b3

ai, bj is an upper tangent. Does not mean that ai or bj is the highest point

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

6.046

## Lecture 3

Feb. 12, 2015

TODAY: Fast Fourier Transform (FFT)

- polynomial operations vs. representations
- divide & conquer algorithm
- collapsing samples / roots of unity
- FFT, IFFT, & polynomial multiplication

degree(A)

Polynomial:  $A(x) = a_0 + a_1 x + a_2 x^2 + \cdots + a_{n-1} x^{n-1}$   $= \sum_{k=0}^{n-1} a_k x^k$ 

 $= \langle a_0, a_1, a_2, \dots, a_{n-1} \rangle$  (coefficient)

Operations on polynomials:

- ① evaluation: poly. A(x) & number  $x_0 \Rightarrow A(x_0)$ — Horner's Rule  $\Rightarrow$  O(n) time  $\Rightarrow$   $\Rightarrow$   $\Rightarrow$   $\Rightarrow$   $\Rightarrow$   $\Rightarrow$   $\Rightarrow$   $\Rightarrow$   $\Rightarrow$   $\Rightarrow$
- @ <u>addition</u>: polys.  $A(x) \& B(x) \rightarrow C(x) = A(x) + B(x) \forall x$ - O(n) time: i.e.  $C_k = a_k + b_k$
- (3) <u>multiplication</u>: polys.  $A(x) \& B(x) \rightarrow C(x) = A(x) \cdot B(x)^{tx}$   $- i.e. C_k = \stackrel{k}{\leq} 1$ ,  $a_j b_{k-j}$  for  $0 \leq k \leq 2(n-1)$ j=0 (degree doubles)

| A  | 190V       | ritt          | m<            | T                    | 15]       |            |               |             | R                                      | en         | <i>ک</i> ھ  | ent                 | ati         | ⁄Ω<            |                  |                    |                  |                     |                     |
|----|------------|---------------|---------------|----------------------|-----------|------------|---------------|-------------|----------------------------------------|------------|-------------|---------------------|-------------|----------------|------------------|--------------------|------------------|---------------------|---------------------|
|    |            |               |               |                      |           | $\bigcirc$ | $C\Delta$     | o A         | -<br>Cìe                               | 1-1-       |             | (R)                 | ω··         | ate            | - (              | $\hat{\mathbf{C}}$ | San              | ,n00                | ><                  |
|    | (1)        | 0\ <i>l</i> 0 | 0             | tion                 |           | W          | <u> </u>      |             | 77                                     | 7113       |             | <b>W</b>            | 7           | n)             |                  |                    |                  | Ng                  | $\tilde{\vec{\pi}}$ |
|    | XX         |               | 1.1.          | UIOX                 | 1         |            |               | X           | \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ |            |             |                     |             | 0              |                  |                    |                  | 12                  | رر                  |
|    | (a)<br>(3) | ado           | KI Ti         | $\frac{\delta N}{N}$ | J.        |            |               | 2           | (n)                                    |            |             |                     |             |                |                  |                    |                  | $\langle N \rangle$ |                     |
| 1  | <u></u>    | <u>mu</u>     | <u> Ktip</u>  | Kica                 | TION      |            |               | U           | (Ng                                    |            |             |                     | U           | (n)            |                  |                    | U                | (n)                 | )                   |
| _  |            |               | Λ             |                      | 1         | 1          | 1             |             | 7                                      | 00         |             | 0                   | Λ           | ,              |                  |                    |                  | 1                   |                     |
| 10 | DAY        | <b>/:</b>     | alı           | MOS                  | ST.       | be         | st            | ot          | C                                      |            | W           | orl                 | ds          | Ł              | y                | co                 | nve              | erti                | ing                 |
|    | DA         |               | $\alpha$      | ef                   | fic       | iev        | its           | 4           | <b>⇒</b> ,                             | Sav        | npl         | es                  | ìv          | ι (            | )(n              | ولي                | n                | y ti                | ime                 |
|    |            |               |               |                      |           |            |               |             |                                        |            |             |                     |             | ,              |                  |                    |                  |                     |                     |
| M  | latr       | ìχ            | Vie           | 2ω:                  |           | 1          | XD            | X           | 9                                      |            | X           | \-1 \<br>\-1<br>\-1 | $\setminus$ | ao             |                  |                    | / Y              | \                   |                     |
|    |            |               |               |                      |           | 1          | <b>X</b> 1    | X           | <b>2</b>                               | • • •      | X           | 1-1                 | M           | Q <sub>1</sub> |                  |                    | y:               | 1                   |                     |
|    |            |               |               |                      |           | 1          | ×a            | メ           | 3                                      | • • •      | X           | <u>_</u> 1          | -           | a              |                  | =                  | J:               |                     |                     |
|    |            |               |               |                      |           | :          | :             | :           | •                                      | <b>`</b> . |             | 1                   | <i> </i>    |                |                  |                    | :                | P                   |                     |
|    |            |               |               |                      |           | 1          | Χ.,           | _4 X        | <u>a</u>                               | •••        | <b>ス</b> ,  | ^1<br>^-1           | / \         | $a_n$          | _1 /             |                    | \y               | 1-1/                |                     |
|    |            |               |               |                      | 7         | 11-        | 0.            |             |                                        |            | T           |                     | ٧.          | .,             | _                | $\chi_{j}^{k}$     |                  |                     |                     |
|    | -          | C             | $\mathcal{L}$ | 7                    |           | Va         |               | 21 771      | ono                                    | e v        | Mail<br>Lin |                     | V •         | +              | K -              | ار م               | luci<br>je<br>y. | + \                 | Ι. Δ                |
|    |            | C0(           | 719           |                      | ラノ<br>、マ( | im         | DXE.          | 5 4         |                                        | EVA        | LuA         | X —<br>TIO/         | n<br>NGC    |                | t                | <b>1</b> 00        | luc              |                     | 1.1                 |
|    |            |               |               | )(N                  | )         |            | $\mathcal{C}$ | E           |                                        | IN         | TERI        | POLA                | TZO         | T<br>V         | _                | Λ                  |                  | 11                  | V                   |
|    |            | Sa            | mp!           | les                  | -><br>->  | cos        | 77.           | ~ ·         |                                        | mo         | Tri         | X - '               | vec         | JOV            | Γ Σ              | SOKI               | æ                | V                   | 20.0                |
|    |            |               | - (           | )(N                  | رد        | Vi         | a             | <b>5</b> a  | us                                     | Sìa        | n !         | eli                 | min         | ati            | on               | . , –1             | N.               | Mai                 | ISCORD              |
|    |            |               | - C           | )(n°                 | ۲)        | Vic        | ) I           | ma          | tri)                                   | (-V        | ect         | or                  | pro         | sdu            | ct               | ν.                 | · )              | = /-\               |                     |
|    |            |               |               |                      |           |            |               |             |                                        |            |             | bie                 | LCON        | YPV            | ue               | 4                  |                  |                     |                     |
|    | _          | to            | do            | be                   | elle      | r +        | har           | $\iota \in$ | )(n                                    | 3),        | C           | k                   | Wì.         |                | C                | hoc                | se               |                     |                     |
|    |            | St            | ec)           | ial                  | V         | Qu         | es            | 4           | )<br>0                                 | X          | 0 1         | $x_1$ .             |             | ٠ ٩ ،          | X <sub>n</sub> . | -1                 |                  |                     |                     |
|    |            | ı             | (             | 50                   | fo        | v 1        | Ne            | ve.         | 9                                      | nles       | Ω<          | SUN                 | ne          | 1 +            | hec              | 1 m                | di               | stin                | ct                  |
|    |            |               |               |                      |           |            |               |             |                                        | 0          |             |                     |             |                | Ü                |                    |                  |                     |                     |
|    |            |               |               |                      |           |            |               |             |                                        |            |             |                     |             |                |                  |                    |                  |                     |                     |

Divide & conquer algorithm: A(x) for  $x \in X$ (1) divide into even & odd coefficients:  $A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A = 1 \\ A = 1 \end{cases} \\ A = \begin{cases} A =$  $T(n,|X|) = 2 \cdot T(n/2,|X|) + O(n+|X|)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $= O(n^2)$   $\Rightarrow T(n) = 2 \cdot T(n/2) + O(n)$   $= O(n \lg n) :$ Constructing collapsing sets via  $\sqrt{s}$ :

O {1} 
Cony nonzero starting number) 1 = 1 - 1 2 = 1 - 1 3 = 1 - 1 4 = 2 = 1Complex numbers!

Solve  $(p+qi)^2 = i$ 

```
Inverse Fourier Transform = A^* \rightarrow V^{-1}. A^*
- in fact V^{-1} = \overline{V/n} (p+qi = p-qi)
                           i.e. P = V \cdot \overline{V} = n \cdot \overline{I}
           - \underset{=}{\text{proof:}} P_{jk} = (\text{row } j \text{ of } V) \cdot (\text{col.} k \text{ of } \overline{V})
= \underset{=}{\text{vi}} \text{ it } mk/n
= \underset{=}{\text{vi}} \text{ eit } jm/n \cdot e^{-itmk/n}
= \underset{=}{\text{vi}} \text{ eit } m(j-k)/n
= \underset{=}{\text{vi}} \text{ eit } m(j-k)/n
                   -if j=k: p_{jk} = \sum_{m=0}^{n-1} 1 = n
                  - if j=k: p_{jk} = m=0 - n

- else: geometric series: (e^{iT(j-k)/n})^n - 1

p_{jk} = \sum_{m=0}^{n-1} (e^{iT(j-k)/n})^m = (e^{iT(j-k)/n} - 1)^m - 0
            - so IDFT = A -> V.A for xk = e-iTk/n
            - IFFT algorithm analogous
Fast polynomial multiplication: C(x)=A(x)·B(x)
      - A* = FFT(A)
      -B^* = PFT(B)
     -c_{k}^{*} = a_{k}^{*} \cdot b_{k}^{*} for k = 0, 1, ..., n-1

-C = IFFT(C^{*})
```

Application: Fourier (frequency) space — A\* is complex  $-|a_k^*| = amplitude of frequency - k signal$  $-arg(a_k^*) = angle(a_k^*) = phase shift$ Example: sound [Adobe Audition, Audacity, etc]
- high-pass filter = zero out high frequencies
- low - - - low - - - pitch shift = shift frequency vector
- used in MP3 compression etc. 6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 6.046                                                                                                         | Lecture 4                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Feb. 19, 2015                                                                                  |
|---------------------------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------------|
| TODAY: van Emde Boas [Peter, 1974] - series of improved data structures                                       |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |                                                                                                |
| - Series of<br>- Inserta                                                                                      | Successor                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | based on Personal                                                                              |
| — Delete<br>— space                                                                                           |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | Communication with Michael Bender, 2001                                                        |
|                                                                                                               |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | ng 80,1,,u-13                                                                                  |
| Subject 500                                                                                                   | to Insert. De                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | lete, Successor                                                                                |
|                                                                                                               |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |                                                                                                |
| -if u=n - exponent                                                                                            | or no then tally faster than                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   | O(lg lg n) time/op.!<br>balanced search trees                                                  |
| - cooler o                                                                                                    | jueries than hash                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | balanced search trees<br>ring<br>tables ( $u=2^{3a}$ in IPvy)<br>s $\rightarrow$ port to send} |
| = { range                                                                                                     | of IP addresse                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 | $s \rightarrow port to send$                                                                   |
| Where might C                                                                                                 | )(lg lg u) bound av                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | rise?                                                                                          |
| - binary se<br>- recurrenc                                                                                    | over ly u es: T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T(ly u) = T( | elements $\frac{4}{2} + O(1)$                                                                  |
|                                                                                                               |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |                                                                                                |
| We'll develop van Emde Boas data structure<br>by a series of improvements on a very<br>simple data structure: |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |                                                                                                |
| simple data st                                                                                                | ructure:                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |                                                                                                |

```
(3) Recurse: 3 ops. in Successor are recursive Successors!
    - V. cluster[i] = size-Ju van Emde Boas a O\ic\Ju
    - V. summary = size-Jú van Emde Boas
    - V. Summary [i] = is V. cluster [i] nonempty?
                                                 co c1 - - 0
   Insert(V_x):
                                                 T(vu)
       Insert (V.cluster[high(x)], low(x))
       Insert (V. summary, high(x))
                                                 T(Vu)
     \Rightarrow T(u) = 2T(Ju) + O(1)
        T'(lgu) = 2T'(lgu) + O(1)
= O(lgu)
   Successor (V_{\lambda} \chi):
       i = high(x)
       j = Successor (V. cluster [i]. low(x))
                                                        T(Vu)
       if j=\infty:
            i = Successor (V. summary. i)
j = Successor (V. cluster [i]. -00)
                                                       Tou
                                                        T(Ju)
       return index(i,j)
     \Rightarrow T(u) = 3T(u) + O(1)
        T'(lgu) = 3T'(lgu) + O(1)
                = O((lg u)^{lg 3})
= O(lg^{1.585} u) 7:
      need to reduce to one recursion!
```

```
(4) Maintain min & max of every structure:
-0(1) overhead in Insert: if x<V.min: V.min=x
                                               if x > V.max: V.max = x
     Successor (V, x):
          i = high(x)
          if low(x) < V. cluster[i]. max:
                   j=Successor(V.cluster[i], low(x))
          else: i = Successor (V. summary, high(x))
                  j = V.cluster[i].min
          return index(i.j)
       \Rightarrow T(u) = T(\sqrt{u}) + O(1)
= O(\lg \lg u)
5 Don't store min recursively:
- Successor checks for min specially:\nif x < V.min: return V.min
     Insert(V.x): rempty case costs O(1) < if V.min = None: V.min = V.max = x: returns
          if x < V.min: Swap x > V.min
          if x > V. max: V. max = x
     if V. cluster [high(x)]. min = None: (previously)

Insert (V. summary, high(x)) *

Insert (V. cluster [high(x)], low(x))

* if both calls, then second costs O(1) (empty)

=> 17117 = NO. 0. 1.
           => T(u) = O(lglg u) =
```

| (7) Space: improve from current O(u) to O(n lglg u)                                                                              |
|----------------------------------------------------------------------------------------------------------------------------------|
| - only create nonempty clusters                                                                                                  |
| -if Vinin becomes None, deallocate V                                                                                             |
| - Vicluster = hashtable of nonempty clusters                                                                                     |
| (recall from 6.006; and see Lecture 8)                                                                                           |
| - insert may create new structure (fill min)                                                                                     |
| alla la us times (each empty insert)                                                                                             |
| - can really happen [Vladimir Cunat]                                                                                             |
| - charge pointer to structure (and associated                                                                                    |
| - can really happen [Vladimir Cunát] - charge pointer to structure (and associated hash-table cell) to the structure             |
| ⇒ O(n lg lg u) space (but randomized)                                                                                            |
|                                                                                                                                  |
| CHARGING AMORTIZATION ~                                                                                                          |
| SEE NEXT LECTURE (5)                                                                                                             |
|                                                                                                                                  |
| 1 Indirection further reduces to O(n) space                                                                                      |
| - store VEB structure with n=0(ggu)                                                                                              |
| using BST or even array  ⇒ O(lg lg n) time once in base case  - O(^/lglg u) such structures (disjoint)                           |
| => O(lg lg n) time once in base case                                                                                             |
| - U(1/lglg u) such structures (disjoint)                                                                                         |
| $\Rightarrow O(\frac{n}{\lg \lg u} \cdot \lg \lg u) = O(n)$ Space for small                                                      |
|                                                                                                                                  |
| - larger structures store pointers to them                                                                                       |
| - larger structures "store" pointers to them $\Rightarrow O(\frac{n}{\lg \lg u} \cdot \lg \lg u) = O(n) \text{ Space for large}$ |
|                                                                                                                                  |
| - details: split/merge small structures                                                                                          |
|                                                                                                                                  |

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

Feb. 24. 2015 6.046 Lecture 5 TODAY: Amortization - aggregate method
- accounting method
- charging method
- potential method différent approaches/ techniques for amortized analysis all related, but one often easier than others - table doubling?
- binary counter > examples of amortized
- 2-3 trees > analysis Powerful technique for data structure analysis - often, what you really care about Recall: table doubling [6.006]

- n elements in table of m slots

- want m = S2(n) for  $1 + \frac{m}{n} = O(1)$  expected performance (with hashing with chaining) - idea: if n grows  $\geq m$ , double m - cost:  $\Theta(m+n) = \Theta(n)$  to build new table  $\Rightarrow pay \Theta(2^0+2^1+2^2+2^3+\cdots+2^{\lceil \lg n \rceil}) = \Theta(n)$ total to resize table over n insertions => 9(1) amortized cost per insertion

| Aga | VP.OII | ate              | . <b>.</b> V | net         | hoo    | <b>Q</b> : |          | 11       | ان        | st       | ade        | J.        | it     | un        | 27      |               |      |     |
|-----|--------|------------------|--------------|-------------|--------|------------|----------|----------|-----------|----------|------------|-----------|--------|-----------|---------|---------------|------|-----|
| Agg | -0     | tot              | al           | C           | 551    | (          | f        | k        | OD        | erc      | atio       | sus       |        | 7         |         |               |      |     |
|     |        |                  |              |             |        |            | K        |          | ·         |          |            |           |        |           |         |               |      |     |
|     | = c    | am               | or           | 517         | ed     | Ci         | st       |          | per       | 0        | per        | cat       | ion    |           |         |               |      |     |
| •   | — C    | OM               | mo           | n C         | My     | 1 +        | Vr       | 51       | mpl       | <u>e</u> | ay         | ali       | 1509   | 5         |         |               |      |     |
| Am  | srt    | ) <del>5</del> i | जि           | le          | )OU    | nd         | 5.       | _        |           |          |            |           | _      |           |         |               |      |     |
|     | as     | Sj               | 9'n          | a           | N      | "a         | mo       | rti.     | 200       |          | C05        | <i>t"</i> | to     | C         | acl     | $\frac{1}{2}$ |      |     |
|     | Op     | ero              | atic         | אל          | ی      | uch        | \ t      | ha       | t         | , e      | res        | ser       | ve     | t         | ota     | L             | •    |     |
|     |        | <u>S</u>         | , au         | mov<br>er   | 71     | 200        | ) (      | cos      | ts        | >        | 2          | ac        | etuc   |           | COS     | 315           |      |     |
|     |        |                  |              |             |        |            |          |          |           |          |            | _         | apı    | eval      | 100     | Seg           | uen  | ce  |
| -   | - 0    | Men              | (y)          | e i         | 5      | jus        | اد<br>ا  | on<br>-2 | e (       | 300      | (D)        | ر<br>رادد | د ۸۱ د | ·         |         |               |      |     |
|     | 6.     | 9,               | 0            | 2n          | X<br>I | 19         | cet      |          | )'<br>)C0 | 200      | ) (<br>) ( | JCV       | roat   | 0<br>0~1  | 2 120 8 | 7             |      |     |
|     |        |                  | 0            | (lg         | N*)    | ) a        | MA       | rti      | ise<br>mh | ۲<br>آ   | xor        | ĵΝ        | SON    | 7         |         | J             |      |     |
|     |        |                  | 0            |             | imo    | srt        | 120      | ed       | De        | <b>1</b> | del        | eto       | 2 (    | )<br>JSS( | rmi     | 19 (          | 2XìS | ts) |
|     | w      | reve             |              | ν*          | = y    | na>        | (im      | um       | \<br>Si   | Ze       | 01         | f s       | set    | at        | an      | y t           | ime  | 2   |
|     | bec    | cau              | 5e,          | C           | C      | reai       | tion     | 15,      | Ĭ         | ĪNS      | sev        | tion      | 154    | d         | ic      | lele          | tion | S   |
|     | cc     | st               | (            | )(c         | ۲ ۲    | (i+        | d)       | lg       | (*N       | =(       | )(         | ンナ        | ily    | g n       | +(      | 8d            |      |     |
|     |        |                  |              | \           | 1.     | 50         | li       | 1        | G.        | . //     |            |           | 1      |           |         |               |      |     |
|     |        |                  | WE           | e'll<br>= c | tì     | ght        | EV       | \        | 0 (       | كرلا     | g n        | 1 (1      | W      | reve      | 2       |               |      |     |
|     |        |                  | <b>/</b> /\  | = C         | ur     | rei        | <u>1</u> | 56       | 1 5       | 120      | 2          | k         | exc    | SW.       |         |               |      |     |
|     |        |                  |              |             |        |            |          |          |           |          |            |           |        |           |         |               |      |     |
|     |        |                  |              |             |        |            |          |          |           |          |            |           |        |           |         |               |      |     |

| Accounting method: "planning ahead for vainy day - allow an operation to store credit (like ban                                                                         | <i>y</i> . |
|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------|------------|
| - allow an operation to store credit (like ban                                                                                                                          | k)         |
| => amortized cost > actual cost                                                                                                                                         |            |
| - allow operations to pay using existing credit                                                                                                                         |            |
| - allow operations to pay using existing credit  amortized cost < actual cost                                                                                           |            |
|                                                                                                                                                                         |            |
| Example: table doubling                                                                                                                                                 |            |
| Example: table doubling  - when inserting an element, add a  coin to it representing c=0(1) work                                                                        |            |
| coin to it representing c=0(1) work                                                                                                                                     |            |
| - when table needs to double n >2n,                                                                                                                                     |            |
| n/2 new elements still with coins                                                                                                                                       |            |
| X clement                                                                                                                                                               |            |
| $\times$ clement $\times \times \times \times \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes \otimes $ |            |
| - use up those coins to pay for O(n) rebui                                                                                                                              | 120        |
|                                                                                                                                                                         |            |
| $\times$ $\times$ $\times$ $\times$ $\times$ $\times$ $\times$                                                                                                          |            |
| -> C(n) - Marc amortized walled cost                                                                                                                                    |            |
| $\Rightarrow \Theta(n) - \frac{n}{2}$ c amortized rebuild cost<br>=0 for large enough c<br>-0(1) + c = $\Theta(1)$ amortized cost per inser                             |            |
| - 0(1) LC - O(1) constituted cost por insort                                                                                                                            | +          |
| O(1) + C = O(1) amor 11 zear cost per inser                                                                                                                             | 1          |
| Counterexample: free deletion in 2-3 trees                                                                                                                              |            |
| counterexample. Thee desertion in a sirres                                                                                                                              |            |
| that of a trace to a family am, deserted                                                                                                                                |            |
| - claim: O(lg n) am. insert. Ø am. delete - attempt: put coin worth O(lg n) on inserted element                                                                         |            |
| on inserted exement                                                                                                                                                     |            |
| - trouble: when deleting that element, n might be bigger => coin worth too litt                                                                                         |            |
| n might be bigger => coin worth too lit                                                                                                                                 | XC.        |
|                                                                                                                                                                         |            |

Charging method: (blaming the past) (not in CLRS)
- allow operations to charge cost retroactively to past operations (not future ops) - amortized cost of op. = actual cost usually > - total charge to past ops.
one or > + total charge by future ops. to this op.\nother Example: table doubling

- when table doubles n -> 2n, charge O(n) cost to 1/2 inserts since last doubling ⇒ each of these elements charged  $\frac{\Theta(n)}{V^2} = \frac{\Theta(1)}{V^2}$ & won't be charged again ⇒  $\Theta(1)$  amortized per insert Example: table doubling & halving motivation: want O(n) space even with deletes - if table down to 1/4 full (n=m/4): shrink to half size (m > m/2) at O(m) cost => still half full after any resize => still ≥ 1/2 inserts to charge to on growth — also ≥ 1/4 deletes to charge to on shrink — each operation charged ≤ once, by ⊖(1) > 9(1) amortized per insert & delete could do this argument with coins instead, but less intuitive (to me) 42 bank accts.

Potential method: (defining karma) - define a potential function of mapping data-structure configuration > nonnegative integer
- intuitively measuring "potential energy"
= potential high costs in the future - equivalent to total unused credit (2 unused coins) stored by all past ops. = bank account balance - nonnegative -> never owe the bank - amortized cost = actual cost + AT = \$ (DS after op.) - \$ (DS before op.) => sum of amortized costs telescopes = sum of actual costs + \$(final DS) - \$\Pi(initial DS) >Ø initial balance so also need to pay  $\Phi(\text{initial DS})$  at start  $\sim$  ideally  $\emptyset$  or O(1)  $\sim$  else another amortization - in accounting method, specify offset (A) between actual cost & amortized cost. which determines total stored value (1) - in potential method, specify total stored value In which determines changes per op:  $\Delta\Phi$  - sometimes one is more intuitive than other - potential method feels most powerful (to me) but also the hardest to come up with proof (1)

| Ex | ample: binary counter 0011010111 incr<br>- operation: increment 0011011000 incr                                                                                                                                                      |                |
|----|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------------|
|    | - operation: increment 0011011000                                                                                                                                                                                                    |                |
|    | - increment costs O(1+ # trailing 1 bits)                                                                                                                                                                                            |                |
|    | so intuition is that 1 bits are bad                                                                                                                                                                                                  |                |
|    | - define $\Phi = c \cdot \# 1$ bits in counter                                                                                                                                                                                       |                |
|    | $\Rightarrow \Delta \Phi$ from increment = c(-#trailing 1 bits +1                                                                                                                                                                    | <u>ヽ</u><br>ーン |
|    | $\Rightarrow$ amortized cost = actual cost $+\Delta \overline{D}$                                                                                                                                                                    |                |
|    | $\Rightarrow$ amortized cost = actual cost $+\Delta\Phi$<br>= $\Theta(1+\# trailing 1 bits) + c(-\# trailing 1 bits + 1$                                                                                                             |                |
|    | = O(1) for c large enough                                                                                                                                                                                                            |                |
|    | =0(1) for c large enough<br>- D(initial DS) = & assuming we start @000-0<br>(necessary for 0(1) amortized bound)                                                                                                                     | <b>)</b>       |
|    | (necessary for O(1) amortized bound)                                                                                                                                                                                                 |                |
|    |                                                                                                                                                                                                                                      |                |
| Ex | ample: insert in 2-3 trees AA                                                                                                                                                                                                        |                |
|    | - O(lg n) splits in worst case                                                                                                                                                                                                       |                |
|    | - but claim only O(1) amortized splits - what causes splits? nodes overflowing                                                                                                                                                       |                |
|    | - what causes splits? nodes overflowing                                                                                                                                                                                              |                |
|    | - () = the world with a children                                                                                                                                                                                                     |                |
|    | $\Rightarrow \land \sigma \leq 1 - \# solits \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad \qquad$                                                   |                |
|    | ⇒ $\Delta\Phi$ ≤ 1 − # splits 3 2 2 add child @top // each split turns $\Phi$ ⇒ amortized # splits = actual #splits + $\Delta\Phi$ ≤ # splits + $(1 - \# \text{splits}) = 1$ .  - $\Phi(\text{initial DS}) = \Phi$ if we start empty |                |
|    | > amortized # solits = actual #solits + NO                                                                                                                                                                                           |                |
|    | $\leq \# \text{ splits} + (1 - \# \text{ splits}) = 1$                                                                                                                                                                               |                |
|    | - O(initial DS) = 0 if we start empty                                                                                                                                                                                                |                |
|    |                                                                                                                                                                                                                                      |                |
|    | In B-trees:  = # nodes with B children                                                                                                                                                                                               | 1              |
|    | In B-trees: $\Phi = \#$ nodes with B children<br>In $(a_nb)$ -trees: $\Phi = \#$ nodes with $b$ children                                                                                                                             | •              |
|    |                                                                                                                                                                                                                                      |                |

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

Randomized Algorithms

- Why randomized?

   Checking Matrix multiply

   Quicksort

Kandomized or Probabilistic Algorithms

- Algorithm that generates a random number r & Eline R3 and makes decisions based on r's value.
- On the same input on different executions randomized algorithm may number of steps

  run or a different number of steps

  produce different outputs

Monte Carlo

. runs in polytime always

· prob (output is correct) > high

Las Vegas

· always produces correct output poly time

Variation due to ~

C = A x B

Simple algorithm: O(n3) multiplications Grassen: Multiply two 2 x 2 matrices using nultiplications: 0(n2.81) log 27 Copporsmith-Winograd: O(n2.376)

Matrix Product Checker

hiven nxn matrices A, B, C or not?
Goal: check of A x B = C or not?

Question: Can we do better than multiply?

We will see an O(n2) algorithm that: If AxB = C, then prob [output = YES] = 1

If AxB = C, then prob [output = YES] < 1/2

We will assume entired in matrices & {0,13.

Choose a random binary vector r[...n]

Such that Pr[ri=1] = 1/2 independently

for i=1,...n If A(Br) = Cr, then output 'YES', else output 'NO'

O(n2) time, since 3 matrix vector multiplications for Br, A(Br). Cr Observations:

If AB=C, then A(Br)=(AB)r=Cr and algorithm always outputs YES.

Analyzing Correctness if AB + C Claim: If AB + C, Hen Prob[ABr + Cr] 7 1/2

Let D = AB - C. Our hypothesis is thus that  $Dr \neq 0$   $D \neq 0$ , Clearly, there exists r such that  $Dr \neq 0$ D = 0. (10.), that there are many r such we need to show that there are many r such that Dr = 0. [Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly specifically, Prob[Dr = 0] > 1/2 for a randomly

Analyzing Correctness (contd.) If Dr +0, we would output 'No', done Dr = 0 case ∃i,j s.t. dij ≠ 0 D= AB-C +0 > i Fix vector v which is 0 in all coordinates except for i=1 $(DV)_i = dij \neq 0$  implying  $DV \neq 0$ Take any r that can be chosen by our algo. We are looking at the case where Dr = 0. except [ = ([+V])
\nexcept [ = ([+V]) r'= r+V vector addition  $\mathfrak{D}r' = \mathfrak{D}(r+v) = 0 + \mathfrak{D}v \neq 0$ r to r' is 1 to 1 because if r'= r+V, then r=r" > Number of r for which Dr=0 Number of r/for which Dr' \$0 Pr[Dr \$0] >, 1/2

## Quicksort

C.A.R. Hoare (1962)

Divide & longuer algorithm but work mostly in divide step rather than combine Sorts "In place" like insertion sort and unlike merge sort = required o(n) auxiliary space

Different variants:

Basic: good in overage cese (for a random input)
Median-based probing: uses median finding Rand-mized: good for all imputs in expectation
Las Vegas algorithm

ducksort

n-element array A

Divide:

1. Pick a pivot element x in A Partition the array into sub-arrays

<\* x > x

Conquer: Recursively sort subarrays L and Go Combine: Trivial

pivot x = A[1] or A[n], first or last element - Remove, in turn, each element y from A and

- Insert y into L, E or G depending on
- the comparison with pivot x
- Each insertion and removal takes of) time
- Partition step takes O(n) time
- To do this in place: see code in CLRS

- Input sorted or reverse sorted
- Partition around min or max elements
- One side L or G1 has n-1 elements, other o

One side 
$$L$$
 or  $O(n-1)$  +  $O(n)$   
 $T(n) = T(0) + T(n-1) + O(n)$  divide step  
 $= O(1) + T(n-1) + O(n)$   
 $= T(n-1) + O(n)$   
 $= T(n-1) + O(n)$   
 $= O(n)$  (arithmetic series)  
 $= O(n)$  (arithmetic in practice)  
Does well on random inputs in practice

Prot Selection Using Median Finding

(an guarantee balanced L and G using rank/median selection algorithm that runs in O(n) time

$$T(n) = 2T(\frac{n}{2}) + \theta(n) + \theta(n)$$

Tecursive median selection divi

recursive median selection divide

T(n) = 
$$\beta(n \log n)$$
This algorithm is slow in practice and loses mergesort.

## Randomized Quicksort

(5)

X is chosen at random from array A (at each recursion, a random choice is made)

Expected time is O(nlogn) for all input arrays A

See CLRS p181-4 for analysis; we will analyze here a variant quicksort

"Paranoid" Quicksort

Repeat

choose pivot to be random element of A

Perform Partition

Until resulting partition is such that

Until < 3 | A| and | a| < 3 | A|

L| < 3 | A| and | a| < 4 | A|

Recurse on L and G7

## "Paranoid" Ancksort Analysis

Let T(n) be an upper bound on the expected running time on any array of n size

T(n) comprises:

- · Time needed to sort left subarray
- . Time needed to sort right subarray
- . The number of iterations to get a good call \* C.N cost of partition

$$T(n) \leq \max_{\substack{n | 4 \leq i \leq 3 | 4^n \\ n | 4 \leq i \leq 3 | 4^n \\ = T(\frac{n}{4}) + T(\frac{3n}{4}) + 2cn}} (T(i) + T(n-i)) + E(\# | 1 + erations)$$

$$E(\# | 1 + erations) \leq 2 \quad since prob of good call$$

$$= T(\frac{n}{4}) + T(\frac{3n}{4}) + 2cn$$

$$= T(\frac{n}{4}) + T(\frac{3n}{4}) + 2cn$$

$$= 2cn$$

$$2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

$$\frac{3}{16} \cdot 2cn$$

2 ch work at each level

max log 4 (2cn) levels

O(n logn) expected runtime.

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## SkipLists

William Pugh (1989)

- Easy to implement (as compared to balanced
- Maintains a dynamic set of n elements in O (log n) time per operation in expectation and with high probability (w.h.p.)

One Linked List.

One (Sorted) linked list

14× 23× 34× 42 × 50 × 59 × 66 × 72× 79 Searches take O(n) time in worst case

Suppose we had two sorted linked lists
- each element can appear in one
or both lists

### Two Linked Lists

Express and local subway lines (à la New York City 7th Avenue Line)

- · Express line connects a few of the stations · Local line connects all stations
- · Links between lines at common stations

14 > 34 42 42

Searching in Two Linked Lists

Search (x):

- . Walk right in top linked list (4) until going right would go too far
- · Walk down to bottom linked list (Lz)
- . Walk right in Lz until element found (or not)

Search (59)

# Searching in Ign Linked Lists

## Insert (x)

To insert an element x into a skip list · Search(x), to see where x fits into

- . Always insert into bottom list
  - . Insert into some of the lists above which ones?
  - if HEADS: promate x to next level up )\nelse stop · Flip fair com

Warmup Lemma: # levels In n-element
skip list is O(lgn) w.h.p.

c.lgn

related

related

Proof: Failure probability (not < clg n levels)

= Pr { > clgn levels}

= Pr { some element got promoted > clg n times}

= Pr { some element x got promoted > clgn times}

< n. Pr { element x got promoted > clgn times}

= n. (1/2) clgn

= n. (1/2) clgn

 $= \frac{1}{h^{c-1}} = \frac{1}{h^{d}} \quad \forall = c-1$ 

Look at < 1 arrows on page 4

#### Proof of theorem

- backwards - Search makes "up" and "left" moves each with probability 1/2
- Number of moves going "up" < # levels < c.lgn w.h.p. (by Warmup Lemma)
- Total number of moves = number of coin flips until you get a lgn heads ("up" moves)

Number of coin flips until clgn heads = O(lgn) w.h.p.

Theorem: Let Y be a random variable representing the total number of heads in a series of m independent coin flips, where each flip has a probability p of coming up heads. Ther for all r > 0, we have Pr[Y7/E[Y]+r] < e-2r2

Lemma: For any c, there is a constant d

Lemma: For any c, there is a constant d

such that with high probability (w.h.p.) the

number of heads in flipping d lgn fair coins

humber is at least c-lgn. This is our claim

from page 7. Let Y be the number of tails when fires - p=1/2  $m = d \lg n$ , so  $E[Y] = \frac{1}{2}m = \frac{d \lg n}{2}$ We want to bound the probability of fewer than < c. lg n heads = the probability of getting of least > d. lgn - clgn tails.

Proof of Lemma (contd.)

Pr [Y >, (d-c) Ign] = Pr [E[Y] + (q-c) Ign]

Choose d= 8c => r=3clgn

By Chernoff, prob of < C. lgn heads

e - 2(3c lg n)2

< e-clgn < 2

(e 72)

= 2 clgn

(1.) for Lemma

event A: number of levels \le c \leq n \times h.p.
\nevent B: number of moves until c. \leq n
\nevent B: \times \times \text{d \leq n} \times h.p.

event A and event B are not independent Want to show Pr (event A & event B) high w.h.p.

Pr (event A & event B) = Pr (event A + event B)

< Pr (event A) + Pr(event B) (union bound)

5 1 + hc

 $= O\left(\frac{1}{h^{c-1}}\right)$ 

Pr (event A & event B) w.h.p.

Search in ollgn) w.h.p. fr theorem.

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 6.046                       | Lecture 8                                  | Mar. 5, 2015                                            |
|-----------------------------|--------------------------------------------|---------------------------------------------------------|
| TODAY: Hashing<br>- review: | 3                                          |                                                         |
| _ diata                     | 000000                                     |                                                         |
| - chai                      | ning<br>ple unitorm<br>hashing<br>(useful) |                                                         |
| - universal                 | le unitorm                                 |                                                         |
| - why                       | (useful)                                   |                                                         |
| - perfect<br>- how          | hashing                                    |                                                         |
| - how                       | (it works)                                 |                                                         |
|                             |                                            |                                                         |
| Dictionary prob             | llem: Abstract                             | Data Type (ADT)                                         |
| subject to                  |                                            | ach with a key.                                         |
| - inse                      | rt (item): add                             | item to set<br>le item from set                         |
| - searc                     | ch (key): return                           | n item with key                                         |
| - assume ite                | ms have distin                             | exists                                                  |
| Cor that in                 | serting new one                            | e clobbers ald)                                         |
| -easier tho                 | an predecessor                             | /successor problem<br>/skip lists (lg n)<br>as (lglg u) |
| & by                        | von Ende Bo                                | as O(glg u)                                             |

Universal hashing:

- choose a random hash function h from H
- require It to be a universal hash family:

Pr { h(k)=h(k')} { } { } { } { } { } { } { } { } { } { now just assuming h is random no assumption about input keys (like Randomized Quicksort) Theorem: for n arbitrary distinct keys
& for random he 74. & 74 universal
E[# keys colliding in a slot] < 1+x

S, 1/m Proof: - consider keys  $k_1, k_2, ..., k_n$  INDICATOR - let  $I_{i,j} = 51$  if  $h(k_i) = h(k_j)$  RANDOM VARIABLE E[# keys hashing to same slot as  $k_i$ ]  $= E[\sum_{j=1}^{k} I_{i,j}]$ = E E [ Ii.j ] = linearity of expectation  $= \underbrace{\sum_{j \neq i}^{-1} E[T_{i,j}]}_{j \neq i} + \underbrace{E[T_{i,i}]}_{j \neq i} + \underbrace{E[T_{i,i}]}_{j \neq i}$   $= \underbrace{Pr\{T_{i,j}=1\}}_{j \neq i} \leftarrow \underbrace{\text{indicator random var.}}_{j \neq i}$   $= \underbrace{Pr\{h(k_j)=h(k_j)\}}_{j \neq i} \leftarrow \underbrace{\text{def. of } T_{i,j}}_{j \neq i}$   $\leq h/m + 1$   $= \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{h/m + 1}_{j \neq i} = \underbrace{$ ⇒ Insert, Deleter Search cost O(1+a) expected.

| Do   | universal hash families exist? YES:                                                                                          |
|------|------------------------------------------------------------------------------------------------------------------------------|
|      | = Fall hash functions                                                                                                        |
|      | hi 20, 1, -, u-13 -> 20, 1, -, n-133 is universal                                                                            |
|      | hut this is usoloss.                                                                                                         |
|      | - storing h takes $lg(m')=ulg m bits >> n$ viust like direct map table (big array)                                           |
|      | vjust like direct map table (big array)                                                                                      |
|      | - would need to precompute u values                                                                                          |
|      | ⇒ $\Omega(u)$ time, possibly $w(\# operations)$                                                                              |
| D 1  |                                                                                                                              |
| 101- | product hash family:                                                                                                         |
| _    | assume in is prime (find nearby prime)                                                                                       |
|      | assume u=mr for integer r (round up else)                                                                                    |
|      | siew keys in base m: k= <konkin-inkr-1></konkin-inkr-1>                                                                      |
|      | for key $a = (a_0, a_1,, a_{r-1})$ define $h_a(k) = (a \cdot k) \mod m$ $= \sum_{i=0}^{r-1} a_i \cdot k_i \mod m$ $= hachet$ |
|      | = file mod m = hachet                                                                                                        |
|      | dot product =0                                                                                                               |
|      | 74= { ha   a = {0,1,, u-1}}                                                                                                  |
|      |                                                                                                                              |
| -    | storing hat 4 requires just storing 1 key, a word RAM model: manipulating O(1) machine words takes O(1) time,                |
| _    | word RAM model: manipulating 8(1)                                                                                            |
|      | machine words takes O(1) time,                                                                                               |
|      | & "objects of interest" (here: keys) fit in a machine word                                                                   |
|      | tit in a machine word                                                                                                        |
|      | computing $h_a(k)$ takes $O(1)$ time $O(\log_m u)$ using just $+2^n \sim can you do better?$                                 |
| 1    | )(Legm u) using just + & ~ can you do belier!                                                                                |
|      |                                                                                                                              |

Theorem: dot-product hash family It is universal Proof: take any two keys  $k \neq k'$   $\Rightarrow$  differ in some digit, say  $k_0 \neq k'_0$ — let not  $d = \{0, 1, \dots, r-1\}, \{d\}$  $Yr \ 2 ha(k) = ha(k')$  $= \Pr_{a} \left\{ \sum_{i=0}^{k} a_i \cdot k_i = \sum_{i=0}^{k} a_i \cdot k_i \pmod{m} \right\}$ = Pr { \subseteq ai \ki + aa \ka = \subseteq ai \ki + aa ka (mod m)} =  $\Pr_{\alpha} \left\{ \sum_{i \neq d} a_i \left( k_i - k_i' \right) + a_d \left( k_d - k_d' \right) = 0 \pmod{m} \right\}$ =  $\Pr \{ a_d = -(k_d - k_d)^{-1} \leq a_i (k_i - k_i) \pmod{m} \}$   $rac{1}{m} \text{ prime} \Rightarrow \mathbb{Z}_m \text{ has multiplicative}$   $rac{1}{m} \text{ prime} \Rightarrow \mathbb{Z}_m \text{ has inverses}$ = E Pr {ad = f(knknanot d)} (because ad is independent) (= 5 Préanot d=x3 Préad=f(k,k,x)3 from anot d = E [ 1/m]
anot d  $= \frac{1}{m}$ Another universal hash family: [CLR5]
- choose prime P > u (once) -  $hab(k) = [(a \cdot k + b) \mod p] \mod m$ -  $94 = \frac{1}{2} hab \mid a, b \in \frac{20}{1}, \dots, u-1\frac{3}{2}$ 

| Stati     | C                           | dic              | tio            | mai       | ry   | P            | orol      | lei   | m:         | C         | jive    | n                 | n            | ke    | 45             |             |          |          |
|-----------|-----------------------------|------------------|----------------|-----------|------|--------------|-----------|-------|------------|-----------|---------|-------------------|--------------|-------|----------------|-------------|----------|----------|
| Stati     | to                          | st               | ore            |           | ろう   | tal          | ole       | 4     | 5U         | (ppi      | ort     | - (               | Se           | arc   | 2h(            | K           | )        |          |
|           |                             | 100              |                | _(/U:     | 2:4  | -            |           |       |            |           |         |                   |              |       |                |             |          |          |
| Perfe     | ect                         | h                | ask            | rīn       | g:   | L            | Fred      | lmo   | in,        | Kon       | Nós     | 5                 | Zen          | veré  | di.            | 198         | 34]      |          |
|           | 1206                        | luni             | SIM            | aV        | hu   | 13O2         | 0 +       | ime   | ) I        | l, h      | b.      | (IA               | 000          | ٠,١   | Uin            | Bal         | $\wedge$ |          |
| _         | 0(                          | 1)               | til            | me        | to   | ór           | S         | car   | ch         | ^         | in      | W                 | 013          | st    | Co             | se          | ha.      | . 4      |
|           | O4                          | ^)               | Spa            | zce       | 1    | ٨            | WC        | 12 V  | (          | as        | e       |                   | ם<br>כ כ     | ha.   | .1             |             | ha.      |          |
| T (       | <b>)</b>                    | $\sim$           |                | )         | Λ    | 1            |           | _     |            | 1         | -       | 1                 | Ø<br>Ø       | 0 4   | al h           | <b>a</b> ,3 |          | _        |
| <u>10</u> | lea:                        | 0                | l-X            | ev        | el   | h            | 05        | nīv   | 19         | V         | 1       |                   | 1<br>3       |       | 1              |             | m        |          |
|           |                             |                  |                |           |      |              |           |       |            |           |         |                   |              |       |                |             | O        | <b>♪</b> |
| (1)       | Pic                         | CK               | h <sub>1</sub> |           |      | ر ۲۷ .       | 20        | U-    | 13         | <i>ار</i> | £0.     | · U               | (            | ~N    | ۷ -            | Lζ          |          |          |
|           | $\mathcal{L}_{\mathcal{L}}$ | om<br>V 1<br>has | W.             | Wi<br>A   | NIVE | 2V.><br>\    | ω<br>G    | N)    | usi        | n t       | am<br>L | TYY.              | 1<br>Cila    | · ^ \ |                |             |          |          |
|           | 70                          |                  | //\_<br>-]     |           | ) 74 | )<br>~~ ~~   | (e        | 9.    | th         | eav       | by      | y Charles         | ( [/)<br>^ @ | 145   | اداد           | ሌ           | h.       |          |
|           |                             | NWS              | )N             |           | - 11 | e,           | U         | W     | 1400       |           | ···     | , , ,             | J            | U.O   | 6              | 7           | 11       |          |
| (2)       | for                         | - 0              | ac             | ا ا       | s Oc | +            | ic        | 50    | 1.1.       |           | m.      | -17               | •            |       |                |             |          |          |
|           | _                           | le               | + (            |           | #    | ite          | ms        | in    | Slo        | sti       | =       | 5 i               | 1            | h(k   | ر. ):<br>در از | _ c<br>_ 1  | }1       |          |
|           | _                           | Pic              | k              | h         |      | : 4          | 0, 1      | L, -  |            | u-        | 13.     | _> :              | ίO.          | 1,.   | · - • •        | m           | 5        |          |
|           |                             | fro              | m              | 0         | M    | viv          | ers       | al    | ho         | ish       | fo      | mi                | ly           |       |                |             | ,        |          |
|           |                             | for              | <u> </u>       | <u>(2</u> | < r  | $\gamma_{i}$ | <b>EQ</b> | (la)  | (4         | 2.9.      | n       | ear               | 64           | Pr    | rim            | e)          |          |          |
|           | - 1                         | rep              | lac            | e c       | cho  | uin          | ìh        |       | 5li        | of j      | h       | iith              | h            | ash   | ing            | -h          | iith-    | ,        |
| Sp        |                             | •                |                |           |      |              | m-:       | 1 0 5 | <b>2</b> \ | _         | cl      | 1 DA              | nìng         | i (u  | sin            | 9 1         | hani     | •        |
|           |                             |                  |                |           |      |              | 1         |       |            |           |         | _                 |              |       | _              |             |          |          |
| _         | - to                        | 9                | ua             | rav       | ite  | 2            | 5         | ac    | e          | =(        | )(      | $\wedge$ ) $^{2}$ |              |       |                |             |          |          |
|           | (d                          | <u></u>          | m-1            | l<br>Na   | ١.   |              | ЛС        | ons   | ant        | te        | b       | 0                 | cho:         | sen   |                |             |          |          |
| (1.5      |                             | it               | j=0            | X;        | >    | > C          | N         | ,     | the        | n         | rea     | S                 | ST           | ep    | (1)            |             |          |          |
|           |                             |                  |                |           |      |              |           |       |            |           |         |                   |              |       |                |             |          |          |

Search time = O(1) for first table (h1)
+ O(max chain size in second table)
- to guarantee = O(1):

2.5) while hanj(ki) = hanj(ki) for any i ≠ i'n j:
repick hanj & rehash those lj items > no collisions at second level! Build time: (122) are O(n), (15) & (2.5)? (2.5):  $\Pr$   $\{h_{a,j}(k_i) = h_{a,j}(k_{i'}) \text{ for some } i \neq i' \}$   $\leq \sum_{i \neq i'} \Pr$   $\{h_{a,j}(k_i) = h_{a,j}(k_{i'}) \}$  Union Bound < (2) · 1/2 by universality \[
 \lambda \frac{1}{2} \quad \text{(Birthday Paradox)}
 \]
 \[
 \Rightarrow \text{each trial is like a coin flip, tails } \Rightarrow \text{OK}
 \]
 \[
 \Rightarrow \text{El# trials} \rightarrow \text{2}
 \]
 \[
 \Rightarrow \text{trials} \rightarrow \text{O(lg n) w.h.p. (by Lecture 7)}
 \] - Chernoff bound  $\Rightarrow$  lj = O(lg n) w.h.p.  $\Rightarrow$  each trial O(lg n) time (also obviously O(n)) - must do this for each j  $\Rightarrow$   $O(n lg^2 n)$  time w.h.p. (or obviously  $O(n^2 lg n)$ )

(15): 
$$E\left[\sum_{j=0}^{\infty}l_{j}^{2}\right] = E\left[\sum_{i=1}^{\infty}\sum_{i=1}^{\infty}I_{i-i}^{i}\right]$$
\nindicator vand.  $var = \begin{cases} 1 \text{ if } h_{i}(k_{i}) = h_{1}(k_{i}) \\ 0 \text{ else} \end{cases}$ 

$$= \sum_{i=1}^{\infty}E\left[I_{i-i}^{i}\right] + 2\sum_{i\neq i}E\left[I_{i-i}^{i}\right]$$

$$\leq n + 2\binom{n}{2} \cdot \frac{1}{m} = universality$$

$$= O(n) \text{ because } m = O(n)$$
 $Pr\left\{\sum_{j=0}^{\infty-1}l_{j}^{2} > c \cdot n\right\} \leq E\left[\sum_{j=0}^{\infty-1}l_{j}^{2}\right] \leq \frac{Markov}{c \cdot n}$ 

$$= \frac{1}{2} \text{ for suff. large const. } c$$

$$\Rightarrow E\left[\# \text{ trials}\right] \leq 2$$

$$\text{ $\#$ trials} = O(l_{g}n) \text{ $w.h.p.}$$

$$\Rightarrow 0 \leq 1.5 \text{ take } O(n_{g}n) \text{ $w.h.p.}$$

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| Order-statistic tr              | ees: (from                            | 6.006)              |      |
|---------------------------------|---------------------------------------|---------------------|------|
| - ADT/interface: - insert(x)/c  |                                       | Abstract Data Type  |      |
| - insert(x)/c                   | delete(x)/s                           | successor (x)       |      |
|                                 |                                       | in sorted order     |      |
|                                 |                                       | < x if all distinct |      |
| - select(i): fi                 | nd element                            | of vank i           |      |
| - idea: use easy                | Tree augme                            | intation to sibre   | .+   |
|                                 |                                       | otree) = # nodes in | _    |
|                                 |                                       | e for c in x.child  | renj |
| - say, AVL tree: - rank(x):     | s = binar                             | also work)          |      |
| - vank = x.                     | Λ = .                                 | , al.               |      |
| - 1,00k 100 t                   | a vont for                            | $\sim$              |      |
| - when go                       | left (x > ?                           | (c'):               | )    |
| vank                            | += x'. left.                          | size + 1            |      |
| - when go rank - select(i):     |                                       |                     |      |
| -x = voot                       |                                       |                     |      |
| $\rightarrow$ vank = $x$ .      |                                       | 74 0 740 0          |      |
| - if i = ran                    | k: return                             | X starting          |      |
| - if i < rank                   | $\langle : \times = \times . \rangle$ | let i at o          |      |
| - if i>rank                     | X = X.                                | right               |      |
|                                 | j -= ro                               | ank                 | •    |
| repeat                          |                                       |                     |      |
| -e.a. con't main                | tain rank o                           | feach mode:         |      |
| -e.g. can't main<br>insert(-00) | would cha                             | nge all ranks       |      |
|                                 |                                       |                     |      |

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

# Dynamic Programming

Longest palindromic sequence Optimal binary search trees Alternating coin game

### DP notions

- 1. (haracterize the structure of an optimal solution
- Recursively define the value of an optimal optimal solution based on optimal solutions of subproblems
- Compute the value of an optimal solution in bottom-up fashion (recursion & memorzation). 3.
- Construct an optimal solution from the computed information 4.

```
Def: A palindrome 1s a string that is unchanged when reversed
 Examples: rador, civic, t, bb, redder
Given: A string X [1..n] n > 1
To find: Longest palindrome that is a subsequence
 Example: Given "character"
output "charac"
       Answer will be 71 in length
L(i,j): length of longest palindromic subsequence of X[i.j] for i \ j
Strategy
  def L(i,j):

f = i = x [j]:

f \times [i] = x [j]:
              if i+1 == j: return 2
else: return 2+ L(i+1, j-1)
return max (L(i+1,j), L(i,j-1))
Exercise: compute the actual solution
```

As written, program can run in symbols exponential time: suppose all symbols X[i] are distinct T(n) = running time on input of length n  $T(n) = \begin{cases} 1 \\ 2T(n-1) \end{cases}$ 

Subproblems

But there are only (n) =  $\theta(n^2)$  distinct subproblems also have problems of size I subproblems also have problem only once, running By solving each subproblem only once, running

time reduces to

 $= \theta(n^2)$  $\theta(n^2) \cdot \theta(1)$ 

time to solve # subproblems Subproblem, GIVEN that smaller ones

memoire L(i,j), hash inputs to get output value, and look up hash table to see if value, and look up hash table to see if the subproblem is already solved, else recorse.

- Memoriting uses a dictionary for L(i,j)
  where value of L is looked up by\nusing i,j as a key. (ould just use a\nusing i,j as a key. (ould just use a
  2-D array here where null entries signify
  that the problem has not yet been solved.
- 2 (an solve subproblems in order of increasing j-i so smaller ones are solved first.

Optimal Binary Search Trees: CLRS 15.5

Given: keys Ki, Kz, ... Kn WLOG Ki = i WLOG Ki = i Weights Wi, Wz, ... Wn (search probabilities)

Find: BST T that minimizes:

¿ Wi. (depthy(Ki)+1)

Example: Wi = Pi = probability of searching

Then, we are minimizing expected search cost. English -> French dictionary (say we are representing an English -> French dictionary and common words should have greater weight.)

#### Enumeration

## Strategy

$$W(i,j) = W_i + W_{i+1} + ... W_j$$

$$e(i,j) = \text{(ost of ophmal BST on Ki, Ki+1, ... Kj.}$$

$$want e(i,n)$$

Kr

Pick Kr in some greedy fashion, e.g., Wris maximum

greedy doesn't work

keys Ki..Kr-1\ne(i,r-1)

"optimal substructure"

keys Krain .. Kj

e(r+1,1)

```
e(i,j) = \begin{cases} w_i & \text{if } i = j \\ \min \left( e(i,r-i) + e(r+1,j) + w(i,j) \right) \\ i \leq r \leq j \end{cases}
  + w(i, j) accounts for wr of root Kras
    well as the increase in depth by 1 of
all the other keys in the subtrees of Kr.

(DP tries all ways of making local choice & subproblems.)

takes advantage of overlapping subproblems.)

Complexity: Q(n²). Q(n) = Q(n³)
                              # subproblems time per subproblem
                      (n) subproblems
```

Row of n coms of values Vi, ..., Vn neven In each turn, a player selects either the first or last coin from the row, removes it permanently, and receives the value of the coin.

Question Can the first player always win? Try: 4 42 39 17 25 6

Strategy: VI V2 V3 V4 ... Vn-2 Vn-1 Vn

1) Compare  $V_1 + V_3 + \cdots V_{n-1}$  against  $V_2 + V_4 + \cdots V_n$ 

And pick whichever is greater.

2) During the game only pick from the chosen subset (you will always be able to!)

How to maximize the amount of money won assuming you move first?

V(i+1,j) subproblem with opponent picking

we are guaranteed min {V(i+1,j-1), V(i+2,j)}

we are guaranteed min {V(i+1,j-1), V(i+2,j)} Opponent picks Vi opponent picks Vi+1

We have.  $V(i,j) = \max \left\{ \min \left\{ V(i+1,j-1), \right\} + V_i, \min \left\{ V(i,j-2), \right\} + V_j \right\}$ (omplexity?  $\theta(n^2)$   $\theta(1) = \theta(n^2)$  time per subproblems subproblem

Subproblem

# Example of Greedy Failing for Optimal BST problem

Thanks to Nick Davis!

$$cost = 1 \times 3 + 10 \times 2$$
  
+  $8 \times 1 + 9 \times 2$   
 $w_3$   
= 49

Choosing highest weight key of 2.
as root doesn't work.

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 6.046                       | Lecture 11                         | Mar. 17, 2015            |
|-----------------------------|------------------------------------|--------------------------|
|                             | pairs shortest r                   | paths                    |
| - dynamic<br>- matrix n     | programming nultiplication         |                          |
| - Floyd-Wa                  | arshall algorithm                  |                          |
| - Johnson S<br>- difference | s algorithm<br>e constraints       |                          |
| Recall: single              | -source shortest                   | - paths [6.006]          |
| - given divec               | ted graph G=(V<br>leights w: F->1R | (E) vertex seV,          |
| - find S(s.                 | (v) = shortest-path                | weight s > V YveV        |
| $(or -\infty) if$           | negweight cycle o                  | weight 5 >V YveV         |
| situation                   | algorithm                          |                          |
| unweighted (v               | N=1) BFS                           | $\sqrt{(1+F)}$           |
| nonneg. edge n              | Bellman-Fo                         | ord O(VE)                |
| acyclic graph               | (DAG) topological<br>+1 pass Belln | sort O(V+E)              |
|                             |                                    | Using Fibonacci<br>heaps |
| all of these                | e vesults are .                    | the best known           |

| A | 11-pairs      | shortes          | t po         | aths:                 |              |                    |            |     |          |     |                            |   |
|---|---------------|------------------|--------------|-----------------------|--------------|--------------------|------------|-----|----------|-----|----------------------------|---|
|   | given         | edge-u           | reight       | sed g                 | rapl         | h G                | =(         | 1,E | $\omega$ | ) _ |                            |   |
|   | given         | S(unv)           | for          | all                   | 4            | $v \in V$          |            | ·   |          | •   |                            |   |
|   |               |                  |              |                       | \            | (obv               | ious       |     |          |     |                            |   |
|   | situation     |                  | algori       | thm                   |              |                    | ng .       |     |          | E   | ==()(V <sup>2</sup>        | ) |
|   | unweighte     | d                | IV XI        | 3FS<br>)ijkstv<br>3-F | $\mathbb{Z}$ | 0(                 | VE         |     |          |     | $O(V^3)$                   |   |
|   | nonneg. we    | ights .          | V ×[         | )i, jkstv             | a            | Ŏ(                 | VE         | tΛg | lg V     | ()  | $\mathbb{Q}(\mathbb{V}^3)$ | ) |
|   | general       |                  | [V  X [      | 3-F                   | )            | O(                 | NAE        |     |          |     | 0(14)                      |   |
|   | general       |                  |              | son's                 |              | 00                 | VE+        | Ng) | lg 1     | /)  | $O(N_3)$                   |   |
|   |               |                  | T            | ODAY)                 | )            |                    |            |     |          |     |                            |   |
|   | 11            | 0.4              |              | 1                     |              | <b>M</b>           |            |     | \        |     |                            |   |
|   | these         | result           | s (e'        | xcept                 | thi          | rd)                | are        | al  | lso      |     |                            |   |
|   | best          | Known            |              | don                   | +            | knov               | 7          | NON | j †      | Ø   |                            |   |
|   | these<br>best |                  |              | beat                  | †            | VI ×               | Vij        | KS  | Ma       |     |                            |   |
|   |               |                  |              |                       |              |                    |            |     |          |     |                            |   |
|   | Applica       | ation.           | 50091        | (e // (               | aps          | prep               | roce       | 255 | ing      |     |                            |   |
|   |               | -                | TJ.          | (pe10                 | vee          | nu                 | by         | POĪ | 175      | ر   |                            |   |
|   |               |                  | Lnter        | nei v                 | our          | ing                |            |     |          |     |                            |   |
|   | - define      |                  | , ) <u> </u> | 0 6                   | · _ /        |                    | <i>A</i> C | -   |          |     |                            |   |
|   | derine        | W(U <sub>1</sub> | V) - C       | X) TO                 |              | (U <sub>2</sub> V) | 40         |     |          |     |                            |   |
|   |               |                  |              |                       |              |                    |            |     |          |     |                            |   |
|   |               |                  |              |                       |              |                    |            |     |          |     |                            |   |
|   |               |                  |              |                       |              |                    |            |     |          |     |                            |   |
|   |               |                  |              |                       |              |                    |            |     |          |     |                            |   |
|   |               |                  |              |                       |              |                    |            |     |          |     |                            |   |

| Dyn        | amic              | , pv     | rogra                       | am                   | (#                                | 1):                    |             |                |                |               |                 |                               |                               |                                |                     |                  |
|------------|-------------------|----------|-----------------------------|----------------------|-----------------------------------|------------------------|-------------|----------------|----------------|---------------|-----------------|-------------------------------|-------------------------------|--------------------------------|---------------------|------------------|
|            | amic<br>Sub       | prob     | lem                         | <u>S</u> :           | duv                               | ) = (                  | neig        | ht             | of             | S             | hor             | test                          | P                             | ath                            | u-                  | <b>→</b> ∨       |
| Ĝ          |                   |          |                             |                      |                                   |                        | Isin        | 9              | ≤w             | ١ ^           | edg             | es                            |                               | 7                              |                     |                  |
| (2)        | ) gue             | ssin     | 9:                          | W                    | shat                              | `S -                   | the         | la             | st             | ed            | ge              | (7                            | ( <sub>1</sub> V              | ) ′,                           |                     |                  |
| <u>(</u> 3 | ) gue<br>) rec    | urre     | nce:                        | d                    | (m) =                             | mi                     | n(d         | WX.            | +              | w(            | X.V)            | ) fo                          | r x                           | in                             | , V                 | )                |
|            |                   |          |                             | d                    | (O) ;                             | = {                    |             | īt             |                | u=            | V               |                               | •                             |                                |                     |                  |
|            |                   |          |                             |                      |                                   | l                      | <i>.</i> 00 | e              | lse            | 2             |                 |                               |                               |                                |                     |                  |
| (4)        | topo              | log.     | orde                        | er:                  | for                               | m                      | =0          | ,1.            | <b>,</b> ,     | n-            | 1:              | for                           | ~ u                           | 2                              | v ir                | V:               |
| (5         | topo              | gina     | Pr                          | المح                 | lem:                              |                        |             |                |                | 4             | M               |                               |                               |                                |                     |                  |
|            | if                | no       | neg<br>Pat<br>eight         | we                   | ight                              | $\sim$                 | ycle        | 5              | the            | n             | (by             | B-                            | F, C                          | anal                           | ysi                 | 5)               |
|            | show              | rtest    | pat                         | th:                  | is 5                              | simi                   | ole:        | $\Rightarrow$  | S(1            | LNY.          | )= (            | luv                           | ·1) =                         | $d_{i}^{l}$                    | λ =                 | . · ·            |
|            | (neg              | -W       | eight                       | cu                   | cle                               | نے ۔                   | >d          | n-1)           | <0             | fo            | ر<br>د ۲        | 507                           | e                             | U6                             | V)                  |                  |
|            | 0                 |          | 0                           | 0                    |                                   |                        | \           | V              |                |               |                 |                               |                               |                                | • )                 |                  |
|            |                   |          |                             |                      |                                   |                        |             |                |                |               |                 |                               |                               |                                |                     |                  |
| T          | ime:              | V        | 3 50                        | ubor                 | oble                              | ems                    | •           | 1/ 0           | choi           | ces           | •               | $\bigcirc$                    | 1)                            | tim                            | e/ch                | oice.            |
| 1          | ime:              | V<br>= 0 | 3<br>50<br>1/4              | ibpr                 | oble<br>- n                       | ems                    | botte       | V              | choi<br>tho    | ces           | //×             | O(Bel                         | 1)<br>Umo                     | tim<br>ah-F                    | e/ch                | oice<br>(        |
| 1          | ime:              | V<br>= 0 | 3<br>{\/ <sup>4</sup>       | jbpr<br>)            | oble<br>- n                       | ems                    | bette       | Var.           | choi<br>tha    | ces<br>.n (   | √×              | O(<br>Bel                     | 1)<br>Umo                     | tim<br>un-f                    | e/ch<br>ovc         | oice             |
|            |                   |          |                             |                      |                                   |                        |             |                |                |               |                 |                               |                               |                                | _                   |                  |
|            | otton             | up       | vic                         | λ                    | reli                              | αχα                    | tion        |                |                |               |                 |                               |                               |                                | _                   |                  |
|            | ottom             | -up<br>m | vic<br>in r                 | ang                  | reli                              | αχα                    | tion        |                | tep            | 5:            | (l<br>&         | ike<br>Be                     | Di<br>Om                      | jks<br>an-                     | tra<br>Forc         | <b>d</b> )       |
|            | ottom             | m        | vic<br>in r                 | ang                  | veli<br>ve (:<br>V:               | <u>axa</u><br>1.n      | tion        |                |                | 5:            | (l<br>&         | ike<br>Be                     | Di<br>Om                      | jks<br>an-                     | tra<br>Forc         | <b>d</b> )       |
|            | ottom             | m        | vic<br>in r<br>u i          | ang<br>n             | velipe (:<br>V:<br>V:             | oxa<br>1, n            | tion<br>):  |                |                | 5:            | (l<br>&         | ike<br>Be                     | Di<br>Om                      | jks<br>an-                     | _                   | <b>d</b> )       |
|            | ottom             | m        | in r<br>u i<br>r v          | ang<br>in<br>in      | relie (:<br>V:<br>V:              | <u>αχα</u><br>1, η     | tion<br>):  | S              | tep.           | 5:<br>7 i     | (l<br>nst       | ike<br>Be                     | Di<br>Um<br>of<br>he          | jks<br>an-<br>u<br>lps         | tra<br>Force<br>(x. | d)<br>J) —       |
|            | ottom             | m        | in r<br>u i<br>r v          | ang<br>in<br>in<br>x | relie (:<br>V:<br>V:<br>in        | 0.x0<br>1.n<br>V:      | tion):      | S+             | tep<br>dx      | 5:<br>7:      | (l<br>nst<br>on | ike<br>Be<br>ead<br>by        | Di<br>Umi<br>of<br>he         | jks<br>an-<br>u<br>lps         | tra<br>Force<br>(x. | l)<br>v)—        |
| <u>B</u>   | ottom<br>for<br>f | m<br>for | in r<br>\nu i<br>r v<br>for | ang<br>in<br>in<br>x | relie (:<br>V:<br>V:<br>in<br>duv | αχα<br>1, η<br>γ:<br>> | duz         | S <sup>+</sup> | d <sub>x</sub> | 5:<br>7:<br>v | (l<br>nst       | ike<br>Be<br>ead<br>Ly<br>rel | Di<br>Umi<br>of<br>he<br>laxi | jks<br>an-<br>u<br>lps<br>atio | tra<br>Ford<br>(xn  | d)<br>J)-<br>tep |
| <u>B</u>   | ottom<br>for<br>f | m<br>for | in r<br>\nu i<br>r v<br>for | ang<br>in<br>in<br>x | relie (:<br>V:<br>V:<br>in<br>duv | αχα<br>1, η<br>γ:<br>> | duz         | S <sup>+</sup> | d <sub>x</sub> | 5:<br>7:<br>v | (l<br>nst       | ike<br>Be<br>ead<br>Ly<br>rel | Di<br>Umi<br>of<br>he<br>laxi | jks<br>an-<br>u<br>lps<br>atio | tra<br>Ford<br>(xn  | d)<br>J)-<br>tep |
| <u>B</u>   | ottom             | m<br>for | in r<br>\nu i<br>r v<br>for | ang<br>in<br>in<br>x | relie (:<br>V:<br>V:<br>in<br>duv | αχα<br>1, η<br>γ:<br>> | duz         | S <sup>+</sup> | d <sub>x</sub> | 5:<br>7:<br>v | (l<br>nst       | ike<br>Be<br>ead<br>Ly<br>rel | Di<br>Umi<br>of<br>he<br>laxi | jks<br>an-<br>u<br>lps<br>atio | tra<br>Ford<br>(xn  | d)<br>J)-<br>tep |

Matrix multiplication: (recall) given n×n matrices A&B,

compute C=A·B: Cij = \( \frac{2}{2} \) aik bkj

- O(n^3) via standard algorithm

- O(n^2.807) via Strassen's algorithm

- O(n^3.376) via Coppersmith-Winograd algorithm

- O(n^3.3728) via Vassilevska Williams algorithm Connection to shortest paths:

- define  $\Phi = \min \& O = +$ - then C = AOB is  $C_{ij} = \min (a_{ik} + b_{kj})$ - define  $D^{(m)} = (d^{(m)})_{\eta} W = (w(i_{\eta j}))_{\eta} V = \{1_{\eta} 2_{\eta} ... n\}$   $\Rightarrow D^{(m)} = D^{(n-1)} \odot W (by 3) above)$   $= W^{(m)}$  where  $W^{(m)} = \begin{pmatrix} 0 & \infty & \infty \\ \infty & \infty & \infty \\ \infty & \infty & \infty \end{pmatrix}$ [Wim makes sense because @ is associative, which follows from (Raminat) being closed semiring) Matrix multiplication algorithm:

- n-2 multiplications  $\Rightarrow$   $O(n^4)$  time (still no better)

- repeated squaring:  $(W^2)^2 = W^{2regn} = W^{n-2}$ = (S(i,j)) if no negative-weight cycles - time:  $O(n^3 \lg n)$ - neg-weight cycles (>> neg. diagonal entries in W - com't use Strassen etc. = (no negation)

| Transitive closure: $t_{ij} = \{1 \text{ if there's a path } i \rightarrow j \}$ $= \{i \text{ is } S(i,j) < \infty^{?}, j \} \xrightarrow{\text{special APSP}} \{(s, s, s, s, s, s, s, s, s, s, s, s, s, s$                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 10 else special                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| $= \left[ is \ S(i,j) < \infty? \right] - \frac{case}{APSP}$                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| - ({0.13, or, and) is a ring => can use Strassen etc.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| - ( $\{0.1\}$ , or, and) is a ring $\Rightarrow$ can use Strassen etc. $\Rightarrow$ $O(n^2.3728 \lg n)$ time                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| +0 1 1 1 100 0 -11 · · · · · · · · · · · · · · · · · ·                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| Floyd-Warshall algorithm: faster dynamic program                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| 1) subproblem cuv = weight of shortest path u->v                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| whose intermediate vertices \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| (i) > (k) > (V={1,2,,n})                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| a) guessing = does shortest path use vertex k?                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| (3) cuv = min { cuv , cuk + ckv }                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| a) guessing = does shortest path use vertex $k$ ?  (a) cuv = min $\{(k-1), (k-1), (k-1)\}$ (b) cuv = $(u,v)$ (cuv = $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use vertex $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v)$ (use $(u,v$ |
| 4) for k: for u, v: use vertex k only onc                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| (5) $S(u_n v) = c_{uv}^{(n)}$ , neg.—weight cycle $\Leftrightarrow$ neg. $c_{uu}^{(n)}$                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
|                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| Time: $O(V^3)$ subproblems · 2 choices · $O(1)$                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| $=0(\sqrt{3})$                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
|                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| Bottom up via relaxation: simple lefficient                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| Bottom up via relaxation: simple lefficient in practice.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| for $k = 1, 2, \ldots, n$ :                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| for u in V:                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
|                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| again OR tor v in V:                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| to omit I car - cak i cky i z resonation again                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| Subscripts Cuv = Cux + Cxv                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 |
|                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |

Johnson's algorithm: 1) find function h: V-> R such that Wh(unv) = w(unv) + h(u) - h(v) > 0 for all unveV or determine that a negative-weight cycle exists @ run Dijkstra's algorithm on (V.E. wn) trom every source vertex seV ⇒ get Sh(unv) for all unveV (3) Claim S(u,v) = Sh(u,v) - h(u) + h(v)Proof of claim: - look at any u->v path p in G
- say p is vo -> v1 -> v2 -> -> > vk  $\Rightarrow \omega_h(p) = \underset{i=1}{\overset{k}{\geq}} \omega_h(v_{i-1},v_i)$  $= \sum_{i=1}^{k} \left[ \omega(v_{i-1}, v_i) + h(v_{i-1}) - h(v_i) \right]$   $= \sum_{i=1}^{k} \omega(v_{i-1}, v_i) + h(v_0) - h(v_k) \quad \text{telescoping}$  $= \omega(p) + h(u) - h(v)$ - 50 all u=v paths change in weight by the same offset + h(u) - h(v) >> shortest path is preserved (but offset) []

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| 6.046                                                                                                        | Lecture 12                                            | Mar. 19, 2015                                                                                                               |
|--------------------------------------------------------------------------------------------------------------|-------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------|
| - MSI prob<br>- optimal s                                                                                    |                                                       | Tree (MST)                                                                                                                  |
| Recall: [Lecti<br>Greedy algori<br>choice/di<br>- saw greed<br>- Dijkstra's<br>(c.f. Bellin<br>- today: gree |                                                       | g make locally best<br>g effect on future<br>scheduling problem<br>$\approx$ greedy<br>rental improvement)<br>graph problem |
| Tree = connect Spanning tree = subset of Spanning (                                                          | ited graph with of graph's edges the Containing all v | no cycles<br>lat form a tree<br>'ertices                                                                                    |

| M | ihimu               | m 5         | pann                   | ing t              | ree               | (MS                  | <u>(Ti</u>                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     | pro      | sbl              | em                | 4       |           |              |     |
|---|---------------------|-------------|------------------------|--------------------|-------------------|----------------------|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------|------------------|-------------------|---------|-----------|--------------|-----|
|   | 911                 | ven         | a g                    | raph               | G                 | (VE)                 | ) &                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | edo      | <u> </u>         | wei               | ghts    | w         | : E -        | >R, |
|   | inimu<br>giv<br>fio | nd s        | spanr<br>u(T)          | ing<br>= 2<br>ee   | tree<br>1, w<br>T | 7⊆<br>(e)            | Ē                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | OF       | mī               | inim              | ium     | M         | <u>eight</u> |     |
|   | Exar                | •           |                        | 95                 | 5                 | 12                   |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                | 9        | $\bigcirc$       |                   |         |           | eight:       |     |
|   |                     |             | 14                     | the same           | 8                 | 10                   | The state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the state of the s | 15       |                  | )                 |         |           |              |     |
|   | Naive               | e a<br>exp  | lg <u>ori</u><br>Poner | thm                | i (               | theck<br>ie i        | < Ol                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           | 20       | sp               | λην               | ing     | tv        | rees         |     |
| G | reedy<br>g          | _pr         | oper<br>ly c           | ties:              | P<br>ith,         | roble<br>ns          | USI                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            | lal      | ar<br>ly         | ven<br>So         | ablatis | e-fy:     | to           |     |
|   |                     | o F<br>solu | mal<br>probl<br>tion(  | Sub<br>lem<br>s) t | inc<br>inc        | uctu<br>orpo<br>Subp | rations of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the control of the contro | e<br>ler | opt<br>op<br>n(s | imo<br>timo<br>s) | al g    | sal<br>19 | ution        | \   |
|   | 2 9                 |             |                        |                    |                   |                      |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |          |                  |                   |         |           |              |     |

| Kr      | usl       | <al< th=""><th>'<sub>S</sub></th><th>alg</th><th>ori</th><th>the</th><th>n:</th><th>ta</th><th>ke g</th><th>loba</th><th>Wy</th><th>low</th><th>est-</th><th>weig</th><th>ht e</th><th>dge</th><th>2</th><th>con</th><th>trac</th></al<> | ' <sub>S</sub> | alg         | ori      | the         | n:       | ta       | ke g                | loba            | Wy       | low                                               | est-     | weig     | ht e     | dge      | 2          | con        | trac |
|---------|-----------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------------|-------------|----------|-------------|----------|----------|---------------------|-----------------|----------|---------------------------------------------------|----------|----------|----------|----------|------------|------------|------|
|         |           | m                                                                                                                                                                                                                                        | ain            | Fair        | 1 0      | Con         | nec      | tec      | $\int_{0}^{\infty}$ | omf             | )02N     | ent                                               | 5        | în       | Ma       | 51-50    | s-f        | ar -       | T    |
|         |           |                                                                                                                                                                                                                                          |                |             |          |             |          |          |                     | tur             |          |                                                   |          |          |          |          |            | •          | •    |
|         | _         |                                                                                                                                                                                                                                          |                |             |          |             |          |          |                     | ne              |          |                                                   |          |          |          |          | )          |            |      |
|         | _         | fo                                                                                                                                                                                                                                       | Λ /            | 101         | 1:       | N           | lak      | 0 -      | 50                  | t(v)            | )        |                                                   | itio     | lle      | . 1      | /16/I    | te         | de         | \mD  |
|         |           |                                                                                                                                                                                                                                          |                | E           |          |             |          |          |                     | ( ( )           |          |                                                   |          |          | 7        |          |            | / 0        | 3111 |
|         | _         | fr                                                                                                                                                                                                                                       | 51 \<br>VC 4   | ひっこ         | (,,      |             |          | (        | 710                 | 5NC             | V01      | acin                                              | ı Oz     | LAFG     | tak      | it o     | rde        | (r)        | l.   |
|         |           | 10                                                                                                                                                                                                                                       | - 7.           | f 1         |          | √/<br>√ _ < | くっと      | (,)      | +                   | inc<br>Fin      | 1 -      | 201                                               | 9        | 1:       |          | 1-A      | PYO        | 1. T       |      |
|         |           |                                                                                                                                                                                                                                          | 1              |             | 0 Y      | ے مد<br>ا   | )        | tu)      | 7                   | 1 IN            | ici      | المحال                                            | CA       | , -      |          | Syl      | SON        | ents       |      |
|         |           |                                                                                                                                                                                                                                          |                | _           | uu<br>Ha |             | <u> </u> | , ,      | 7                   |                 |          |                                                   |          | =        | <b>)</b> | - W      | 10h        | +          | _    |
|         |           |                                                                                                                                                                                                                                          |                |             | W,       | HOI         | vci      | 人へ `     | <b>V</b> )          |                 |          |                                                   |          |          | m        | rake     | ~ <b>Q</b> | Cy         | CIR  |
|         | $\bigcap$ | <b>~</b> \/\                                                                                                                                                                                                                             | 704            | Tian .      | رد       | î l.        | 0) [ 0   | 16.0     | .+.                 | +               | ico o    | . T                                               |          | 4        | , ,      | ς Λ.     | 15         | r 7        | 术    |
|         | 4         |                                                                                                                                                                                                                                          | 20             | ING         | <u> </u> | <u> </u>    | 100      | 1        | W1 .                |                 | To       | - <del>                                    </del> | <u> </u> |          |          |          |            |            | ,    |
|         |           |                                                                                                                                                                                                                                          |                |             | _        | ΛK          |          |          | L -                 | 5M              | _        |                                                   |          | H        | $\int$   | 25)<br>e | of         | ) (7       | 4    |
|         |           |                                                                                                                                                                                                                                          | Wr             | ien         | a        | you         | ng       | و<br>۲   | 0e                  | twee            | en.      |                                                   |          |          | 70       | Ž\V      | 15         | <u>(S)</u> |      |
|         |           |                                                                                                                                                                                                                                          | Co             | mpo         | Med      | nIS<br>1    |          | -1       | <i>ک</i> ر          | _ي.             | U        | ise                                               | J        | _        |          | <b>S</b> | \          |            |      |
|         |           |                                                                                                                                                                                                                                          | gva            | eed         | y-,      | Cho         | oice     | P        | ope                 | Cz:             | 5        | n (                                               | Cut      |          | $C_1$    | ~ V      |            | Ca         |      |
|         | To        |                                                                                                                                                                                                                                          |                | <del></del> | . (      | ~\<br>\     | ,        | $\sim$ / | ι λ                 | T,              | <b>.</b> |                                                   | . (      | \/-`     | \ A      |          | \ _        | _          | \    |
|         |           | me                                                                                                                                                                                                                                       |                | Isa         | rt (     |             | ) +      | 0        | Λ).                 | Tmainy its 0(1) | kesi     | et <sup>*</sup>                                   | + (-     | ノヒ       | 1.6      | find     | +          | lunic      | sn)  |
|         |           |                                                                                                                                                                                                                                          |                | O(E         | l le     | E           | )_       |          | +                   | iny             |          |                                                   |          |          |          | 00       | x(V        | )) a       | M.   |
|         |           |                                                                                                                                                                                                                                          | (              | )(E         | ) 6      | .9.         | it       | W        | eigh                | 15<br>0(1)      | 17       |                                                   | 11       |          |          | 1        | 1          | ົ          |      |
|         |           |                                                                                                                                                                                                                                          | are            | vī S        | ite      | gers        | ; E      | 10       | 1E                  | 0(1)            |          | ~                                                 | the      | 2n       | Con      | be       | at         | <b>Yri</b> | Vh   |
|         |           |                                                                                                                                                                                                                                          |                |             |          |             |          |          |                     |                 |          |                                                   |          |          |          |          |            |            |      |
| $\circ$ | ,         |                                                                                                                                                                                                                                          |                | <b></b>     | Λ        |             | 16       |          |                     | 1               |          | 140                                               |          | <b>—</b> |          |          | 00.        |            |      |
| De De   | est       |                                                                                                                                                                                                                                          | <u>15</u>      | 1           | alg      | or          | th       | m:       | L                   | Karg            | er.      | , Kl                                              | ein      | , 10     | vje      | ın I     | 997        | 3]_        |      |
|         |           | $\bigcirc$                                                                                                                                                                                                                               | (V+            | E)          | é        | xpe         | ect      | ed       | 4.                  | me              | <i>(</i> |                                                   | (v       | and      | OM       | 120      | d)         |            |      |
|         |           |                                                                                                                                                                                                                                          |                |             |          | 4           |          |          |                     |                 |          |                                                   |          |          |          |          |            |            |      |

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

## Linear Programming

Examples: politics, flow, shortest paths General form and converting to it Sim plex algorithm
- Iterating over slack form

#### Politics

How to campaign to win an election? Staff estimates votes obtained per dollar spent advertising in support of a particular issue

| ad vertising "    | )<br>)c   | mographic  | fural  |
|-------------------|-----------|------------|--------|
| Policy            | Urban     | Suburban.  | 3      |
| X, Building roads | -2        | 2          | -5     |
| Control           | 8         | 0          | 10     |
| Farm substilles   | 0         | 0          | 2      |
| Caroline tax      | 10        |            | 1.     |
|                   | yarity in | EACH demos | 50,000 |

EACH demographic 50,000 Wart to win 100,000 100,000 25,000 Population majority 50,000 by spending minimum

```
Algebraic setup
                             denote dollars spent
   Let X, X2 X3 X4
    per issue.
         Minimize X1+X2+X3+X4
          Subject to () -2x, + 8x2 + 0x3 + 10x4 >, 50,000
                       (2) 5x_1 + 2x_2 + 0x_3 + 0x_4 > 100,000
                       (3) 3×1 -5×2 +10×3 -2×4 7,25,000
                       X1, X2, X3, X4 7,0 (can't unadvertise)
              X1 = 2050 000/111
                                        X1+ X2+ X3 + X4
    Ophmum:
                ×2 = 425 000/111
                                      = 3 100 000
                x_3 = 0
x_4 = \frac{3100000}{111}
 Linear Programming (LP)
- Minimize or maximize linear objective function
subject to linear inequalities (& equations)
     yariables = \begin{pmatrix} x_1 \\ x_2 \\ \vdots \end{pmatrix}
```

- Objective function:  $\vec{z} \cdot \vec{x} = c_1 x_1 + c_2 x_2 + \cdots c_d x_d$ Inequalities:  $A \times \leq \overrightarrow{b} \sim A \times n \times d$ \ne.g.,  $x_1 - x_3 \leq 7$  (10-100)  $x \leq 7$ 

thus: max c.x s.t. Ax < 6, x >10 Is there a short certificate that shows LP solution is indeed optimal?

Consider 
$$\frac{25}{222} \times (1) + \frac{46}{222} \times (2) + \frac{14}{222} \times (3)$$

$$= \frac{1}{222} \times \frac{1}{111} + \frac{1}{222} + \frac{1}{222} \times \frac{1}{222} + \frac{1}{222} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{111} \times \frac{1}{1111} \times \frac{1}{1111} \times \frac{1}{1111} \times \frac{1}{1111} \times \frac{1}{1111} \times \frac{1}{1111} \times \frac{1}{1111} \times \frac{1}{11$$

Since X1 + X2 + X3 + X4 >1 X1 + X2 + 140 X3 + X4 remember xi 7,0 no solution can be smaller than this-

#### LP DUALITY

Short certificate is not a coincidence but a consequence of the following.

Theorem: max 
$$\overrightarrow{C}.\overrightarrow{x}$$
 =  $s.t.$   $\overrightarrow{A}\overrightarrow{Y} \geqslant \overrightarrow{C}$ 
 $\overrightarrow{x} \geqslant 0$ 

Theorem:  $\overrightarrow{A} \Rightarrow 0$ 
 $\overrightarrow{A} \Rightarrow 0$ 

Theorem:  $\overrightarrow{A} \Rightarrow 0$ 
 $\overrightarrow{A} \Rightarrow 0$ 

related to maxflow-minut theorem

# heneral algorithms

- Simplex algorithm: x walks from vertex to vertex practical but worst-case exponential
- Ellipsoid algorithm: Guarantee OFT & ellipsoid
  Shrink ellipsoid

First polytime, weful in theory, impractical

- Interior point method: \(\fix\) moves inside polytipe

polytime & quite practical

### CONVERTING TO STANDARD FORM

- 1) Want to minimize -2x, +3x2. Negate coefficients and maximize 2x, -3x2.
- 2) If X; does not have a non-negativity

  (onstraint. X; replaced by X; X; " X; 70

  Xj" 70
  - 3) Equality constraint X1+x2=7 translated to X1+12 57, X1+12 777
  - constraint translated to < by multiplication
    of -1

Difference constraints: Xi - Xj & Wij spend use of linear programming where spend use of A has one +1 and one -1, & rest os solved by Bellman Ford

=|f|Maximum Flow  $\max_{v \in V} f(s,v)$ s.t.  $f(u,v) = -f(v,u) + u,v \in V$  shew YEV f(u,v) = 0 + u E V - {s,t} conject
vation  $f(u,v) \leq c(u,v) + u,v \in V$  capacity

Shortest paths From vertex s:

max & d[v]

S.t. d[v] - d[u] < w(u,v) + (u,v) & E (triangle inequality) d [s] = 0

no solution (=> neg-weight cycle reachable from s max not

Works well in practice, but exponential in the worst case

Flow: Represent LP in slack form

(onvert one slack form into

(onvert one slack form where

an equivalent slack form where

an equivalent has not decreased

objective value increased.

and has likely increased.

Keep going till the optimal solution

keep going till the optimal solution

Think of Simplex as Gaussian Elimination on inequalities

Maximize 
$$3x_1 + x_2 + x_3$$

Subject to:

 $x_1 + x_2 + 3x_2 \leq 30$ 
 $x_1 + 2x_2 + 5x_3 \leq 24$ 
 $2x_1 + 2x_2 + 5x_3 \leq 36$ 
 $4x_1 + x_2 + 2x_3 \leq 36$ 
 $x_1, x_2, x_3 \neq 0$ 

Nonbesic variables

 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 

Stack form:

 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 
 $x_1, x_2, x_3 \neq 0$ 

Objective function: 3(0) + 1(0) + 1(0) = 0

Objective function: 3(0) + 1(0) + 1(0) = 0

be solution, may not always

be solution.

1) Select a nonbasic variable Xe whose coefficient in the objective function is positive

2) Increase the value of Xe as much as possible who violating any of the constraints

Variable te becomes basic, some other

variable tecomes honbasic

variable becomes honbasic

variables & objective function

(values of other basic variables & objective function

may change)

Increese the value of XI. 3rd constraint is
the tightest one (-4 multiplier) and limits
how much we can increese XI.

X1 = 9 -  $\frac{\chi_2}{4}$  -  $\frac{\chi_3}{4}$  -  $\frac{\chi_6}{4}$ Rewrite other equations with  $\chi_6$  on r.h.s. That is, replace  $\chi_1$  with above equation's r.h.s.

11 = X4 = - 4×3 + ×1 X5 =

Original hasic solution: (0,0,0,30,24,36) EQUIVALENCE satisfies II and has objective value 27 + 4.0 + 1.0 - 3.36 = 0Basic solution for II: set nonbasic values to 0 (9,0,0,21,6,0) Basic Solution for II satisfies I, objective value = 27

Increasing X6 causes objective value to decrease 1/2 or 1/3: choose x3 Again 3rd constraint is the limiting factor  $x_3 = \frac{3}{2} - \frac{3x_2}{8} - \frac{x_5}{4} + \frac{x_6}{8}$ 111 + X2 - X5 - 16 X6  $X_1 = \frac{33}{4} - \frac{X_2}{16} + \frac{x_5}{8} - \frac{5\times6}{16}$  $\chi_2 = \frac{3}{2} - \frac{3\chi_2}{8} - \frac{\chi_5}{4} + \frac{\chi_6}{8}$  $\frac{69}{4} + \frac{3}{16} + \frac{5}{8} - \frac{2}{16}$ 

Basic solution III:  $(\frac{33}{4}, 0, \frac{3}{2}, \frac{69}{4}, 0, 0)$ Objective volue: 111

 $28 - \frac{x_3}{6} - \frac{x_5}{6} - \frac{2x_6}{3}$  $X_1 = 8 + \frac{X_3}{6} + \frac{X_5}{6} - \frac{X_6}{3}$   $X_2 = 4 - \frac{8X_3}{3} - \frac{2X_5}{3} + \frac{X_6}{3}$  $-\frac{x_3}{2} + \frac{x_5}{2}$ > all nonbasic variable coefficients in objective function are negative > reached!

constraints We won't prove that ... Simplex converges in (n+m) iterations variables

How to determine of LP is feasible?
What if LP is feasible but the invital besite solution is infeasible?
How do we determine of the LP is unbounded?
How do we choose the pivot? Did not discuss.

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

|    | _                                      | Co         | in                   | aş    | Sur        | ne        | al               | $\mathbb{U}_{-}$ | 9u       | ess      | in            | 9 ī         | S                   | do          | re              | fir        | st                |           |
|----|----------------------------------------|------------|----------------------|-------|------------|-----------|------------------|------------------|----------|----------|---------------|-------------|---------------------|-------------|-----------------|------------|-------------------|-----------|
|    | $\Rightarrow$                          | eg         | ghiv                 | rale  | ent        | to        | P                | oly              | nor      | nial     | l             | tim         | e '                 | ver<br>Ver  | ific            | ev .       | of                |           |
|    |                                        | Po         | Run                  | m     | rial       | 1-5       | i <del>Z</del> e | <i>(</i>         | cer      | tifi     | cate          | 25          | for                 | YE          | <b>35</b>       | ans        | wel               | (5        |
|    |                                        |            | te                   |       |            |           |                  |                  | . /      |          |               |             |                     |             |                 |            |                   |           |
| _  | Dra                                    | 10         | em                   | X     | is         |           | 0                |                  |          |          |               |             |                     |             |                 |            |                   |           |
|    |                                        |            | P-0                  |       |            |           |                  | <i>C</i> ,       | Χe       | NF       | > 5           | 2 2         | ( ;                 | <b>S</b>    | NP-             | ha         |                   |           |
|    |                                        |            |                      |       |            |           |                  |                  |          |          |               |             |                     |             |                 |            |                   | X         |
|    |                                        | . 71       | _ ;                  | f 1   | ) ±        | ۸ID       | 14.              | y                |          | (d       | P             |             | / N/S               |             | ) _             | s X        | ()                |           |
|    |                                        |            |                      | ,     | 7          | / ۷ ۱     | 1,4              | (er              |          | 14       |               |             | _' V [              |             |                 |            |                   |           |
|    | ım,                                    | ۔ ر ا      | tic                  |       | for        |           | <b>(</b> ) (     | 10               | 210.     | Δ        | 4             |             | cal.                | 00.         | . 7             | <b>Z</b> - |                   |           |
|    | 100                                    | Duc<br>Dua | 2110                 |       | 110        | m<br>a.o  |                  | MX C             | i.U      | 7        | 10            | 7           | 00                  | xer<br>liac | n <u>l</u>      | יני ל      | -<br>ւքս <u>-</u> | t-        |
|    | 1-1-1-1-1-1-1-1-1-1-1-1-1-1-1-1-1-1-1- | gn         | OMI                  | av i  |            | +         | D                | 901              | 110      | to       | $\mathcal{C}$ | <b>5</b> NO | er i                | 0           | 7 /             | ) (V       | φα                | 12        |
|    | in!                                    | O          | eg                   | VIV   | Ove        | MI        | D                | 12               | 1pi      | 117      | 30            |             |                     |             | A.              | كاهد       |                   |           |
|    |                                        |            | t)                   | Sar   | ne         | 76<br>7   | 5/1              | 10<br>1          | an<br>D  | SWG      | X<br>         |             | 1 \                 | <b>D</b>    |                 | 0          |                   |           |
|    | _                                      | 15         | Be Be                | = P   | T<br>N     | hei<br>11 | n /              | 4 <              | 4 15     | 1        | ۷             | 7           | † <del></del> )     | B-          | <sup>3</sup> 29 | XVE        |                   |           |
|    | _                                      | 1+         | ν                    | : //( | A 15       | rhei      | n 1              | 46               | NF       | 1        |               |             | ΛIΩ                 | 1           | n               |            |                   |           |
|    |                                        | ıt         | Α                    | 15    | /V1        | -ha       | ard              | 1                | hen      | n C      | <b>3</b> i    | 5           | NY.                 | -ho         | ivd             |            |                   |           |
| 11 |                                        | 1          |                      |       | ,          |           |                  | 4 17             |          |          | n             | _/          |                     |             |                 |            |                   |           |
| Ho | W                                      | to         | Pr<br>€ 1            | ove   | 2 /        | X         | îS_              | Νŀ               | <u> </u> | om       | ple           | 210         | •                   | n           |                 | //         |                   |           |
|    | (1)                                    | Х          | $\epsilon$ $\lambda$ | JP.   |            | Jīa       | N                | <b>She</b>       | lete     | ern      | nini          | sti         | C                   | alg         | gori            | thi        | n                 |           |
|    |                                        |            | Λ                    |       | ^          | ov        | · C              | er               | titi     | cal      | e             | +           | VE                  | rit         | fier            | -<br>. ^   | em                |           |
|    | (F)                                    | rec        | Yuc                  | e -   | <u>tro</u> | n k       | < No             | WY               | ı /      | VP.      | -CO           | mp          | let                 | e           | Pro             | ble        | em                | λ         |
|    |                                        |            |                      | -     | <u>to</u>  | X         | _                |                  |          |          | <b>\</b> 1    |             |                     |             |                 |            |                   |           |
|    |                                        | (=         | ⇒ a                  | my    | Z          | ?E 1      | VP               | ->               | Y        | <b>→</b> | X             | <b>⇒</b>    | X                   | îS          | NF              | 2-1        | arc               | 1)        |
|    |                                        | (A)        | pol                  | y-    | tim        | e         | con              | vev              | Sìc      | m T      | from          | n >         | y il                | npui        | 15 1            | 6)         | l in              | puts      |
|    |                                        | <b>B</b>   | if                   | Y     | ans        | swe       | ri               | S                | YE:      | 5 1      | he            | $\lambda$   | $\langle a \rangle$ | nsc         | ver             | īs         | YE                | puts<br>5 |
|    |                                        |            | if                   | X     | ai         | 15W       | er               | ìS               | YE       | ·S -     | the           | n >         | / a                 | nsi         | ver             | is         | YE                | 3         |

3-Dimensional Matching: (3DM) given disjoint sets X.Y.Z each of n elements. & triples TEXXYXZ, is there a subset SET such that each element \( \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times \times - ENP: guess which triples ES - O(T) nondet. check for exact coverage - O(T) - NP-hard by reduction from 3SAT: cos of x or x [Garey & Johnson 1979 book] ># occurrences of x or x - variable x -> 2nx, chain: 7000 - either x's or x's left x of local of x's local of x's left x's or x's left x's x's left x's x's x's x's x's x's x's x's x's x's - exactly 2 solutions 2 x y y y z > x unique copies x exy local to clause vest \(\in \) - solvable if x or y or z's left
- garbage collection: \*\* all x; & x; s

\* t shared (per repeat) repeated & nx, - # clauses, times #x & x 's left by vars. # covered by clauses - can cover exactly all unused x s & x s satistying assignment > 3DM (x=T -> leave x: x=F -> leave x: satisfy clauses; cover remaining with garbage collector) 3DM -> satisfying assignment (x left > x=T; \overline{\times} left > x=F; satisfy clauses)

Subset Sum: given n integers A= {a1.a2....an} is there a subset SEA such that  $\Sigma S = \Sigma a = t?$ - ENP: guess  $S_n$  are - pseudopolynomial algorithm via DP (like knapsack)
- Spolynomial in n & sum of numbers (A)
- Weakly NP-hard by reduction from 3DM 5 hard when numbers exponential in n (but still only polynomial number of bits) - view numbers in base b=1+ max nx. > never overflow/carry # occurrences of x; - triple  $(x_i, x_j, x_k) \rightarrow 00010010001000$ -t=11-..1=56+64+64

4-Partition: given n integers A = \( \frac{2}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{3} \) = \( \frac{1}{ is there a partition into 1/4 subsets of 4 each with the same sum t = 5/A/(1/4)? - €NP: guess A > subset mapping - strongly NP-hard by reduction from 3DM [G&J] 4) NP-hard even when number values polynomial in n - write numbers in base r=100. E(XUYUZ) - element  $x \in X \rightarrow (10, i, 0, 0, 1) = 10^{4} + ir^{3} + 1$ - element  $y_{j} \in Y \rightarrow (10, 0, j, 0, 2)$ - element  $z_{k} \in Z \rightarrow (10, 0, j, 0, 2) \times (ny_{j} - 1)$ - element  $z_{k} \in Z \rightarrow (10, 0, 0, k, 4) \times (nz_{k} - 1)$ - triple  $(x_{i}, y_{j}, z_{k}) \rightarrow (10, -i, -j, -k, 8)$ copies  $(x_{i}, y_{j}, z_{k}) \rightarrow (10, -i, -j, -k, 8)$ copies - triple (xinyinzk)  $= 10r^4 - ir^3 - jr^2 - kr^3 + 8$ - target sum t = (40.0.0.0.0.15) = 40r4 + 15- no carries (r large enough) - mod r => use one xi. one yj, one zk, one triple - [si/r] mod r ⇒ zx & triple match - [21/r2] mod r ⇒ y; & triple match  $-\lfloor 2/r^3 \rfloor \mod r \Rightarrow x_i \& \text{triple match}$ - LE/r4] mod r ⇒ 4.10 → chosen triple ∈ S or 11+11+8+10 > unused triple \$5 primary (10) form of xi (or y; or Zk) must appear in exactly one chosen triple (and elements of triple must all match)

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

### Approximation Algorithms I

Definitions Vertex cover

Set cover

NP-complete problems

Np-hard

Partition

# Approximation Algos & Schemes

An algorithm for a problem of size n has an approximation ratio P(n) if for any input, algorithm produces a solution of cost C such that

max ( copt, copt) < e(n)

Algorithm is an e(n)-approximation algorithm

An approximation scheme takes as input \$70 and for any fixed \$\xeller\$, the scheme is a (1+\xeller)-approximation algorithm.

Polynomial time approximation scheme (PTAS): polynomial in n

Fully PTAS: polynomial in n and \( \frac{1}{\xi} \) O(\( n^2/\xi\) PTAS not FPTAS. O(\( n/\xi^2\)) FPTAS

Undirected graph G(V, E) Find a subset VI C V such that if (4, v) is an edge of Gi, then either uev' or vev' or both. Find a V' so V' is minimum.

## Approx - Vertex - lover

C <- \$ E' LE while E' + \$ Pick (U,V) E E arbitrarily C - C U {u} U {v} Delete from E' all edges incident on U or V

Return C

Runs in polytime. Produces a vertex cover. How close to optimal?

Approx-Vertex-lover could pick (b,c), (e,f), (d,g) C = {b, c, d, e, f, g} |C| = 6 Optimal solution Copt = {b,d,e} |(opt|=3

Approx-Vertex-Lover is a 2-approximation algorithm

Proof: Let A denote the edges that are picked. Optimal cover Copt must include at least one endpoint of each edge in A (and other edges) No two edges in A share an endpoint. |A| is a lower bound for | Copt|, |Copt| > |A| Number of vertices in C = 2/A 1 C| < 2 | Copt |

#### Set-lover

Given a set X and a family of (possibly overlapping) subsets  $S_1, S_2, \dots, S_m \subseteq X$  such that  $S_i = X$ , find  $C \subseteq \{1, 2, \dots m\}$   $S_i = X$ , find  $S_i = X$ , while minimizing |C|.

Such that  $US_i = X$ , while minimizing |C|.

Approx- Set-lover (on next page) selects S1, S4, S5, S3 in that order Optimal: S3, S4, S5

Approx - Set - Cover While elements in X remain |X| = nPick largest Si; C= C V {i} Remove all elements in Si from X and other Si Poly time, returns a cover Return C Approx-Set-lover is a (ln(n)+1)-approximation algo Proof: Assume there is a cover Copt |Copt|=t Let  $X_k$  be set of elements in iteration k  $(X_0 = X)$ The them covers at least IXA elements.

The algo picks a set of (current) \$1720 > [XK]

The algo picks a set of (current) \$1700 > [XK]  $\Rightarrow$   $\forall k | | | | | | | | | | | | | | | | | |$ More careful analysis (see CLRS, (h 35) relates
((n) to harmonic numbers. t should shrink!

Approximation ratio gets worse for larger problems.

Set S of n items with weights Si,...Sn WLOG S1 7, S2 7, ... 7, Sn Assume Partition into A and B to minimize max (\( \leq \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ w(A) Define 2L =  $\frac{2}{i}$ Si = w(s) Optimum solution > L. Note: 2-approx algo trivial. Want a PTAS. (1+E) -approximation (FPTAS also exist)
for this problem)

Define 
$$m = \begin{bmatrix} 1 \\ \epsilon \end{bmatrix} - 1$$
 $\epsilon \approx m+1$ 

Second phase: 
$$A \leftarrow A'$$
  $B \leftarrow B'$   
for  $i = m+1$  to  $n$   
\nif  $w(A) \leq w(B)$   
 $A = A \cup \{i\}$ 

#### APPROX-PARTITION IS PTAS.

WLOG, assume w(A) >, w(B) approximation ratio = W(A)

|   | C     |
|---|-------|
| A | // 3k |
| A |       |
|   |       |

k is the LAST ifem added to A.

Could have been added in first or second phase.

- 1) k is added to A in first phase. This means A = A'. We have an optimal partition
  - since we can't do better than w(A') when we have ny, m items, and we know w(A') is optimal
- for the m items. 2) k is added to A in second phase.

We know  $w(A) - Sk \leq w(B)$ 

This is why k was added to A. (Note w/B) may have mirrored after this addition to A).

 $\Rightarrow$   $w(A) - Sk \leq 2L - w(A)$  w(A) + w(B) = 2L

 $\Rightarrow w(A) \leq L + \frac{Sk}{2}$ 

Since Si >, Sz ... >, Sn We can say that S1, S2, .. Sm all 7, Sk

2L 7/ (m+1) Sk since k>m.

 $w(A) \leq L + Sk/2 = 1 + \frac{Sk}{2L} \leq 1 + \frac{Sk}{(m+1)Sk}$ 

= 1 + m+1

## Approx - Vertex\_ Cover\_ Natural


C = P E' \( \) E While E' \( \neq \)

pick v with maximum degree

pick v with maximum degree

C = C V \( \neq \varphi \)

Remove v and all incident edges from E'

Remove v and all incident edges from E'

=> m. logla vertex cover.

Smaller than Zdi

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| Pa | ram | ete           | Kin             | $\mathcal{A}$ | pro         | الطو     | em         | =          | orol      | sleu | n 4        | t p            | ara  | met     | er           |      |     |      |   |
|----|-----|---------------|-----------------|---------------|-------------|----------|------------|------------|-----------|------|------------|----------------|------|---------|--------------|------|-----|------|---|
|    |     | _             |                 |               | <b>V</b>    | (        | pro        | sble       | m         | wit  | <i>it.</i> | Po             | rav  | nete    | 2 ()<br>2 () |      |     |      |   |
|    | (   | oten          | ntia            | lly           | Ma          | NY       | inte       | ves        | ling      | POU  | OIM        | eter           | iZa  | tion    | 5)           |      |     |      |   |
|    |     |               |                 | -             |             |          |            |            |           |      |            |                |      |         |              |      |     |      |   |
| G  | oal | ) :           | 00              | lyi           | JOW         | rial     | (          | ìh         | PY        | do   | ler        | h S            | siz  | er<br>k | ١,           |      |     |      |   |
|    |     |               | ex              | D0            | nes         | tia      | L          | in         | P         | aro  | rme        | eter           | -    | k       |              |      |     |      |   |
|    |     |               |                 | 1             |             |          |            |            | 1         |      |            |                |      |         |              |      |     |      |   |
| EX | (an | nol           | e:              | k             | (- V        | ert      | tex        | (          | _<br>_O\/ | ev   |            | (              | NP   | -ha     | ird          | )    |     |      |   |
|    | Gi  | ven           | -<br>•<br>•     | gra           | ph          | G        | -=(        | V,E        |           | No   | mn         | e90            | tive | iv      | itea         | er   | k   |      |   |
|    | G   | ) !           | is              | H             | here        | 2 0      | l 5        | et         | Ś         | of   | . <        | ≤k             | ٧    | ert     | ice          | 5    |     |      |   |
|    | -   |               | the             | at            | ``C         | DV/6     | ers        | '' 0       | W         | ed   | 20:        | 5;             | Ac   | eE      | J            | ,eS  | ne  | ,    |   |
|    | Pa  | ram           | ete             | r:            | k           |          |            |            |           | - 6  | 7          |                |      |         |              |      |     |      |   |
|    |     |               |                 |               |             |          |            |            |           |      |            |                |      |         |              |      |     |      |   |
|    | Νà  | ste           |                 | C             | an          | V        | ιοV        | 6          | k         | <<   | IV         | <b> </b> :     |      |         | C            | 美    | _   |      |   |
|    |     |               |                 |               |             |          |            |            |           |      |            |                |      | 50      | 8            | 7)   | 6   | 5    | 0 |
|    | Br  | ute           | <del>-</del> {c | VCE           | 2 5         | solu     | itio       | <u>ኢ</u> ኒ | (B        | AD   |            |                |      |         |              |      |     |      |   |
|    |     |               | try             | q             | 00          | (V<br>k  | )+(        | (V)<br>k-1 | )+ ·      | +(   | (V)        | se             | ts   | of s    | ≤k           | ٧χ   | 5   |      |   |
|    |     |               | 0               |               |             |          |            |            |           |      |            |                |      | ette    |              |      |     |      |   |
|    |     |               | tes             | ;†            | CoV         | eva      | 9C         | ìn         | 0         | (m)  | +          | ime            | (    | n=#     | edo          | es)  |     |      |   |
|    |     | $\Rightarrow$ | 0               | (1)           | ΚÈ          | )        | tin        | 16         |           |      |            |                |      |         | O            |      |     |      |   |
|    |     |               |                 |               | ولمان       | ,        |            |            | dr<br>Or  | fix  | ed         | K              |      |         |              |      |     |      |   |
|    |     |               | _               | -b            | ut          | no       | t &        | Soum       | e i       | oly  | non        | nial           | ] _  | -eg     | }. n         | at ( | O(v | 100) |   |
|    |     |               | _               | - il          | neff        | Sicie    | ent        | în         | m         | ost  | ca         | ses            |      | 0       |              |      |     | ,    |   |
|    |     |               | _               | ) (           | neft<br>let | n<br>The | <b>9</b> _ | nf         | (k)       | to   | h          | e <sup>1</sup> | BAD  |         |              |      |     |      |   |
|    |     |               |                 |               |             |          |            |            |           | re   |            |                |      |         |              |      |     |      |   |
|    |     |               |                 |               |             |          |            |            | 700       |      |            |                |      |         |              |      |     |      |   |

general technique Bounded search-tree algorithm: (Good) - pick arbitrary edge e=(u,v) - know that either uES or VES (or both) but don't know which guess: try both possibilities

(1) add u to 5 delete u & incident edges from G recurse with k'=k-1' a ditto with v instead of u - return OR of two outcomes - like guessing in dynamic programming, but memoization doesn't help here - recursion tree: u' (u'.v') | (u'',v'') | '' - at leaf (k=0): return IEI = 0 - O(V) time to delete u or v  $\Rightarrow$   $O(2^{K} \cdot V)$  time - O(V) for fixed k -degree of polynomial independent of k - also polynomial for k= O(lg V)
- practical for e.g. k ≤ 32
- define f(k)·n(1) to be Good

| F | PT:      | P   | ara             | me  | teri       | 200                 | l (         | oral     | bler   | n       | ìs             | f          | ixe       | <u>d-</u> p | ara              | ame                     | ter         | -    |   |
|---|----------|-----|-----------------|-----|------------|---------------------|-------------|----------|--------|---------|----------------|------------|-----------|-------------|------------------|-------------------------|-------------|------|---|
|   |          | 7   | rac             | tal | <u>ble</u> | $\mathcal{C}$       | FP          | T)       | īt     |         | the            | re         | īS        | ai          | 1                | alg                     | ori         | Hum  |   |
|   |          | h   | ith             | ۲   | unr        | ing                 | +           | ime      |        | #(      | k)r            | ),<br>O(1  | 7         | <b>S</b> _  | n                | ſ                       | ,           | 0    |   |
|   |          |     |                 |     |            | (Na<br><del>[</del> | V-)<br>nneg | W.       |        | Par     | ame            | eter       |           | Tino        | lep.             | 70                      | K           | ž n  |   |
|   |          |     |                 |     |            |                     |             | <u> </u> |        |         |                |            |           |             |                  |                         |             |      |   |
| ( | ડ્રો ૧૯૬ | +1  | Ωn;             | ١٨  | ماملا      | +                   | 7k)         | ) · w    | 0(1)   | ) (     | tan            | f          | γk\       | ۱+          | 0                | (1)                     | ?           |      |   |
|   |          |     |                 |     |            |                     |             |          |        |         |                |            |           |             |                  |                         |             |      |   |
| T | heo      | rev | n:              | 3.  | flk        | ). N                | C (         | alg      | orit   | hm      | بخ             | )<br>)     | ]f        | (k)         | t n <sup>c</sup> | - ' C                   | ilgo        | rill | m |
|   |          |     |                 |     |            |                     |             |          |        |         |                |            |           |             |                  |                         |             |      |   |
| F | root     | [;  | $(\not \subset$ | ) . | tri        | Vìa                 | y c         | (a       | ssu    | mik     | 19 0           | +(         | k)        | & v         | )<br>(()         | $\geq 1$                | )           |      |   |
|   |          |     | (⇒              | )   | ît<br>C    | M:                  | < (I        | (k)      | +h     | en      | <del>(</del> ) | (k)        | , N       | \ <u>\{</u> | +(1              | د) <sup>ر</sup> ۲<br>۲) | T           |      |   |
|   |          |     |                 |     | 1†         | t(1                 | () S        | h<br>C   | th     | en      | f              | K).        | N<br>1.1c | +1          | N                | 412                     |             |      |   |
|   |          |     |                 |     | 50         | t                   | (K)         | N.       | \ \ \  | M       | ľ/c<br>γ× .    | { †(<br>+1 | K) -      | Ct          | n 1              |                         | <b>&gt;</b> | D    |   |
|   |          |     |                 |     |            |                     |             |          | 2      | tl      |                |            | , A       | C           | <u>,</u>         |                         |             | و    |   |
|   |          |     | ٥               | R:  | 7          | Ų                   | ۷ .         | χą.      | +49    | †<br> - | (              | r(k        | )= -      | f/k         | 19               | 2                       | -/=         | 20   |   |
|   |          |     |                 |     |            |                     |             |          | _      |         |                |            |           |             |                  |                         |             |      |   |
| E | XQ       | mp  | le:             |     | 00         | $a^k$               | $\sim$      |          | $\leq$ |         | 0(             | yk         | +         | Ng,         | )                |                         |             |      |   |
|   |          |     |                 |     |            |                     |             |          |        |         |                |            |           |             |                  |                         |             |      |   |
|   |          |     |                 |     |            |                     |             |          |        |         |                |            |           |             |                  |                         |             |      |   |
|   |          |     |                 |     |            |                     |             |          |        |         |                |            |           |             |                  |                         |             |      |   |
|   |          |     |                 |     |            |                     |             |          |        |         |                |            |           |             |                  |                         |             |      |   |

|               |      |               |          |                  |             |          |            |               |          |            |             |              |             | 4           |                 |                   |          |
|---------------|------|---------------|----------|------------------|-------------|----------|------------|---------------|----------|------------|-------------|--------------|-------------|-------------|-----------------|-------------------|----------|
| Kern          | eli  | zat           | ion:     |                  | α 5         | sim      | slif       | yih           | 9        | Sel        | 2f-         | rec          | luc         | tio         | n               |                   |          |
|               | pol  | yno           | mio      | <b>U</b> -1      | time        | 2 0      | ilgi       | 5 ( i         | thu      | η (        | CON         | Ver          | rtiv        | 19          | 1 /             | 1 1               |          |
|               | inp  | ut            | (x       | <b>,</b> k)      | ìV          | ito      | SV         | nal           | X e      | qui        | Val         | ent          | īl          | rpu         | 1 (             | x` <sub>1</sub> k |          |
|               |      |               | 17       | 5                | HLK         | .)       | <b>(</b>   |               |          | <i>ڪ</i> ه | NSh         | verl         | <b>X</b> ): | =av         | rSW             | <b>e</b> r ( 2    | く)       |
| Theo          | rem  | 2.            | FP       | TE               | €           | 1E       | cer        | ne!           | Lí Z     | ati        | <b>S</b> 11 |              |             |             |                 |                   |          |
| Proof         | · (  | (ک            | ke       | MAP              | 170         |          | <b>∋</b> 1 | ^<br>ک        | f(       | (k)        |             |              |             |             |                 |                   |          |
| Proof         |      |               | Υu       | n                | XMY         | Fi       | nit        | e             | g(n)     | ()         | lgo         | <b>5</b> VI. | Hm          |             |                 |                   |          |
|               |      |               | <u> </u> | N <sub>Q</sub> ( | 1) 4        | 9(       | f(I        | <))           | +        | îme        |             | •            |             |             |                 |                   |          |
|               |      |               |          |                  |             |          |            | <i>?(</i> (   | C        |            | Λ           | //           | 1           |             |                 |                   |          |
|               |      | $\Rightarrow$ | le       | t P              | be          | a<br>n 1 | n t        | (K)<br>1      | ·h       | a          | lgo         | ritl         | ım          | Λ           |                 | )                 |          |
|               |      |               | 1:0      | n                | ≤ t         | (K)      | 1          | hen           | a        | lre        | ady         | K            | en          | <i>eli</i>  | <del>2</del> eq |                   |          |
| 0,550         | ımih | G             | ) IT     | 70               | () <u> </u> | ν·<br>•  | ] -        | <b>&gt;</b> 1 | f(k)     | . 10       | · ·         | 'n           | +1          | 4700        | 0               |                   |          |
| CUSSU<br>K is | Kno  | SWh           |          | _                | aut         | nut      | Ŷ          | 1)-           | Siz      | e          | YES,        | /NO          | in          | sta         | nce             |                   |          |
|               |      |               |          |                  | out         | as       | 5 6        | LPPY          | dpr      | iate       | 2           | to           | keri        | nel         | ize)            |                   |          |
|               |      |               |          |                  |             |          |            |               |          |            |             |              |             |             |                 |                   |          |
|               |      |               | it       | k<br>Li          | is          | unk      | (NOI       | Wh:           | YU       | IN         | A           | for          | r           | C+3         | t ti            | me                |          |
|               |      |               |          | A in             | N           | ot (     | don        | Q n           | Kno      | ςW         | alv         | رون          | ly          | kerv        | reli            | Zed               | П        |
| 5. 1          | r    |               | J - 1    |                  |             | Λ        |            | . 1           |          | n          |             | 1            |             | 1           |                 |                   | _/_      |
| So (find      | exp  | SNEA          | ntia     | (L)              | Ken         | Vez      | (A)        | 1513          | را<br>2، | Ke         | cer         | ۸l<br>       | مار         | YK          | ai              | ms<br>:<br>ch(    | אר<br>אר |
| ) ING         | hox  | yvvo'         | rn(i (XX | - (              | 214         | 1 L      | IN(C)      | W)            |          | CI N       | ex.         | ) U          | N NIA       | <b>//</b> ( | μ.              | 10101             | (K.      |
|               |      |               |          |                  |             |          |            |               |          |            |             |              |             |             |                 |                   |          |

| Pol | lyr           | m        | jal            | <    | eri      | vej      | _        | for              | - (         | ٧-١      | ver  | tex           |         | 0V6                 | er:      |                   |                                              |            |   |
|-----|---------------|----------|----------------|------|----------|----------|----------|------------------|-------------|----------|------|---------------|---------|---------------------|----------|-------------------|----------------------------------------------|------------|---|
|     |               |          |                | gv   |          |          |          |                  |             |          |      |               |         |                     |          |                   |                                              |            |   |
|     |               | _        | - 17           | em   | 016<br>1 | Ø        | OOP      | 5 (              | g           | L        | mu.  | Sti-          | -ed     | lges                | 5        | <b>⊘</b>          | •                                            |            |   |
|     |               |          |                |      | 4        |          |          |                  |             |          |      |               | 7 1     | _                   |          | Co                |                                              | -          |   |
|     |               |          |                |      |          |          |          |                  |             |          |      |               |         |                     |          | ed                |                                              |            |   |
|     |               |          |                |      |          |          |          |                  |             |          |      |               |         |                     |          | dg                |                                              |            |   |
|     |               |          |                |      |          | •        |          | _ ^              | J           |          | -    |               |         |                     |          |                   | _                                            |            |   |
|     | $\Rightarrow$ | (C)      | MO-            |      | 0        |          | 201.     | عن<br>لم         | nc          | lan      | n v  | 1             | on va   | 00                  | < L      | ngl               | 7                                            |            |   |
|     | ⇒             | 00       |                | 100  | 9        | 7        | spn      | A) (C            |             | M        | tos. |               |         | <i>(C</i>           | - K      | 0                 | oloos                                        |            |   |
|     | <u> </u>      | £        | JI             | V 64 | mai      | ning     |          | عوں<br>امم       | er<br>      | Ver      | 16   | $\mathcal{L}$ | ove     | <b>1</b>            | = F      | < Q               | χ <b>γ</b> ες<br>Λ                           | )<br>In '  |   |
|     | 7             | 11       | T <del>T</del> | 10   | ma<br>+  | ini      | 19       | ear              | 9es         | ح ز      | K.   | 1             | ran     | 2Me                 |          | īS                | / )                                          | ان.<br>الم |   |
|     |               | <u> </u> | OU             | IPU  | 11<br>-/ | cai      | S<br>NOV | 1100             | W.          | NC       | ) )  | ns            | Ian     | œ                   | •        | •                 | ,                                            | $\mu_{-}$  |   |
|     | —(            | SKE      | se             | lt   | こし       |          | 1        |                  |             | 1.       |      |               |         |                     |          |                   |                                              |            |   |
|     | _             | rei      | nov<br>Ul      | e .  | 150      | lat<br>I | es)      | V                | er          | tice     | 5    |               |         |                     |          |                   |                                              |            |   |
|     |               | 17       |                | ے ک  | ZK'      |          | 4        | _                |             | <i>(</i> | I —  | $\lambda$     |         |                     |          | X                 | (l.2                                         |            |   |
|     |               | re       | du             | ced  | 1        | ī O      | ns1      | and              | e           | CV       | 、に   | )<br>1        | 01      | Si                  | Ze       | 0                 | CK                                           | )          |   |
|     |               |          | _              |      | 1.       |          |          | <b>A</b> (.      |             | 9        | uad  | lrat          | ic      | Ke                  | rue      | V                 |                                              |            |   |
|     | _             | ru       | nnī            | ng   | +7       | me       | ; (      | $\tilde{\Omega}$ | NE          | ) (      | 661  | 110           | 45,     |                     |          | S)<br>Wa          |                                              |            |   |
|     |               |          |                |      |          |          | (        | O(               | <b>V</b> +' | ヒ)       | W    | ith           | n       | nor                 | <b>e</b> | WC                | 3VK                                          |            |   |
|     | _             | it       | We             | ν    | 10 C     | ) (      | rpp      | ly:              |             |          | _    | •             |         |                     | -\\L     | ·                 |                                              |            |   |
|     |               | _        | bro            | ite. | -tou     | rce      | 5        | slut             | ion         | =>       | 0    | (V+           | Et      | (A                  | ( )      | WC<br>K+2<br>2k+2 | <u>)                                    </u> | _          |   |
|     |               |          |                |      | <b>A</b> |          |          |                  |             | =        | O    | (V+           | -E ·    | + 2'                | kk'      | xk+d              | ) -                                          | fime       | _ |
|     |               |          | pa             | und  | ed       | sea      | avel     | n-ti             | æe          | 50<br>(\ | sli  | tion          | ١       |                     |          |                   |                                              |            |   |
|     |               |          |                |      |          |          |          | 3                | <b>)</b>    | 0(1      | /+ E | + 6           | $2^k k$ | $\langle z \rangle$ | ti       | nl                |                                              |            |   |
|     |               |          |                |      |          |          |          |                  |             |          |      |               |         |                     |          |                   |                                              |            |   |
|     | Be            | st       | _0             | lgi  | sri      | the      | n ·      | to               | d           | ate      | );   | 0             | (k)     | V+                  | 1.       | 27                | 14K                                          |            |   |
|     | •             |          |                | 1    | Ch       | en.      | K        | ani              | , )         | Lia      | _    | TC            | Si      | 201                 | 07       | 27                |                                              | -          |   |
|     |               |          |                |      |          | -        | •        |                  |             |          |      |               |         |                     | J        |                   |                                              |            |   |

| C         | DIMM | ود         | tion       | ١ -         | to     | ap        | pYa   | Xì   | nai      | tion     | ુલ.     | <u> </u> | rith                | ms      | :          |          |           |                   |    |
|-----------|------|------------|------------|-------------|--------|-----------|-------|------|----------|----------|---------|----------|---------------------|---------|------------|----------|-----------|-------------------|----|
|           | _    | to         | ke         | 0           | pti    | —1<br>Mi2 | ati   | on   | F        | rol      | lei     | ma       | int                 | egy     | al         | Of       | 77        |                   |    |
|           |      | Co         | nsi        | dei         |        | ass       | 50C   | ate  | d'       | dea      | cisi    | m        | Pn                  | ble     | m:         | Ĉ        | PT        | <b>\( \lambda</b> | k? |
|           |      |            | ran        | h h         |        |           | · •   | 1    |          |          |         |          |                     |         |            |          |           |                   | •  |
|           |      | V          |            | _           |        |           | 0     |      |          |          |         |          |                     |         |            |          |           |                   |    |
| Th        | ഭര   | ren        | h.         | <b>∆</b> ຄົ | tim    | ī70       | tion  | h a  | prob     | ler      | n l     | nas      | E                   | PTA     | 5          |          |           |                   |    |
| \ <u></u> |      |            |            | 4           |        |           |       | Y    | (        | offi     | cien    | t        | PTA                 | 5:      | fl         | 1/2)     | ·n        | )(1)              |    |
|           |      |            |            |             |        |           |       |      | 6        | 2.9      | Ap      | prax     | c-Pa                | ortit   | īm         | ΓĹ       | 17]       |                   |    |
|           |      | ·          | <b>⇒</b> > | de          | eci?   | TON       | Œ     | orak |          |          |         | FP       |                     |         | ion        |          |           | ,                 |    |
| Pr        | too  |            |            |             |        |           |       |      |          |          |         | a        |                     | )       |            |          |           |                   |    |
|           |      | - S(       | ري.<br>اور | m           | αXi    | mi        | zat   | מתנ  | E        | enl      | De      | n        | 12                  | ,<br>≤k | . D        | orig     | جزي<br>حي |                   |    |
|           | -    | - m        | 110        | E           | TA     | 5         | britt | 7    | ر<br>ج ج | 1/       | )<br>)k | ir       | \ \f                | 1/2k    | ()         | 00       | 1)        | ,                 |    |
|           |      |            | elai       |             |        |           |       |      |          |          |         |          |                     |         |            |          |           |                   |    |
|           | =    | ) a        | bso        | lut         | 2 6    | ox Y      | or'   | <    | 1        | if       | (       | SPT      | ≤k                  |         |            |          |           |                   |    |
|           |      | · \$0      | , ,        | f           | 1210   | 4         | End!  | <    | مالم     | tim      | _       | wift     | <i> </i><br>  \ \ \ | allu    | 2 <        | k        |           |                   |    |
|           |      | H          | 201        | · (         | DP7    | -<br>_    | /1    | + 1  | /sk      | ).       | k s     | ≤k       | + 1                 | /2      | _          |          |           |                   |    |
|           |      |            |            | -           | nte    | 986       | 0 =   | ⇒′,  | SP       | ,<br>Γ ≤ | k       | ≤ k<br>⇒ | У                   | ES.     |            |          |           |                   |    |
|           |      | el         | 100        | (           | SPT    | 7         | k     |      |          |          |         |          | ·                   |         |            | U        |           |                   |    |
|           |      |            |            |             |        |           |       |      |          |          |         |          |                     |         |            |          |           |                   |    |
| Al        | 150  | •          | =,         | ۷.          | >      | C         | leci  | sio  | n        | PN       | sbla    | 2ms      | a                   | re      |            |          |           |                   |    |
|           |      |            | 9          | ιīVα        | les    | J<br>N    | h/.   | rt   |          | FP       | T       | ms       |                     |         |            |          |           |                   |    |
|           |      |            | 9.         |             |        | •         |       |      |          |          |         |          |                     |         |            |          |           |                   |    |
| ~         | ~ (  | $\sim$     | 10         | 1a          | SO     | +         | his   |      | rol      | )at      | T ON    | 1        | እ                   | Фr      | <b>か</b> / | 6        |           |                   |    |
|           | ţ    |            | TA         | \<br>\{C    | ے<br>م | la        | 4     | e)   | (151     |          | h       | 507      | ml                  | 1       | 705        | -<br>P ( |           |                   |    |
|           | •    | <b>-</b> \ | , , (      | <b>J</b> 3  |        | ~\\n      | ,     |      |          |          |         | . ن      |                     |         | ے میں      | へゝ       |           |                   |    |
|           |      |            |            |             |        |           |       |      |          |          |         |          |                     |         |            |          |           |                   |    |

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

Intro to Cryptography: Hashing (Part I of II)

Hash functions

Random oracle model

Random oracle model

Desirable froperties

Applications to Security

Hash Functions

A hash function maps arbitrary

Strings of data to fixedlength

Strings of data to fixedlength

output in deterministic, public,

output in manner.

h: {0,13\* -> {0,13dd strings of arbitrary strings of length 70 length d

No secret key. All operations public.

Anyone can compute h, polytime computation

Examples: MD4, MD5, SHA-1, SHA-256, SHA-512

Examples: MD4, MD5, SHA-1, SHA-256, SHA-512

broken (CR): 26 237 269

Ideal: Random Oracle (not achievable in practice)

Oracle: On input  $x \in \{0, 19^n\}$ If x not in book

flip coin d times to determine h(x)record (x, h(x)) in book
\nelse: return y where  $(x, y) \in book$ 

hiver random answer every time, except as negliwied for consistency with previous answers. (h must be deterministic) answers. (h must be deterministic)

In practice, \$\frac{1}{2}\$ RO so need something pseudo random

Desirable Properties OW () "one-way" (pre-image resistance)

Infersible, given y Ex {0,1}d to

find any x s.t. h(x) = y

\*pre-image" of y (2) Collision-resistance (strong collision resistance) In feasible to find x, x', s.t. x \neq x' and h(x) = h(x') (a "collision") TCR (3) Week collision resistance (target CR) Infeasible given x, to find  $x' \neq x$  s.t. h(x) = h(x')(4) Pseudo-randomness Behavior industinguis hable from RO (5) Non-malleability In feasible, given h(x), to produce h(x') where x and x' are "related" (e.g. x' = x+1) Informal definitions. Formal requires family


hy CR > his TCR (but not reverse)

h is OW > his CR, TCR (neither impl.

h is OW > holds)

Collisions can be found in O(2d/2) - birthday attack

Inversion can be found in O(2d)

Examples

 $\begin{array}{c} X_1 \\ X_2 \\ X_3 \\ X_n \end{array} \begin{array}{c} \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\ \\$ 

h(x) is OW, CR h'(a,b, X2,..Xn) Is still OW, but not TCR

 $h'(x) = \begin{cases} 0 | 1 \times f(x) \leq n \\ 1 | 1 h(x) \text{ otherwise.} \end{cases}$  his Ow, CR, but h' is TCR, not OW TCR  $\Rightarrow$  OW

## Applications

(5)

- 1) Password storage
  - Store h(PW), not PW, on computer

     Vice h(PW) to compare against h(PW')

     Vice h(PW) to the typed password

    where PW' is the typed password

    Where PW' is the typed password

    Need OW.
- 2) File modification detector
  - For each file F, store h(F) securely (on DVD)
  - check if F modified by recomputing h(F)
  - heed TCR (adversary wants to charge F but not h(F))
- 3 Digetal signatures PKA: Alice's Public key

  SKA = Alice's Private key

Signing:  $\sigma = sign(sK_A, M)$ Verify: verify(M,  $\sigma$ , PKA) = true/false

Adversary wants to forge a signature that verifies

For large M, easier to sign h (M) = sign (ska, h/m))

Need CR, don't need OW. Alice gets Bob to sign x, then

Need CR, don't need OW. claims he signed x', if (h(x) = h(x))

## Applications (contd.)

Commitments 4 (e.g., auction bid) Alice has value x Alice then computes ((x) and submits it as her bid (&) is her "sealed bud" When bidding is over, Alice "opens" (Cx) to reveal X Binding: Alice should not be able to open ((x) in multiple ways. Secrecy: Auctioneer seeing (x) should not learn anything about x

NM: Given ((x) shouldn't be possible to produce ((x+1)) NM, CR, OW (really need more for secrety!)

h(x) = h(x) 11 msb(x) Need:  $((x) = h(r | | x) r \in_{\mathbb{R}} \{0, 1\}^{256}$ How: to open reveal r & X

randomized

This could be ow but expose most significant bit and breek secrey! 6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

- Symmetric key Encryption

- Key Exchange

- Asymmetric key encryption

- RSA

- NP- complete problems & cryptography

- graph coloring

- knapsack.

Symmetric Key Encryption Ciphertext encryption function decryption function m = dk (c) permute l'reverse-permute reversible operations (+) +/-, shift left/right Symmetric algos: AES, RC5, DES

# Key Management Question

How does secret key k get exchanged/shared?

| Alice PIRATES                                                                                                                                                     | Bob Boxes                                       |
|-------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------------------------------------------|
| Boxes<br>Locks<br>Keys                                                                                                                                            | Locks                                           |
| Pirates won't touch locked box, be away keys, messages in unlocked amay keys, messages in unlocked toward does Alice send a message (without pirates knowing what | ut will take d box(es) ge to Bob?  ye was sent) |

Alice puts in in box, locks it with KA Solution: 7 Box sent to Bob Bob locks box with K13 Box sent to Alice Alice unlocks KA Box sent to Bob Bob unlocks KB, reads m! Lock KA, Lock KB,

Commutative locks! remove KA, remove KB

### Diffre-Hellman Key Exchange

finite field (mod p, aprime) \* means invertible elements only {1,2,...p-13 G= Fp g public p public 2 ≤ 9 ≤ P-2 Alice 1 ≤ a, b ≤ p-2.

Select a Compute ga → ga Select b Compute 9 b 96

(gb) a mod p = K Alice can compute Bob can compute (ga) b mod p = K

Assumes Discrete Log Problem is hard. Given ga, gb compute

Diffie Hellman Problem is hard. Given ga, gb compute

Man-in-the-middle

doesn't know she is communicating with Bob. agrees to a key with Eve (thinks she is Bob) agrees to a key with Eve (thinks she is Alice) see all communications can Eve

Message + public key = (iphertext

(iphertext + private key = Message

Two keys need to be linked in a methemetical way

Knowing the public key should tell you nothing

knowing the private key.

Alice picks two large secret primes P & V. Alice computes N = P.Vwhich satisfies Chooses an encryption exponent e e=3,17,65537 gcd (e, (p-1)(g/-1)) = 1 Alice public beg = (N, e) Decryption exponent obtained noisy Extended Enclidean Algorithm e. d = 1 (mod (p-1)(qv-1)) Alice private bey = (d, p, q) not alsolutely necessary, only for efficiency

#### ENCRYPTION & DECRYPTION WITH RSA

Why it works

Since ed = 1 (mod \$) there exists an integer k such that ed = 1+ kp

Two cases:

Two cases:

By Fermat's theorem

$$m^{P-1} \equiv 1 \pmod{p}$$

$$m^{P-1} \equiv 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

$$m^{P-1} = 1 \pmod{p}$$

2)  $gcd(m,p) = P \quad m \mod p = 0$ frivial case med = m

on in both cases  $med \equiv m \pmod{p}$   $med \equiv m \pmod{q}$   $med \equiv m \pmod{q}$ Since  $p \notin q$  are distinct primes  $med \equiv m \pmod{N}$   $med \equiv m \pmod{N}$   $med \equiv m \pmod{N}$   $med \equiv m \pmod{N}$ 

#### HARDNESS OF RSA

NP-complete

- Given N, hard to factor into p, 9/
- 2) hiven e such that gcd (e, (p-1)(y-1)) = 1 and C, find m such that me = c (mod N)

## NP- Completeness

unknown if NP-complete Is N composite? ENP with a factor within a range

Is a graph k-colorable? NP-complete

Assign & colors to each vertex
such that no two vertices connected not 3-colorable
by an edge share the same color

Given a pile of n ctems, each with different weights. Wi, is it possible to put items in a knapsack such that we get a speafie weight S?

S= b1 W1 + b2 W2 + - bn Wn?

NP- completeness & Cryptography NP- complete ness: about worst-case complexity
(ryptography: want a problem instance, with
suitably chosen paremeters that\nis hard on average. Most Knaplack cryptosystems have failed. Determiny y a graph is 3-colorable is NP-complete But very easy on average, because average graph, beyond a certain Size, is not 3-10/orable! Consider standard backfracky search to determine 3-10lorability.

Order vertices Vi,... Vt. (olors = {1,2,3})

Traverse graph in order of vertices

Traverse graph in order of vertices

On visity a vertex, choose smallest possible color

that "works". that "works" stuck, backfrack to previous

If you get stuck, backfrack to previous

choice, and try next choice

choice, and try next choice

Run out of colors for 1st vertex -> NOT

Successfully color last vertex -> YES.

Random graph of t vertices, average number vertices traveled < 197, REGARDLESS of t!

NP-complete henerel knapsack problem: linear time solvable Super-increeding knapsacks:

W; > 15 wi
\ni=1 {2, 3, 6, 13, 27, 52}

Merkle Hellman Cryptosystem:

Private bey -> Super increesing knepsack problem

Private bey -> Super increesing knepsack problem

Private bey -- "hard" general knapsack problem Transform: two private integers N, M s.t. gcd(N, M)=1 Multiply all values in the sequence by N, and then mod M.

N=31, M=105 private key = {2,3,6,13,27,523} public key = {62, 93,81,88,102,373.

Message = 011000 110101 101110 93+81 = 174 011000 Ciphertext: 62+93+88+37=280110101 62+81+88 + 102 = 333 101110 = 174, 280, 333 Recipient knows N= 31, M=105 {2,3,6,13,27,523 Multiplies each uphentest block by N-1 (mod M) N-1 = 61 (mod 105) 174.61 = 9 = 3+6 = 011000280.61 = 70 = 2+3+13+52 = 110101333.61 = 48 = 2 + 6 + 13 + 27 = 101110

Lattice based techniques breek this scheme.

Density of knapsack  $d = \frac{n}{\max \{ \log_2 w_i : 1 \le i \le n \}}$ Lattice basis reduction can solve knapsacks of low density. Unfortunately M-H scheme always produces knapsacks of low density!

Ton average, easy to solve!

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

|    | 6.  | ٥u              | t6           |          |     |     | Le  | ctu  | ive | ک    | 3        |     | $\wedge$ | lay             | 1   | 2.  | 20  | 15  |      |   |
|----|-----|-----------------|--------------|----------|-----|-----|-----|------|-----|------|----------|-----|----------|-----------------|-----|-----|-----|-----|------|---|
| To | DDA | <del>1</del> 7; | (            | Co       | ch  | c – | ob  | Riv  | iou | S    | al       | 90r | ith      | .MS             | : 1 | - ( | of  | 2)  |      |   |
|    |     | me              | mo           | svy      | 0   | rie | rar | ch   | J   |      | · ·      | 1   |          | 1 /             | )   |     |     | nod | n () |   |
|    |     | ex              | ter          | no       | K I | me  | mo  | ry   | V   | 5.   | Ca       | Cho | 2 (      | sb <sup>x</sup> | ivi | ous | s r | Nod | lexs | • |
|    | -   | div             | ani<br>It De | o<br>Min | 9   | CO  | nOl | 10 V |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     | SC<br>div       | M            | ed       | ian | 4   | ind | lino |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     | _               | <b>/</b> ^   | caty     | īΧ  | m   | ult | ipl  | ica | tion | 1        |     |          |                 |     |     |     |     |      |   |
|    | ~   | LR              | U            | 69       | loc | k   | rep | plac | en  | reni | <b>†</b> |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 | •   |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |
|    |     |                 |              |          |     |     |     |      |     |      |          |     |          |                 |     |     |     |     |      |   |

So far we've viewed all word operations & all memory accesses as equal cost... Modern memory hierarchy: CPU-LI-LZ-LY-Main Flash Disk sisters) (Haswell) Memory Flash Disk ~ 10K 100K MBs 100MB GBS-TB 100GB-TBs TBS-PB (registers) ~ ns 10ns 10ns 100ns us 10-100ms 10ms > bigger but slower latency: distance travel & physical seek on disk - bandwidth usually matched (RAID etc.) - blocking to mitigate latency: - when tetching a word of data, get entire block containing it - idea: amortize latency over whole block => amortized cost per word = latency + 1 block Size, bandwidth set roughly equal via block size to work, we need algorithms to use all elements in a block (spatial locality) & re-use blocks in cache (temporal locality

| Di          | VĩC           | le               | &       | Cor               | 1gu        | er      | Q1        | ppr      | <u> </u> | <u>ch</u> : | _             | <b>→</b> (                             | ac           | he         | ob       | livi          | JUS      |            |       |
|-------------|---------------|------------------|---------|-------------------|------------|---------|-----------|----------|----------|-------------|---------------|----------------------------------------|--------------|------------|----------|---------------|----------|------------|-------|
|             | _             | al               | gar     | ith               | m          | di      | Vid       | les.     | P        | rob         | ler           | n c                                    | low          | in .       | to       | Ŏ(            | 1)       | Siz        | 9     |
|             | _             |                  |         | 1512              |            |         |           |          |          |             |               |                                        |              | it i       | Jhì      | ch            |          |            |       |
|             |               | _                | PI      | rob               | len        | y .     | fit       | s i      | n        | ca          | che           |                                        | 1            |            | ì.e.     | _ ≤,          | M,       |            |       |
|             |               |                  |         | ob.               |            |         |           |          |          |             |               |                                        |              |            | i.e.     | $\mathcal{C}$ | (B)      | )          |       |
|             |               | TO               | DA      | y:                | 0          | re      | ex        | ar       | np!      | le          | of            | e                                      | ac           | h          |          |               |          |            |       |
| ۸۸          | Λ             |                  |         | 2 0               |            |         | /         | Λ        |          | 1           | 1             | 1                                      |              |            |          |               |          |            |       |
| <u>/Vle</u> | edi           | an               | †ī      | nd                | ing        | _/      | 0         | rcke     | 25       | <u>s</u> †  | ati:          | stic                                   | <u>ဋ</u> ္ဌ: |            | 0        |               | 1        | ۲          | . ~ ` |
|             |               | rec              | cal     | 0 (               | )(/        | V) ·    | -tî       | me       | d        | lete        | XW            | ini                                    | stic         |            | alg      | orit          | hm       | : [        | Ld    |
|             |               | (I               | ) \     | /ieu              | JC         | rn      | ay        | Q:       | 5        | Par         | titi          | one                                    | (X)<br>L /   | into       | ) (      | iolu          | mn       | <b>5</b> C | + 5   |
|             |               | 6                | ) .     |                   | †          | •       | i         | Lik      | e e      | KOC.        | KS,           | bu                                     |              | )(1)<br>0. | Sin      | ર્શ્ય         | <b>J</b> |            |       |
|             |               | (S)              | ) {     | SOVE              | (          | ea      | ch<br>1   | C        | sku      | mn          | _<br>         | → V                                    | Nec<br>L     | Xian<br>C  | 1<br>(). |               |          | 0          |       |
|             |               |                  |         | ecu               | 45.<br>181 | NO      |           | tin      | a 1      | med<br>-    | xia           | M                                      | Ø1<br>~      | CO.        | llen     | 1VL           | me       | JUU        | 15    |
|             |               |                  | ץ<br>ער | art<br>econy      | (110       | n<br>-0 | arv       | ay       | 9        | y ,         | کر<br>نظام    | (2                                     | ۸۸           |            |          |               |          |            |       |
|             |               |                  | ) N     | 20                | uv z<br>4  | 777.    | 0r<br>-<1 |          | orw.     | اد          | 1             | ·70                                    |              | 117        | -(n)     | λ             |          |            |       |
|             |               | (1               | ) .     |                   | <u> </u>   | 1 Cg    | 10        | <b>U</b> | U        | Ma          | 92            | <i>ح</i> ار                            |              | ///        | (//      | J             |          |            |       |
|             |               |                  |         | frei<br>SCO<br>MT | ۲<br>۱۵    | =       | · (       | $\gamma$ | V/13     | +           |               |                                        |              |            |          |               |          |            |       |
|             |               |                  |         | MT                | /N         | 1/5     | )         |          | f        | WE          | C             | dal                                    | los          | co         | ٨        | 1/5           | m        | edi        | QM.   |
|             |               |                  |         |                   |            | ילט ו   |           |          | into     |             | ) (           | TOM                                    | 500          | rativ      | se.      | ω<br>ΩΥ       | Var      | 1          |       |
|             |               |                  |         |                   |            |         |           | (        | Vic      |             |               | Dar                                    | all          | el         | So       | Car           | 5        |            |       |
|             |               | (4               | ) .     | MT  3  MT  (v)    | Pav        | rall    |           | SC       | an       | S           | $\Rightarrow$ |                                        | (~/          | Bt         | -1)      |               |          |            |       |
|             |               | (5)              |         | MT                | ( ;        | 7/10    | V)        |          |          |             |               |                                        |              |            |          |               |          |            |       |
|             | $\Rightarrow$ | > \(\bar{\chi}\) | 11      | (N)               | =          | M       | T(        | N/       | 5)       | +/          | MT            | \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ | N            | )+         |          | (N)           | B+       | 1)         |       |
|             |               |                  |         |                   |            |         |           |          |          |             |               |                                        |              |            |          |               |          |            |       |
|             |               |                  |         |                   |            |         |           |          |          |             |               |                                        |              |            |          |               |          |            |       |

- usual base case: 
$$MT(O(1)) = O(1)$$
  
 $\Rightarrow MT(N) \geqslant \#$  leaves  $L(N)$  in recursion  
-  $L(N) = L(N/5) + L(\frac{7}{10}N)$   
 $N^{\alpha} = (N/5)^{\alpha} + (\frac{7}{10}N)^{\alpha}$   
 $1 = (1/5)^{\alpha} + (7/10)^{\alpha}$   
 $\Rightarrow \alpha \approx 0.83978$   
 $\Rightarrow MT(N) \geqslant N^{0.8} = \omega(N/8)$  if  $B = \omega(B^{0.2})$ 

| W | 14         | LI  | RU        | k              | loc          | k          | re       | pl    | ace        | me       | nt       | ร์              | tra        | teg       | y?        |                 |                 |                 |             |
|---|------------|-----|-----------|----------------|--------------|------------|----------|-------|------------|----------|----------|-----------------|------------|-----------|-----------|-----------------|-----------------|-----------------|-------------|
|   | 0-         | LR  | lu        | <sub>N</sub> ≤ | 6            | <b>}</b> • | OP       | TM    | <b>′</b> a |          |          | RE              | SOU        | IRC       | E_        | Auc             | <del>S</del> ME | NTA             | TION        |
|   |            |     |           | leat           | or a         | X,Τα       | arjo     | an .  | 198        | 55       |          |                 | (c         | har       | 19in      | 9               | M)              |                 |             |
|   | Pro        | oof | •         |                |              |            |          |       |            |          |          |                 |            |           |           |                 |                 |                 |             |
|   | -          |     | Pai       | rtit           | ion          | Ь          | loc      | k o   | 2CC        | ess      |          | equ             | ienc       | ce        | int       | Ö               | ma              | Xim             | ial         |
|   |            |     |           |                | 25           |            |          |       |            |          |          |                 |            |           |           |                 |                 | <u>/_1</u>      |             |
|   |            |     | LK<br>OP  | tu<br>T        | Sp           | sen<br>ist | ds<br>s  | מפוני |            | y ¤<br>≥ | <u>M</u> | em<br>-/f       | 01)<br>3   | ne<br>me  | van<br>Ma | 51e             | tro             | /pho            | ise<br>fers |
|   |            |     | pe        | '<br>'         | pho          | 15e        | :        | at    | be         | st,      | 51       | ar              | ts         | pho       | use       | <i>ر</i><br>ر   | vitl            | 1               |             |
|   |            |     | en        | tire           | ) '<br>  ( ) | M          | 2 (      | cad   | che        | l        | vitl     | 1 U             | nee        | de        | g) '      | ite             | ms              | •               |             |
|   |            |     | bui<br>50 | ٠<br>>         | the<br>ho    | of<br>Of   | dv<br>fv | e o   | 74         | 3        | blc      | ck              | <b>S</b> ( | du        | sing      | 3 F             | oha             | se.             |             |
|   |            |     |           |                |              |            |          |       |            |          |          |                 |            |           |           |                 |                 |                 |             |
|   | <u>O</u> N | LIA | JE.       | A              | LG           | FOR        | ITH      | IMS   | 2          |          | Co       | mp              | ari        | ng        | (E        | gu              | lai             | r<br>uve<br>ith | \           |
|   |            |     | ``or      | Lin            | e"<br>H      | al         | 90°      | ritl  | m          |          | Can      | \' <del>+</del> | S(         | ee<br>tim | th        | e               | futi            | rre<br>:Ho      | 100         |
|   |            |     |           |                |              |            |          |       |            |          |          |                 |            |           |           |                 |                 |                 |             |
|   | _          | ch  | an        | gin            | 9            | M          | k        | y     | fa         | cto      | V        | of              | 2          | . (       | doe       | S4 <sup>1</sup> | + (             | affe            | ct          |
|   |            | 60  | un        | ds             | l            | ike        | (        | Ō(    | NBV        | M        | )        |                 |            |           |           |                 |                 |                 |             |
|   |            |     |           |                |              |            |          |       |            |          |          |                 |            |           |           |                 |                 |                 |             |
|   |            |     |           |                |              |            |          |       |            |          |          |                 |            |           |           |                 |                 |                 |             |

.

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

---

| W | 14         | LI  | RU       | k              | loc            | k          | re          | pl         | ace        | me       | nt       | ร์              | tra              | teg     | y?       |                 |           |                 |             |
|---|------------|-----|----------|----------------|----------------|------------|-------------|------------|------------|----------|----------|-----------------|------------------|---------|----------|-----------------|-----------|-----------------|-------------|
|   | 0-         | LR  | lu       | <sub>N</sub> ≤ | 6              | <b>}</b> • | OP          | TM         | <b>′</b> a |          |          | RE              | SOU              | IRC     | E_       | Auc             | ME        | NTA             | TPON        |
|   |            |     |          | leat           | or a           | X,Τα       | arjo        | วท         | 198        | 55       |          |                 | (c               | han     | gin      | 9               | M)        |                 |             |
|   | Pro        | of  | •        |                |                |            |             |            |            |          |          |                 |                  |         |          |                 |           |                 |             |
|   |            |     | Pai      | rtit           | ion            | Ь          | loc         | k o        | 2CC        | ess      |          | equ             | ienc             | ce,     | int      | Ö               | ma        | Xim             | ial         |
|   |            |     |          |                | 25             |            |             |            |            |          |          |                 |                  |         |          |                 |           | <u>/.1</u>      |             |
|   |            |     | LK<br>OP | T              | Sp             | sen<br>ist | ds<br>s     | משמים:     |            | y B<br>≥ | <u>M</u> | em<br>-/f       | ٥٧ <i>)</i><br>۲ | ne.     | mo       | ste<br>vu       | rs/<br>tr | pho             | ise<br>fers |
|   |            |     | pe       | <b>'</b>       | pho            | 251<br>25e | :           | at         | be         | st,      | 5        | ar              | İs               | pho     | use      |                 | vitl      | 1               |             |
|   |            |     | en       | tire           | ġ              | Mj         | 2 (         | cad        | che        | L        | uiH      | 1 <i>V</i>      | nee              | de      | <i>)</i> | ite             | ms        | •               |             |
|   |            |     | bu<br>50 | † ·<br><       | the<br>ho      | ne<br>Ne   | C/A         | e e        | 100/       | 3        | blc      | ck              | S (              | du      | sing     | 3 F             | oha       | se.             |             |
|   |            |     | 20       |                | 200            | X (        |             | ee         |            |          |          |                 |                  |         |          |                 |           |                 |             |
|   | <u>O</u> N | LIA | JE       | A              | LG             | FOR        | ITH         | IMS        | 2          |          | Co       | mp              | ari              | ng      | æ        | gu              | lav       | r .             |             |
|   |            |     | "or      | lin            | e <sup>u</sup> | al         | 90          | ritl       | m          |          | Can      | \' <del>+</del> | 56               | je<br>L | th       | e -             | feit      | r<br>ure<br>ith | )           |
|   |            |     | aga      | ling           | 51             | 01         | <b>-</b> +L | ine/       | pv         | وجد      |          | NI              | Op               | IIM     | ax       | Civ             | 901       | 1711            | m           |
|   |            | ch  | and      | gin            | 9              | M          | k           | ) <b>y</b> | fa         | cto      | V        | of              | a                |         | loe      | 5h <sup>1</sup> | + (       | affe            | ct          |
|   |            | 60  | ันท      | ds             |                | ike        | . (         | Ŏ(         | NBV        | M        | )        |                 |                  |         |          |                 |           | affe            |             |
|   |            |     |          |                |                |            |             |            |            | , -      |          |                 |                  |         |          |                 |           |                 |             |
|   |            |     |          |                |                |            |             |            |            |          |          |                 |                  |         |          |                 |           |                 |             |

.

| <u>S</u> e | lavi      | ch: | F  | ore: | pro  | ces        | 55<br>ar | n         | e<br>OVE | len<br>Io | nev<br>Os | its       | in<br><   | Co      | mf         | oar<br>. t  | ison | m<br>× | ode | l |
|------------|-----------|-----|----|------|------|------------|----------|-----------|----------|-----------|-----------|-----------|-----------|---------|------------|-------------|------|--------|-----|---|
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
| (1)        | <u>B-</u> | tre | es | 5    | Sup  | Pov        | +        | pre       | de       | ces       | Sóv       | - (       | 2         | ins     | evt        | - &         | de   | let    | e)  |   |
|            |           |     | in |      | )(X  | oge        | +1       | /V<br>+ > | 1        | me<br>eve | mo<br>h i | ry<br>f e | Tv<br>= 1 | an<br>~ | S(e<br>but | 45<br>- 100 | -00  | iano   | ve. |   |
|            |           | -   | ea | ch   | , No | ode        | 2        | مدد       | up       | ies       | Ē         | (1)       | d (       | loc     | ks         |             |      | let    |     |   |
|            |           | _   | he | igh  | +    | <b>=</b> ( | Θ(.      | log       | B        | N)        |           |           |           |         |            |             |      |        |     |   |
|            |           |     | we | eo   | T    | 0          | Kno      | 3W        | D        |           |           |           |           |         |            |             |      |        |     |   |
|            | C         | ach | e  | ob   | livi | ou         | s?       |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           | •         |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |
|            |           |     |    |      |      |            |          |           |          |           |           |           |           |         |            |             |      |        |     |   |

Analysis of BST search in vEB layout:
- consider recursive level of refinement at which △ has ≤B nodes: - (5B) height is between = lg B & lg B (binary searching on height) (⇒ size is between JB & B)  $\Rightarrow$  any root-to-node path (search path) visits  $\leq lg N = 2 log_B N log_B$ 's - each (B) occupies ≤2 memory blocks ⇒ ≤ 4 log B N = O(log N) memory transfers - generalizes to height not a power of 2, B-trees of constant branching factor, & dynamic B-trees: O(log N) insert/del. (Bender, Demaine, Farach-Colton 2000) (see 6.851: Advanced DSs)

| 5         | s+·      | م دان | •             |                |             |                          |          |             |              |               |            |           |              |            |                   |      |        |                   |          |
|-----------|----------|-------|---------------|----------------|-------------|--------------------------|----------|-------------|--------------|---------------|------------|-----------|--------------|------------|-------------------|------|--------|-------------------|----------|
| <u>)(</u> | srt      | -0    | , •           |                |             |                          |          |             |              |               |            |           |              |            |                   |      |        |                   |          |
|           |          |       |               |                |             |                          |          |             |              |               |            |           |              |            |                   |      |        |                   |          |
|           | 9        | ΛJ    | Sla           |                | +<          | -                        | +        |             |              | ما            | ماما       | (); , ;-  |              | \ <b>b</b> | 4.                | ~~   |        | EMP<br>(N)        |          |
|           | <b>(</b> | / V   | IN            | 261            | 12          | - \                      | אוכ      |             | Cac          | ne-           | -OD        | χιVι      | SN2          | Įν         | ) <del>-</del> 10 | 66   |        |                   |          |
|           |          |       | $\Rightarrow$ | $\sim \Lambda$ | NTI         | N)                       | =        |             | $( \land$    | <i>S</i> LC   | 9p         | $\wedge$  | ()           | —          | NO                |      | SPT    | CMF               | H_       |
|           |          |       |               | l              |             | +.                       | <u> </u> | 4           | Do           | 7             | <b>フ</b> じ | +         | ·            |            | 1                 | 0    | ^      | 4.0               | _"       |
|           |          |       |               | by             | C           | ואת                      | as       | <b>SI</b> , | D            | <b>&gt;</b> / | So         | YI        | 15           | ٥          | DIII              | nax  | 0      | NX                | 3 N      |
|           |          |       |               |                |             |                          |          |             |              |               |            |           |              |            |                   |      |        | _                 |          |
|           | (D)      | (1.   |               | `              |             | <b>~</b> ·C              |          |             | +<br>M<br>(M | \             |            |           | ۱ _          |            | 0                 |      | _      |                   |          |
|           | 8        | W     | na            | vy.            | ) Vr        | lei,                     | ge :     | 201         | 1            | 15            |            | သွင       | he           | -01        | OXI               | SIOV | ıS_    |                   |          |
|           |          |       |               | m              | era         | e T                      | îs       | 3           | } F          | ar            | $\alpha M$ | el        | SC           | an         | 5                 |      |        |                   |          |
|           |          |       | _             | 1              | 4           | 77                       | _        | 7           | . 11         | T/            | N/         |           | <b>+</b> /   | 7//        | V/c               | ٠ ــ | 1      |                   |          |
|           |          |       | <u>ー</u>      | / V            | 11          | (V)                      | <u> </u> | Ø           | 101          | 1 (           | 10         | <i>2)</i> | 1            | ノし         | 76                | 5 T  | エノ     |                   |          |
|           |          |       |               | <b>/</b> V     | T(          | M)                       | =        |             |              | B             | )          |           |              |            |                   |      |        |                   |          |
|           |          |       | _             | <b>V</b>       |             |                          |          | 1           |              |               | Λ          | 10        |              | _          |                   |      | - N    | 6                 |          |
|           |          |       |               | 18             | CUV         | SI                       | On       | 110         | ec.          | •             | /          | ΛĎ        |              |            |                   |      | /      | 5                 |          |
|           |          |       |               |                |             |                          |          | 个           |              | 1,            | 1,         | 1         | Λ <i>1</i> / |            |                   |      | Λ.     | /_                |          |
|           |          |       |               |                | 0,          | 9(4)                     |          |             |              | ā, `          | /B         | <u>a</u>  | ĹŹΒ          |            |                   |      | 14     | $\mathcal{B}$     |          |
|           |          |       |               |                | 20          | 101                      |          |             |              |               |            | -         |              |            |                   |      |        |                   |          |
|           |          |       |               |                |             |                          | •        | <b>U</b> /  | ns           |               |            |           |              | _          |                   | _    | N      | M                 | N        |
|           |          |       |               |                |             |                          |          | ,           | 18           |               |            |           |              | ر          |                   |      | 47 · · |                   | त        |
|           |          |       |               |                |             |                          |          |             |              | N/            |            |           | 100          |            |                   |      | •      | D                 |          |
|           |          |       |               |                |             |                          |          |             |              |               | 1)         |           |              |            |                   |      |        |                   |          |
|           |          |       | _             | . Λ            | 17          | $\langle \gamma \rangle$ | _        | N           | 0            | Λ             | J          | _         | B            |            |                   | L    | Ш      | an (              | <b>M</b> |
|           |          |       | <u> </u>      | <i>,</i> / v   | 11          | 10)                      |          | B           | · XC         | 7             | 7          |           | lg           | B          | rasi              | er   | 710    | an (              | नाः      |
|           |          |       |               |                |             |                          |          |             |              |               |            |           |              |            |                   |      |        |                   |          |
|           | (2)      | M     | 6-            |                | <b>.</b>    | 100                      | 2,00     |             |              | L.            | (          | 10        | 1-=          |            |                   |      | 0- 0   | جر د ۔            | 4)       |
|           |          |       | 0             | <u>Wi</u>      | 19 -        | rru                      |          | 1 <u>es</u> | Or           | <u> </u>      |            | V >.      | 51           | nar        | 9                 | rne  | 90     | 501               | リ        |
|           |          |       |               | SE             | <b>slit</b> | α                        | .YY      | au          | înī          | to            |            | B         | eg           | ua         | l s               | ubo  | 3 V V  | au?               | 5        |
|           |          |       |               | 100            | <b>.</b>    | ۱۱ مرے                   | ,, ()    | U           |              | +             |            | اہ        | 6            | _          |                   | 1    | _ +,   | 0                 | 1.       |
|           |          |       |               | 16             | <u>u</u>    | 1511                     | اهم      | 9           | 70 A         | - (           | <u>حر</u>  | ات ا<br>1 | \<br>O       |            |                   | ر٥   | ohli   | guc               | ous      |
|           |          |       |               | Mo             | 919         | e                        | Vic      | a '         | We.          |               | Pav        | all       | les          | ک          | car               | 25   |        |                   |          |
|           |          |       |               | 11             |             | -, -                     |          | ,           | น            |               |            | 14        | 1.0          |            |                   | 0    | 0:0    | 4)                |          |
|           |          |       |               | CK             | eep         | ing                      | , (      | ML          |              | LUV           | ren        | 1         | אמ           | UCK        | P                 | ZV   | MIS    | sor<br>ay:<br>guo |          |

| A! | <u> </u> | rit | hm               | S          | cl         | <b>0≲</b> ≤ | ies   |      | at       | /         | NI        | 7:   |            | (pa   | tsc  | -(          | 5,01 | 16)   |    |
|----|----------|-----|------------------|------------|------------|-------------|-------|------|----------|-----------|-----------|------|------------|-------|------|-------------|------|-------|----|
|    | <u> </u> | 6.  | Or               | 17         | : (        | Coy         | npu   | tat  | ion      | al        | Bi        | olog | 99         | U     |      |             |      |       |    |
|    |          | (0  | jeni             | omo        | 25,        | ph          | ylo   | gei  | ny,      | ્હ        | tc.)      | )    |            |       |      |             |      |       |    |
|    | _        | 6.  | 25               | 54         | ٠          | Adı         | san   | ce   | V I      | Ale       | 305       | ithr | 75         |       |      |             |      |       |    |
|    |          | Ci  | nte              | ns         | ၉ .        | SW          | rve,  | y    | st       | <u> </u>  | John      | le t | fie!       | ld    | )    |             |      |       |    |
|    | _        | 6   | 85               | O(         | ` (        | <u>5</u> e  | om    | etr  | ric      |           | <i>on</i> | npu  | tin        | 9     |      |             |      |       |    |
|    |          | (u  | JOY              | kiv        | 19         | Wi          | th f  | 2071 | nts.     | Li        | nes       | · Po | sky        | 70hs  | s, w | 105         | 165, | (··)  |    |
|    | _        | 6.  | 8c               | 19         | : (        | Seo         | me    | tvi  | C        | to        | lotiv     | 29   | Alg        | ygy i | thi  | <u> 1</u> 5 | K    | emaii |    |
|    |          | (6  | rig              | am         | أم         | rob         | ot    | avn  | 15,      | yq        | ote       | in t | old        | ling  | n    | .)          | D    | email | ne |
|    |          | _   |                  | _          |            |             |       |      | _        |           |           | S    |            | ctu   | res  | 5           | 6    |       |    |
|    |          | (5  | iub              | 209        | ari        | thw         | NIC   | Pe   | erte     | STM       | anan      | ce)  | 11         |       |      |             | •    |       |    |
|    | _        | 6.  | 85               | <u> </u>   | 9 )        | )ìs         | str   | ibu  | ted      | Į į       | 469       | orit | hn         | 15    |      |             |      | ynch  |    |
|    |          |     |                  |            |            |             |       |      |          |           |           |      |            |       |      | h ·         | faul | lts)  |    |
|    | -        | 6.  | X5               | 3          | : <i>F</i> | ty9         | orit  | thm  | nī C     | (         | am        | ie T | lhe        | 765   | 1    | ٨           |      |       |    |
|    |          | (/  | Jas              | \<br>      | egi        | LìLÍ        | orio  | 74 ( | iuci     | tio       | n Y       | nec  | cha        | inis  | m.   | de.         | sign | 4 -   | )  |
|    |          | 6.  | χ                | つり         | ! /        | Ve          | mo    | rk   |          | )pti      | mi        | zat  | 102        | 1     | 1 -  | +           | . Lf | 1     |    |
|    |          | (0  | ptir             | Jig        | atio       | y i         | in    | 940  | aph      | .:  <br>N | oey       | ond  | 5          | hor   | Tes. | J           | rath | 5)    |    |
|    | -        | 6.  | 85               | 96         | ;<br>^     | <b>Ka</b> i | ndc   | )Mī  | ક્લ      | l F       | tlgc      | orit | ИM         | 15    | 0    | 0           | 0    | 1 .   |    |
|    |          |     | 0W<br><i>Q T</i> | 0)         | ind        | omi         | 1es   | S 1  | nal      | <@S       | a         | 195. | , <u>S</u> | im    | pler | 2           | tas  | ter)  |    |
|    |          | 6.  | <u>გ</u> ე       | ) <i>F</i> | • /        | Ve          | TWO   | rK   | av       | 1dl       | (a        | mp   | ute        | er    | 26   | Cu          | rity | 1     |    |
|    |          | (a  | ppki<br>0 =      | red        | CV         | ypt         | ogr   | apl  | 14)      |           | _         | 0    | <b>^</b>   | _1    |      | 0           |      |       |    |
|    |          | 6.  | 87               | アン         | ٠ (        | ry          | p70   | gra  | lph      | 9         | ano       | X (  | بالا       | 1PTO  | ana  | xy:         | SīS  |       |    |
|    |          |     | nes<br>Q 1       | LG!        | ica)       | ۲ (<br>۱۸.  | ry(   | 2010 | Va       | ohy<br>D. |           |      |            | T.    |      |             |      |       |    |
|    |          | Ø,  | <b>Δ</b> .       | 16         | , /        | VW          | X) (C | LOV  | <b>e</b> | YY        | 99Y       | COM  | NV/\       | ing   |      |             |      |       |    |
|    |          |     |                  |            |            |             |       |      |          |           |           |      |            |       |      |             |      |       |    |

Other theory classes: - 6.045: Automata, Computability, & Complexity - 6.840: Theory of Computing - 6.841: Advanced Complexity Theory - 6.842: Randomness & Computation - 6.845: Quantum Complexity theory - 6.440: Essential Coding Theory - 6.441: Information Theory - Frisbee Competition

6.046J / 18.410J Design and Analysis of Algorithms Spring 2015

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.
