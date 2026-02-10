MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# Fibonacci heaps

Lecturer: Michel X. Goemans

## 1 Introduction

Today we will describe Fibonacci heaps, a data structure that provides a very efficient implementation of a priority queue. By priority queue we mean a data structure that stores a set S of elements where with each element s we associate a key k(s) being "priority" of that element. Now, we want the queue to handle three operations on set S:

- INSERT Adding a new element s' with a key k(s') to S
- EXTRACT-MIN Returning an element  $s^*$  of S having minimal key and removing  $s^*$  from S
- DECREASE-KEY Replacing the value of a key of some element s by a new, smaller value.

The motivation behind the search for fast implementation of priority queues can be observed on the example of two classical graph problems: Single-source Shortest Paths and Minimum Spanning Tree.

## 1.1 Single-source Shortest Paths problem

We are given a directed graph G = (V, E), some vertex  $s \in V$  and a length function  $l : E \to \mathbb{R}_+$  on the arcs. Observe that we impose that the lengths are nonnegative. Now, for each vertex  $v \in V$  we want to compute the length  $d_s(v)$  of the shortest path from s to v.

The classical solution for this problem is Dijkstra's algorithm. The algorithm is:

- 1. Maintain a priority queue containing some subset S of vertices of G with keys k(v). Initially, S = V, k(s) = 0 and  $k(v) = +\infty$ .
- 2. As long as S is nonempty:
  - Extract a vertex u from S with minimum key. Output k(u) as the value of  $d_s(u)$ .
  - For each out-neighbor  $v \in S$  of u, we update (i.e. possibly decrease) the key k(v) of v to be  $\min\{k(v), k(u) + l((u, v))\}.$

In this algorithm, k(v) represents the length of the shortest path from s to v using only intermediate vertices not in S, and represents  $d_s(v)$  when extracted. The algorithm can be adapted to output the shortest paths.

## 1.2 Minimum Spanning Tree problem

Given an undirected graph G=(V,E) and a weight function  $w:E\to\mathbb{R}$  on edges, we would like a spanning tree of G of minimal weight. Surprisingly, one of the classical solutions of this problem - Prim's algorithm - is very similar to the approach of Dijkstra's algorithm for Single-source Shortest Path problem. The algorithm is as follows:

- 1. Maintain a priority queue containing some subset S of vertices of G with keys k(v) and a tree T spanning  $V \setminus S$ . Initially,  $T = \emptyset$ , S = V, k(s) = 0 for some arbitrary vertex s and  $k(v) = +\infty$  for  $v \neq s$ .
- 2. As long as S is nonempty:
  - Extract a vertex u from S with minimum key. If  $u \neq s$  (first iteration), add to T the corresponding edge (i.e. the minimum-weight edge connecting u to T of weight k(u)).
  - For each neighbor  $v \notin S$  of u, we update (i.e. possibly decrease) k(v) to be  $\min\{k(v), w((u,v))\}$ .

## 1.3 Number of priority queue operations

We will not prove the correctness of the algorithms. However, for the sake of the running time analysis that we will do later, we notice that in both cases the algorithm uses |V| insert operations, |V| extract-min operations and, since each edge can enforce at most one decrease-key operation, at most |E| decrease-key operations.

# 2 Binary heaps

The classical implementation<sup>1</sup> of priority queues are binary heaps. A binary heap T is a binary tree whose nodes correspond to elements of the set S and has two properties:

- it is almost complete i.e. if T has depth h then it has exactly  $2^i$  vertices on depth i if i < h and the last level is filled from the left.
- heap-ordering: the key of every child is not smaller than the key of its parent.

Keeping this properties in mind it is relatively easy (see [CLRS]) to develop procedures for inserting, extracting the minimal element and decreasing the key that execute any of these operations in  $O(\log n)$  time where n is the number of items in the priority queue. Therefore, since the number of elements is at most |V| in our applications, we obtain the total running time of both algorithms to be  $O((|V|+|E|)\log|V|)$ . Obviously,  $|E| \geq |V|$  in case of connected graphs and therefore the running time is dominated by the  $O(|E|\log|V|)$  term corresponding to decrease-key operations. The question is: can we do better?

# 3 d-ary heaps

One of the ideas to get a better running time is increasing the arity of the tree that we are using. If we use a d-ary tree instead of a binary one then we reduce the depth of our tree and thus our inserts and bottlenecking decrease-key operations execute in  $O(\log_d |S|)$  time. On the other hand, the execution of extract-min operation requires  $O(d\log_d |S|)$  time. So, by choosing the best possible  $d = \lceil |E|/|V| \rceil$  we get the total running time of our algorithms to be  $O((|E|+d|V|)\log_d |V|) = O(|E|\log_{\lceil |E|/|V| \rceil}|V|)$ , which is a significant improvement for dense graphs. However, it turns out that we can do even better. Namely, we can implement priority queue in such a way that from the point of view of running time analysis of our algorithms the cost of DECREASE-KEY will be constant and costs of INSERT and EXTRACT-MIN will be logarithmic. This leads to the essentially optimal  $O(|E|+|V|\log|V|)$  running time of both algorithms and for some present-day applications (think graphs with billions of edges) this improvement can make a huge difference.

<sup>&</sup>lt;sup>1</sup>A comprehensive coverage of binary heaps (as well as Fibonacci heaps) can be found in [CLRS].

# 4 Fibonacci heaps

The Fibonacci heaps were proposed by Fredman and Tarjan in 1984 giving a very efficient implementation of the priority queues. The main motto of this construction is laziness - "we do work only when we must, and then use it to simplify the structure as much as possible so that the future work is easy". This way, we enforce that any sequence of operations has to contain a lot of cheap ones before we need to do something computationally expensive - the formalization of this intuition will be given later.

## 4.1 Construction

A Fibonacci heap consists of a collection of heap-ordered trees (of variable arity) with following properties:

- 1. nodes of the trees correspond to elements being stored in the queue,
- 2. roots of heap-ordered trees are arranged in a doubly-linked list,
- 3. we keep a pointer to the root of a tree that corresponds to the element with minimum key (note that heap-ordering of the trees implies that such minimum element has to be a root of some tree),
- 4. for each node we keep track of its rank (degree), i.e. the number of its children, as well as whether it is marked (the purpose of marking will be defined later on),
- 5. size requirement: if a node u has rank k then the subtree rooted at u has at least  $F_{k+2}$  nodes, where  $F_i$  is the i-th Fibonacci number, i.e.  $F_0 = 0$ ,  $F_1 = 1$  and  $F_i = F_{i-1} + F_{i-2}$  for  $i \ge 2$ .

We proceed now to describing how do we perform priority queue operation on our Fibonacci heap.

## **4.1.1** INSERT

Inserting is very simple. We just add the new element s as a new heap-ordered tree to our collection and check whether k(s) is smaller that the current minimum for the queue—if so then we change the pointer to the minimum accordingly (see Figure 1).

### 4.1.2 DECREASE-KEY

When we decrease the key of an element s, if the heap-ordering is still satisfied then we do not need to do anything else. Otherwise, we just cut s out of the tree in which it resides and put it as a root of a new tree in our collection (note that all the descendants of s are now in this new tree as well). We compare the new key of s and the previously minimum key and change the pointer accordingly (see Figure 1).

This way we end up with something that looks like a desired Fibonacci heap. However, the problem with simply cutting each such s is that, when we perform in this manner many DECREASE-KEY operations, we may end up violating the size requirement that we wanted to preserve. Therefore, to alleviate this issue we introduce an additional rule that when we cut s we check whether its parent is marked. If so then we cut the parent as well (and we unmark it). Otherwise, we just mark the parent. Note that we do this cutting recursively, so if the parent of marked parent of s is also marked then we cut it as well, and so on. Obviously, if we cut a root we are not doing anything, and so it is useless to mark a root. This (potentially cascading) cutting procedure therefore always ends.

Figure 1: Illustration of: (left side) inserting a new element to the Fibonacci heap; (right side) cutting a vertex in the first step of DECREASE-KEY operation. In both examples we assumed that the newly created root has smaller key than the keys of all the other elements.

#### 4.1.3 EXTRACT-MIN

Finally, we can describe extracting the minimum element  $s^*$ . We start with removing  $s^*$  (recall that we stored the pointer to it) and putting all the children of  $s^*$  as roots of new trees in our collection. Next, we scan the entire list of roots in our collection to find the new minimum element and we set the relevant pointer accordingly.

In principle at this point we could be done, because we obtain once again a valid Fibonacci heap. However, it is not hard to see that so far executing of any of our queue operations makes the list longer and longer. So, going through the whole list of roots during EXTRACT-MIN can be very expensive computationally. Therefore, in the spirit of laziness, if we have to do this work anyway then we can use this opportunity to do some cleaning as well, and avoid in this way the necessity of doing the whole work again when doing the next EXTRACT-MIN. What we do is, as long as there are two trees whose roots have the same rank, say k, we merge these trees to obtain one tree of rank k+1. Merging consist of just comparing the keys of the roots and setting the root of the tree with larger key as a new child of the other root (see Figure 2). Note that since merging can introduce a second tree of rank k+1 in the collection, one root can take part in many merges.

## 4.2 Running-time Analysis

Now we want to analyze the worst-case performance of the described Fibonacci heap data structure.

## 4.2.1 A worst-case example

Let's imagine the following scenario: We do n consecutive INSERT operations into the Fibonacci heap such that it is a circular linked list containing all elements as singleton heaps. If we perform an EXTRACT-MIN operation on this Fibonacci heap, this operation will have to go through the entire list to determine the new minimum. This takes O(n) time — an unbearable performance for just one operation.

Figure 2: Illustration of merging of two trees of the same rank.

## 4.2.2 Are Fibonacci heaps useless?

Does this mean that Fibonacci heaps are inefficient? No! Intuitively such heavy operations can occur only very rarely and make no big contribution to the overall running time of an algorithm using the heap. Being not able to give worst-case performance guarantees for each individual operation, we want to consider a sequence of operations and give a proof that, for any such sequence, the total running time is small, in the sense that this running time can be apportioned between the individual operations so that each has a small contribution. This type of analysis is called amortized analysis [CLRS]. More precisely, if we have  $\ell$  different types of operations and we claim that the amortized running time of an operation of type j is at most  $t_j$ , this means that for any sequence of operations composed of  $k_j$  operations of type j for all  $j=1,\cdots,\ell$  (with operations of different types interlaced in any way), the total running time is upperbounded by  $\sum_j k_j t_j$ .

#### 4.2.3 Excursion: Amortized Analysis via the Potential Method

The most common way to perform amortized analysis is using the potential method. The idea of the potential method allows cheap operations to save up time for the use of heavy operations. This functions like a bank account with time deposited in it. The potential function  $\Phi$  represents the balance in the account. Initially, the balance is zero, and remains nonnegative during the whole sequence. Now operations are performed having costs (i.e. running times) of  $c_1, c_2, c_3, ..., c_k$ . Every operation is allowed to either pay more than its actual cost  $c_i$  thereby increasing its amortized cost, placing the credit/savings in the bank account thus increasing the balance  $\Phi$ , or pay less than the actual cost by withdrawing the difference from  $\Phi$ . This gives the amortized cost.

Often one can think of the potential function as a measurement of the complexity of the data structure or configuration within an algorithm. In this case cheap operations are allowed to increase the internal complexity, while operations which simplify or clean up the data are allowed to take more time.

Making this formal, a potential function,  $\Phi$ , maps a configuration  $D_i$  of an evolving algorithm or data structure D into a nonnegative number. The start configuration is normalized to have the value 0:  $\Phi_0 = \Phi(D_0) = 0$ . Consider a sequence of operations  $o_1, o_2, o_3, ..., o_k$  and let  $D_i$  be the configuration of the data structure after performing the *i*th operation. We impose that the potential

function remains nonnegative throughout:

$$\forall t : \Phi_t = \Phi(D_t) \geq 0.$$

If operation  $o_i$  has cost (running time)  $c_i$  then its amortized cost is defined by:

$$a_i = c_i + \Delta \Phi_i = c_i + \Phi_i - \Phi_{i-1}.$$

Given this, it is easy to see that the sum of the amortized costs upperbounds the original total cost:

$$\sum_{i=1}^{k} a_i = \sum_{i=1}^{k} (c_i + \Phi_i - \Phi_{i-1}) = \sum_{i=1}^{k} c_i + \Phi_k - \Phi_0 \ge \sum_{i=1}^{k} c_i.$$

Thus amortized analysis provides an upper bound on the worst-case cost of any sequence of operations.

The difficulty in performing amortized analysis is in choosing the right potential function.

## 4.2.4 Fibonacci heaps obey the size requirement

The first important observation regarding the heap-ordered trees in a Fibonacci heap is that the restriction to cut off at most one child prevents cutting down the nice binomial tree like structure built up through the combination steps. This guarantees that the size requirement we want to have is preserved.

**Lemma 1** Consider a node x with rank (number of children) d. Let  $y_1, y_2, ..., y_d$  be those children in the order they were added to the tree. Then every child  $y_i$  has rank at least i-2.

**Proof:** When  $y_i$  was added to x, at least the i-1 children  $y_1$  to  $y_{i-1}$  were present. Since only roots of the same rank get combined,  $y_i$  had at least i-1 children at this time. At most, one of these children could have been cut away since otherwise  $y_i$  would have qualified for a cascading cut. Thus  $y_i$  has at least i-2 children.

A simple counting argument given in the next lemma reveals that the number of nodes in a subtree rooted at a node of rank d is at least  $F_{d+2}$ . This exponential growth upperbounds the heap degrees to be logarithmic.

**Lemma 2** Let N(d) be the smallest possible number of nodes in a subtree rooted at a node of rank d. Then  $N(d) \geq F_{d+2}$ . Thus, the rank of any node in a Fibonacci heap with n elements is  $O(\log n)$ .

**Proof:** For N, it holds that N(0) = 1, N(1) = 2 and we have the recurrence relation:

$$N(d) \ge 2 + \sum_{i=2}^{d} N(i-2)$$

because of Lemma 1 (counting one for the root, one for the first child  $y_1$  and N(i-2) for each remaining child  $y_i$ ). Proceeding by induction on d (thus assuming that  $N(j) \ge F_{j+2}$  for j < d), we get that

$$N(d) \ge 2 + \sum_{i=2}^{d} F_i = 1 + \sum_{i=0}^{d} F_i.$$

The right-hand-side is  $F_{d+2}$ ; this can be shown again by induction on d:  $1 + \sum_{i=0}^{d} F_i = F_{d+1} + F_d = F_{d+2}$ . Thus we have shown the first part of the lemma that  $N(d) \geq F_{d+2}$ .

Using the closed-form expression for the Fibonacci numbers, we get that

$$N(d) \ge F_{d+2} = \frac{1}{\sqrt{5}} \left( \left( \frac{1+\sqrt{5}}{2} \right)^{d+2} - \left( \frac{1-\sqrt{5}}{2} \right)^{d+2} \right) \ge 1.61^d.$$

Since  $N(d) \leq n$ , all ranks of nodes in the heap are at most  $log_{1.61}$  n.

## 4.2.5 Amortized Analysis of the Fibonacci heap operations

Each individual adding, combining and cutting step takes only O(1) time. Thus the only two critical situations occur when we have to search through many roots for finding the minimum and when we have a long chain of cascading cuts. The length of a cascading cut corresponds to the number of nodes being unmarked. With this intuition, we choose the potential function to be

$$\Phi_t = r_t + 2m_t$$

where  $r_t$  is the number of roots and  $m_t$  the number of marked nodes at time t. The reason for the factor of 2 will become clear in the analysis. Here is the amortized analysis of each operation.

#### • INSERT

Inserting a new root in the list takes  $c_t = O(1)$  time and increases the number of roots  $r_t = r_{t-1} + 1$  by one. Thus the amortized cost for an INSERT operation is also constant:

$$a_t = c_t + (r_t - r_{t-1}) + 2(m_t - m_{t-1}) = O(1) + 1 + 0 = O(1).$$

#### • EXTRACT-MIN

During an EXTRACT-MIN operation, we start with  $r_t$  roots, cut away the minimum root (say of rank d) leaving  $r_{t-1}+d-1$  roots in the list. These get combined to  $r_t$  roots, having different ranks. Since, by Lemma , the maximum possible rank is  $O(\log n)$ , there are in the end only  $r_t = O(\log n)$  roots left. Since the cut and each of the combining steps takes O(1) time and eliminates one root the actual time spend on an EXTRACT-MIN operation is at most  $c_t = r_{t-1} + d - 1$  units (where the 'unit' may need to be redefined to take into account constants). Putting this together the amortized cost for an EXTRACT-MIN operation is logarithmic:

$$a_t = c_t + (r_t - r_{t-1}) + 2(m_t - m_{t-1}) = (r_{t-1} + d - 1) + (r_t - r_{t-1}) + 0 = r_t + d - 1 = O(\log n).$$

### • DECREASE-KEY

Let's assume that during a DECREASE-KEY operation we do k cuts,  $k \ge 1$ . Each (but the first) cut unmarks a node and each cut introduces a new root. Thus the increase in the number of roots,  $r_t - r_{t-1}$ , is equal to the number k of cuts performed. The decrease  $m_{t-1} - m_t$  of marked nodes is either k-1 or k (depending on whether the node itself was marked); thus, in any case,  $m_{t-1} - m_t \ge k - 1$ . The key decreasing, cutting and reinserting takes 1 + k units of time (redefining the unit, if needed), and thus its amortized cost is:

$$a_t = c_t + (r_t - r_{t-1}) + 2(m_t - m_{t-1}) \le 1 + k + k - 2(k-1) = O(1).$$

This last relation justifies the constant 2 in the definition of the potential function.

Summarizing, in a Fibonacci heap, every INSERT and DECREASE-KEY takes O(1) amortized time, and every EXTRACT-MIN takes  $O(\log n)$  amortized time.

#### 4.2.6 Using Fibonacci heaps to speed up Prim's and Dijkstra's algorithm

Using Fibonacci heaps in the two algorithms mentioned in the introduction leads to improved running times of  $O(|E| + |V| \log |V|)$ .

# References

[CLRS] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Cliff Stein. *Introduction to Algorithms (Second Edition)*. MIT Press and McGraw-Hill.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

## Network Flows

Lecturer: Michel X. Goemans

## 1 Introduction

In the previous lecture, we introduced Fibonacci heaps, which is a data structure that provides an efficient implementation of priority queues. In this lecture, we switch our attention from efficiency to algorithm design. In particular, for the next few lectures we study **Network Flows**.

Network flows are a family of problems that are concerned with a directed graph and properties of functions defined on the graph. A flow is an abstraction of elements which typically do not disappear while travelling through the edges of the directed graph; it could be current in an electrical network, packets in a computer network, cars/trains in a transportation network, or some purely abstract object. In the maximum flow problem, we try to obtain a flow on the graph such that the flow going from a given source vertex to a given sink vertex is maximized.

In today's lecture, we focus on two instances of network flow problems: the **Shortest Path Problem** and the **Maximum Flow Problem**. There are other variants of network flow problems that we cover later in this class. For example, we will talk about the minimum cost flow or minimum cost circulation problem, which is a generalization of both the shortest path problem and the maximum flow problem. We will also cover the bipartite matching problem, which has two versions: cardinality bipartite matching (a special case of the maximum flow problem) and weighted bipartite matching (a special case of the minimum cost flow problem). There are still other network flow problems that we do not discuss such as the multi-commodity flow problem. Figure 1 illustrates how these network flow problems are related to one another.

### 2 Shortest Path Problem

Let G = (V, E) be a directed graph, where V denotes the set of vertices and E denotes the set of edges. Let  $\ell \colon E \to \mathbb{R}$  be a length function defined on the edges of G. Given two vertices s and t in V, the s-t shortest path problem is the problem of finding a simple directed path on G from s to t of minimum total length. The length of a path P is defined to be the sum of the lengths of all the edges in P:

$$\ell(P) = \sum_{(v,w)\in P} \ell(v,w).$$

In this problem, we refer to s as the "source" vertex and t as the "sink" vertex.

We note that if the length function  $\ell(e)$  is non-negative for every edge  $e \in E$ , then Dijkstra's algorithm using Fibonacci heaps provides a  $O(m+n\log n)$  solution to this problem, where m=|E| and n=|V|. On the other hand, if some edges of G have negative lengths, but the graph has the property that for every cycle C the total length of the cycle is non-negative, then we can use the Bellman-Ford algorithm to solve the s-t shortest path problem in polynomial time. For more information on Dijkstra's and the Bellman-Ford algorithm, see Chapter 24 in [CLRS].

<sup>&</sup>lt;sup>1</sup>For  $v, w \in V$ , we use the notation  $\ell(v, w)$  to mean the length of the edge e = (v, w). In these notes, we use the two notations  $\ell(e)$  and  $\ell(v, w)$  interchangeably.

Figure 1: Some instances of network flow problems and how they are related to one another, where the arrow indicates "is a special case of". In this lecture we only cover the shaded boxes: the shortest path problem and the maximum flow problem.

**Remark 1:** In this lecture, we consider directed graphs only. For undirected graphs with nonnegative edge lengths, we can still apply Dijkstra's algorithm by transforming every (undirected) edge into two edges of opposite directions with the same length, as illustrated in Figure 2.

Figure 2: Transformation of an undirected edge into two directed edges to apply Dijkstra's algorithm.

However, the same trick does not apply for the Bellman-Ford algorithm, because even if the original undirected graph satisfies the constraint that every cycle has non-negative length, the new directed graph resulting from the transformation might violate this constraint. An example of this case is given in Figure 3.

The problem of finding the shortest path between two vertices in an undirected graph where every cycle has non-negative length is still solvable in polynomial time, but it is a much harder problem. We will discuss this problem later in the class if time permits.

**Remark 2:** In directed graphs with non-negative, given a shortest path P between two vertices, the path between any two vertices in P is also the shortest path between those two vertices. However, this is not necessarily true in the case of undirected graphs (and this prevents the use of a transformation to a directed graph). For example, in the graph given in Figure 3(a), the shortest path between v and w is  $P = \{(v, z), (z, w)\}$  with length 0. However, the shortest path between v and v is not v as it appears in v, but rather v and v with length 0.

(b) Directed graph after the transformation. The cycle  $\{(w,z),(z,w)\}$  has negative length.

Figure 3: An example where the given transformation creates a negative cycle so that the Bellman-Ford algorithm cannot be applied.

## 3 Maximum Flow Problem

The second instance of network flow problems that we study in this lecture is the maximum flow problem. In this problem, we want to find a flow from a source vertex to a sink vertex with maximum flow value.

More precisely, we define the problem framework as follows. Let G = (V, E) be a directed graph, where V is the set of vertices and E is the set of edges of G. Let n denote the cardinality of V and m denote the cardinality of E. Given a vertex  $v \in V$ , let  $N^+(v)$  (resp.  $N^-(v)$ ) denote the set of endpoints of edges coming out (resp. into) v:

$$N^{+}(v) = \{ w \in V : (v, w) \in E \},\$$

$$N^{-}(v) = \{ w \in V : (w, v) \in E \}.$$

Furthermore, let  $u: E \to \mathbb{R}_+$  be a capacity function that limits the amount of flow that we can send through each edge of G. We refer to the graph G and the capacity function u collectively as the **network** G. Given a source vertex  $s \in V$  and a sink vertex  $t \in V$ , we are interested in determining how much flow we can push from s to t through this network.

#### 3.1 Notions of Flow

Loosely speaking, a flow is an assignment of quantity to the edges of G under certain constraints. There are two notions of flow that we use in this class: raw flow and net flow.

**Definition 1** A raw flow on a network G is a function  $r: E \to \mathbb{R}$  satisfying the following properties:

- 1. Capacity constraint: For all  $(v, w) \in E$ ,  $0 \le r(v, w) \le u(v, w)$ .
- 2. Conservation constraint: For all  $v \in V \setminus \{s, t\}$ ,

$$\sum_{w \in V : (v,w) \in E} r(v,w) - \sum_{w \in V : (w,v) \in E} r(w,v) = 0.$$

Given a raw flow r, the **flow value** of r is defined to be the total excess of flow at the source vertex s, i.e.

$$|r| = \sum_{w \in N^+(s)} r(s, w) - \sum_{w \in N^-(s)} r(w, s).$$

We now give the second definition of flow, which is the one we primarily use for the rest of these notes.

**Definition 2** Given a raw flow r on a network G, the **net flow** f with respect to r is the function  $f: E \to \mathbb{R}$  given by f(v, w) = r(v, w) - r(w, v).

An example of raw flow and the corresponding net flow is illustrated in Figure 4.

Figure 4: An example of a raw flow and its corresponding net flow.

Before we go any further, we first note that from the definition given above, to compute f(v, w) we need both r(v, w) and r(w, v). However, there is a slight difficulty because even if  $(v, w) \in E$ , (w, v) might not be an edge of G. To resolve this issue, we assume that the graph G has the property that if  $(v, w) \in E$  then  $(w, v) \in E$ . Given a directed graph G, we can achieve this property by modifying G as follows:

- 1. Consider the set  $E' = \{(v, w) \in E : (w, v) \notin E\}$ .
- 2. For every  $(v, w) \in E'$ , create a new edge (w, v) with edge capacity 0 and add it to E.

Similar to the definition of the flow value of raw flow, the **flow value** of f is defined to be the total amount of net flow that comes out from the source vertex s:

$$|f| = \sum_{w \in N(s)} f(s, w), \tag{1}$$

where we now use N(s) to denote  $N^+(s) = N^-(s)$ , the common set of out-neighbors and in-neighbors of s.

From the definition of net flow, it is easy to check that the net flow f satisfies the following properties:

- 1. Skew symmetry: For all  $(v, w) \in E$ , f(v, w) = -f(w, v).
- 2. Capacity constraint: For all  $(v, w) \in E$ ,  $f(v, w) \le u(v, w)$ .
- 3. Flow conservation: For all  $v \in V \setminus \{s,t\}$ ,  $\sum_{w \in N(v)} f(v,w) = 0$ .

Note that, unlike r, the flow f has no restriction on being negative. In fact, f will be negative for some edges, unless it is the 0 flow everywhere. For example, if the original graph G has an edge (v, w) with positive raw flow r(v, w) such that (w, v) is not an edge, then in the modified graph, the edge (w, v) has negative net flow f(w, v) = -r(v, w). Note that this does not violate the capacity constraint since  $f(w, v) \leq u(w, v) = 0$ . Figure 5 illustrates an example of a net flow.

For the maximum flow problem, we use the notion of net flow. For the rest of these notes, unless specified otherwise, the term flow refers to net flow. We can now define the maximum flow problem properly.

**Definition 3 (Maximum Flow Problem)** Given a network G, a source vertex  $s \in V$ , and a sink vertex  $t \in V$ , the maximum flow problem is the problem of finding a flow through G of maximum flow value.

Notice that modifying G by adding to E the new edges needed to define the net flow does not affect the maximum flow problem, since the new edges all have zero capacity.

Figure 5: An example of a flow of a network. The label x/y on each edge e is such that x = f(e) and y = u(e). Here the flow value is |f| = 3.

### 3.2 s-t Cut

We now define the notion of *cut*, which helps us to construct the solution of the maximum flow problem.

**Definition 4** Suppose that we have a network G with source vertex s and sink vertex t. Let S be a subset of V such that  $s \in S$  and  $t \notin S$ , and let  $\overline{S} = V \setminus S$ . Then the s-t cut with respect to S is defined to be

$$(S:\overline{S}) = \{(v,w) \in E : v \in S \text{ and } w \in \overline{S}\}.$$

We can also denote an s-t cut by  $\delta^+(S)$  or  $\delta^-(\overline{S})$ , but in this class the preferred notation is  $(S:\overline{S})$  as introduced above. Figure 6 shows an example of an s-t cut.

Figure 6: An example of an s-t cut. The solid arrows represent the edges in  $(S:\overline{S})$ .

**Definition 5** Given an s-t cut  $(S:\overline{S})$ , then its **cut capacity** is defined to be the total capacity of the edges across the cut:

$$u(S:\overline{S}) = \sum_{(v,w)\in(S:\overline{S})} u(v,w).$$

### 3.3 Connection between Flows and Cuts

We have the following lemma that connects flows and cuts.

**Lemma 1** Let G be a network with source s and sink t. Then for every flow f and every s-t cut  $(S:\overline{S})$ , we have

$$|f| = \sum_{(v,w)\in(S:\overline{S})} f(v,w). \tag{2}$$

In particular, this implies that  $|f| \leq u(S : \overline{S})$ 

**Proof:** From the flow conservation property of f, for every vertex  $v \in S \setminus \{s\}$ , we have

$$\sum_{w \in N(v)} f(v, w) = 0.$$

Taking the sum over all vertices  $v \in S \setminus \{s\}$  gives us

$$\sum_{v \in S \setminus \{s\}} \sum_{w \in N(v)} f(v, w) = 0.$$

Adding the definition of the flow value of f (Eq. (1)) to the equation above yields

$$|f| = \sum_{w \in N(s)} f(s, w) + \sum_{v \in S \setminus \{s\}} \sum_{w \in N(v)} f(v, w).$$

Now notice that if an edge (v, w) appears in either of the summations above and  $w \in S$ , then (w, v) also appears in the summations. Therefore, we can rewrite the equation above in a slightly different way:

$$|f| = \sum_{(v,w)\in(S:\overline{S})} f(v,w) + \sum_{v\in S} \sum_{w\in S} f(v,w).$$

By the skew-symmetry property of f, the second summation in the equation above is equal to 0 since f(v, w) and f(w, v) cancel each other out. Therefore, we conclude that

$$|f| = \sum_{(v,w)\in(S:\overline{S})} f(v,w),$$

as desired.

Furthermore, by the capacity constraint of f, we can write

$$|f| = \sum_{(v,w) \in (S:\overline{S})} f(v,w) \le \sum_{(v,w) \in (S:\overline{S})} u(v,w) = u(S:\overline{S}).$$

This completes the proof of the lemma.

In particular, if we take  $S = V \setminus \{t\}$  and  $\overline{S} = \{t\}$ , then Eq. (2) from Lemma 1 tells us that the flow coming from s is equal to the flow going to t. In other words, there is no loss in the flow of the network.

An important corollary to Lemma 1 comes from the observation that since the value of any flow f is always less than equal to the capacity of any s-t cut  $(S:\overline{S})$ , then it also holds for the case when f is a maximum flow and  $(S:\overline{S})$  is a minimum cut. This fact is known as the Weak-Duality Lemma.

Corollary 2 (Weak-Duality Lemma) Let G be a network with source vertex s and sink vertex t. Then

$$\max_{f} |f| \le \min_{(S:\overline{S})} u(S:\overline{S}),$$

where the maximum is taken over all possible flows and the minimum is taken over all possible s-t cuts in G.

## 4 The Max-Flow and Min-Cut Theorem

In this section, we show that the inequality in the Weak-Duality Lemma is actually an equality, that is, the maximum value of a net flow is equal to the minimum value of an s-t cut. This fact was first discovered in 1956 by Elias, Feinstein, and Shannon (see [EFS]), and independently by Ford and Fulkerson in the same year.

**Theorem 3 (Duality Theorem/Maxflow Mincut Theorem)** In a network G, the following equality holds:

$$\max_{f} |f| = \min_{(S:\overline{S})} u(S:\overline{S}).$$

In order to prove the theorem, we first have to introduce some new definitions. The first one is residual capacity, which denotes the extent to which a flow on some edge is less than the capacity on that edge.

**Definition 6** The residual capacity of G with respect to f is the function  $u_f: E \to \mathbb{R}$  defined by  $u_f(v, w) = u(v, w) - f(v, w)$  for all (v, w) in E. Hence, the residual capacity on the edge (v, w) is the amount of additional flow that we can push from v to w, without violating the capacity constraint.

We observe that the capacity constraint implies that  $u_f(v,w) = u(v,w) - f(v,w) = u(v,w) + f(w,v) \le u(v,w) + u(w,v)$ . Moreover, since f is a flow,  $u(v,w) \ge f(v,w)$ , so that  $u_f(v,w) \ge 0$ . Hence, the following inequality holds for any edge (v,w) in E:

$$0 \le u_f(v, w) \le u(v, w) + u(w, v).$$

All the edges with positive residual capacities are members of a set that we call the residual arcs.

**Definition 7** The residual arcs  $E_f$  of G with respect to f is the set given by  $E_f = \{(v, w) \in E : u_f(v, w) > 0\}$ . Intuitively, the residual arcs is the subset of E that contains those edges through which we can push a non-zero additional flow.

Given the vertices of a network G, its residual arcs, and its residual capacity, we can make a new network, the residual network.

**Definition 8** The residual network  $G_f$  of the network G with respect to f is the network given by the graph  $G_f = (V, E_f)$  together with the capacity function  $u_f$ .

The residual network is used to understand to what extent a flow is not maximal, and we do that by defining a certain kind of path in the residual network that we call augmenting path.

**Definition 9** An augmenting path of G with respect to f is a directed simple path from the source s to the sink t in the residual network  $G_f$ .

In fact, the existence of an augmenting path in a residual network for a given flow indicates that the flow is not maximal, as we prove in the following lemma.

**Lemma 4** If a residual network  $G_f$  has at least one augmenting path P, then f is not a maximum flow.

**Proof:** By definition, the residual network  $G_f$  includes only edges with non-zero residual capacity with respect to f. Therefore, an augmenting path P of  $G_f$  is a path through which we can push more flow in the original network G, and the additional amount of flow is upper bounded by the "bottleneck" of P.

More precisely, consider the quantity given by

$$\epsilon(P) = \min_{(v,w)\in P} u_f(v,w).$$

Observe that  $\epsilon(P) > 0$ , because  $P \subset E_f$  so that P is a finite set of positive real numbers.

Then, construct the flow f' given by

$$f'(v,w) = \begin{cases} f(v,w) + \epsilon(P) & \text{if } (v,w) \in P, \\ f(v,w) - \epsilon(P) & \text{if } (w,v) \in P, \\ f(v,w) & \text{otherwise.} \end{cases}$$

Note that f' is satisfies all the flow constraints for G. Moreover,  $|f'| = |f| + \epsilon(P) > |f|$ , so that the flow f is not a maximum flow.

Using Lemma 4 and the Weak-Duality Lemma, we prove now the Maxflow Mincut Theorem.

**Proof of Theorem 3:** Let f be a flow of maximal value for G = (V, E). By Lemma 4, the residual network  $G_f$  has no augmenting path, since, if it did, then f would not be of maximal value.

Consider the set S of vertices  $v \in V$  such that there exists a directed path from the source s to v in  $G_f$ . By definition,  $s \in S$ . Moreover,  $G_f$  has no augmenting path, so that  $t \notin S$ . Therefore,  $(S : \overline{S})$  is an s - t cut.

Now notice that  $u_f(v, w) = 0$  for any  $(v, w) \in (S : \overline{S})$ . By definition,  $u_f(v, w) = u(v, w) - f(v, w)$ , so that f(v, w) = u(v, w) for any  $(v, w) \in (S : \overline{S})$ . Thus, we can compute that

$$|f| = \sum_{(v,w) \in (S:\overline{S})} f(v,w) = \sum_{(v,w) \in (S:\overline{S})} u(v,w) = u(S:\overline{S}).$$

The Weak-Duality Lemma tells us that the value of any flow is upper bounded by the capacity of any s-t cut, so we can conclude that

$$\max_{f} |f| = \min_{(S:\overline{S})} u(S:\overline{S}).$$

We summarize all of the results in the following theorem.

**Theorem 5 (Max-Flow Min-Cut Theorem)** Let G be a network and f be a flow on G. Then, the following statements are equivalent:

- 1. f is a flow of maximal value;
- 2.  $G_f$  has no augmenting path; and
- 3.  $|f| = u(S : \overline{S})$  for some s t cut  $(S : \overline{S})$ .

**Proof:** We prove the equivalence of the statements by showing that  $(1) \Rightarrow (2) \Rightarrow (3) \Rightarrow (1)$ , that is:

- $(1) \Rightarrow (2)$ : This implication is the contrapositive of the implication proved in Lemma 4.
- $(2) \Rightarrow (3)$ : This implication follows from the proof of the Maxflow Mincut Theorem.
- $(3) \Rightarrow (1)$ : This implication follows from the Weak Duality Lemma.

## 5 The Ford-Fulkerson Algorithm

In 1956 Ford and Fulkerson used the Max-Flow Min-Cut Theorem to design an algorithm, called the Ford-Fulkerson algorithm, to compute the maximal flow of a network (see [FF]). The idea of their algorithm is very simple: as long as there is an augmenting path in the residual network we push more flow along that path in the original network. This idea is illustrated as pseudocode below.

FORD-FULKERSON(G)

- 1 start with a zero flow f (or any feasible flow)
- 2 while  $G_f$  has an augmenting path P
- 3 **do** push  $\epsilon(P)$  more units of flow through P, so that  $|f| \leftarrow |f| + \epsilon(P)$

Before we declare the idea above an algorithm, there are two issues that need to be addressed:

- 1. Does the algorithm ever halt?
- 2. If there is more than one augmenting path in the residual network, which one should we choose? And how does our decision affect the correctness and running time of the algorithm?

We consider three cases.

Case 1: Assume that the capacity function u of G is integer valued. Then we can make the following observations:

- 1. At every iteration of FORD-FULKERSON, the flow f is integer valued, and therefore so are the residual capacities. Indeed, this is the case at the beginning when f = 0, and by induction, this is maintained since  $\epsilon(P)$  is the minimum of a set of positive integers and thus a positive integer, and therefore the resulting flow after an augmentation is also integer valued.
  - Furthermore, since  $\epsilon(P) \ge 1$  (being a positive integer) and since the minimum-cut value (and thus the maximum flow value) is finite, it follows that the FORD-FULKERSON always halts.
- 2. Since the algorithm halts and every intermediate flow is integer valued, the maximum flow output will also be integer valued. That is, if the capacities of a network are integral then there is a maximum flow that is also integral. This is a very useful property that has many applications. One such application is the cardinality bipartite problem, as we will see in the next lecture.
- 3. The number of iterations is bounded by  $|f| \leq |N(s)|U \leq nU$ , where  $U = \max\{u(s,w) : w \in N(v)\}$ . Note that U may not be polynomial in the size of G. In fact, Figure 7 shows an example of a graph where FORD-FULKERSON takes exponential time to halt. The dotted and dashed lines represent paths from the source to the sink. The algorithm might choose alternatively and repeatedly the two paths as augmenting paths. In such a case, the algorithm will take  $O(2^L)$  time to terminate. Thus, we need a better policy to choose the augmenting path.
- Case 2: Assume that the capacity function u of G is **rational** valued. Then, a similar discussion as the one carried out in Case 2 shows that FORD-FULKERSON always halts, that the value of the maximal flow is rational, and that there exists an example of a network for which the running time is exponential. The arguments are similar because the rational capacities behave like integers if we consider them all as written with the same least common multiple.
- Case 3: Assume that the capacity function u of G is real valued. In the general case (i.e.  $u(E) \subset \mathbb{Q}_+$  is not necessarily true) there exist instances of networks such that FORD-FULKERSON never halts. Moreover, in such cases, the value of |f| may converge to a sub-optimal value.

Figure 7: An example of a network for which the Ford-Fulkerson algorithm may not halt in polynomial time (the reverse edges and the corresponding flows are not shown for clarity).

# 6 Fixing the Ford-Fulkerson Algorithm

The problems of the Ford-Fulkerson algorithm that we examined at the end of Section 5 can be addressed, at least in part, by specifying a policy for choosing the augmenting path at every iteration. A good policy must satisfy two properties:

- 1. It is possible to efficiently (e.g. in polynomial time) find the augmenting path specified by the policy; and
- 2. The maximum number of augmentations (and thus the total time) is polynomial.

In fact, we should be precise when we say that a running time is "polynomial", because it means different things depending on the model of computation. Also, ideally, we would like algorithms for which the number of operations does not depend on the size of the numbers involved in the input (e.g. the capacities in a maximum flow instance); such algorithms could be used even if the data was irrational (provided our model allows (arithmetic) operations on irrational data).

Given an instance I of a number problem (a computational problem involving numbers as input), let size(I) denote the number of bits needed to represent the input and number(I) denote the number of numbers involved in the input. For example, for a maximum flow instance, number(I) corresponds to the number m of edges while size(I) corresponds to the number of bits needed to represent all edge capacities. For the solution of an  $n \times n$  system of linear equations, number(I) will be  $n^2 + n$  ( $n^2$  for the matrix and n for the right-hand-side) while size(I) is the sum of the binary sizes of all the entries of the matrix and the right-hand-side.

We say that an algorithm A running on an instance I is (weakly) polynomial if

- the number of operations performed by A is at most polynomial in size(I) and
- the size of any number obtained during the execution of A is at most polynomial in size(I).

For an algorithm to be strongly polynomial, we require that

- the number of operations performed by A is at most polynomial in number(I) and
- the size of any number obtained during the execution of A is at most polynomial in size(I).

Thus, the two notions differ only in whether the number of operations performed depends on the size of the numbers in the input. For example, Gaussian elimination can be shown to be strongly polynomial for solving a system of equations (it is clear that the number of operations is at most  $O(n^3)$ , but one can also show that the size of the numbers obtained through the algorithm are polynomially bounded in the size of the input). On the other hand, Euclid's algorithm for computing the gcd is clearly not strongly polynomial (as only 2 numbers are involved), but is polynomial.

We now consider two policies for choosing the augmenting path in the Ford-Fulkerson algorithm. Both were proposed by Edmonds and Karp in 1972 [EK]. Both lead to polynomial algorithms, while the second leads to a strongly polynomial algorithm.

**Pick the Fattest:** Suppose that, in the case of integral capacities, at every iteration of the Ford-Fulkerson algorithm, we pick the "fattest" augmenting path, that is, a path P such that  $\epsilon(P)$  is maximized. Given this policy:

- By adapting Dijkstra's algorithm to find this *bottleneck* path rather than the shortest path, it is possible to find the augmenting path that maximizes  $\epsilon(P)$  in  $O(m+n\log n)$  time;
- It can be shown that the number of iterations is  $O(m \log U)$ , where U is a bound for the capacity function, yielding a running time for this fattest augmenting path algorithm of  $O((m + n \log n)m \log U)$ .

A similar argument works for rational capacities as well. However, for irrational capacities, the time complexity given above does not apply, and this analysis does not even show whether the algorithm terminates.

**Pick the Shortest:** Suppose that, in the case of integral capacities, at every iteration of the Ford-Fulkerson algorithm, we pick the "shortest" augmenting path, that is, a path P such that its number of edges is minimized. Given this policy, we observe that:

- Using breadth-first search, it is possible to find the augmenting path with a minimum number of edges in O(m) time (by breadth-first-search);
- It can be shown that the number of iterations is O(nm), yielding a running time for the algorithm of  $O(nm^2)$ . Thus this *shortest augmenting path* algorithm is **strongly polynomial** and therefore halts even if capacities are irrational.

Next time we will discuss more network flow problems.

### References

- [CLRS] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein, *Introduction to Algorithms*, Second Edition, MIT Press and McGraw-Hill, 2001.
- [EFS] P. Elias, A. Feinstein, and C. E. Shannon, *Note on maximum flow through a network*, IRE Transactions on Information Theory IT-2, 117–119, 1956.
- [EK] Jack Edmonds, and Richard M. Karp, Theoretical improvements in algorithmic efficiency for network flow problems, Journal of the ACM 19 (2): 248–264, 1972.
- [FF] L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canadian Journal of Mathematics 8: 399–404, 1956.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

| 18.415 | /6.854 | Advanced | Algorithms |
|--------|--------|----------|------------|
|        |        |          |            |

September 10, 2008

Lecture 3

Lecturer: Michel X. Goemans

## 1 Introduction

Today we continue our discussion of maximum flows by introducing the fattest path augmenting algorithm, an improvement over the Ford-Fulkerson algorithm, to solve the max flow problem. We also discuss the minimum cost circulation problem.

### 2 Maximum Flow

In a maximum flow problem, the goal is to find the greatest rate (flow) at which material can be sent from a source s to a sink t. Several problems can be modeled as a max-flow problem, including bipartite matching, which will be discussed today. We will also discuss flow decomposition and the fattest augmenting path algorithm.

## 2.1 Maximum Cardinality Matching in Bipartite Graphs

A bipartite graph is a graph G = (V, E) whose vertex set V can be partitioned into two disjoint sets, A and B, such that every edge connects a vertex in A to one in B. A matching M is a subset of E such that the endpoints of all the edges in M are distinct. In other words, two edges in M cannot share a vertex. We are interested in solving the following problem: Given an undirected bipartite graph G = (V, E) where  $V = A \cup B$ , find a matching M of maximum cardinality.

We can formulate this maximum cardinality matching problem as a max-flow problem. To do that, consider the network shown in Figure 1.

Figure 1: The figure on the left represents a matching in a bipartite graph. The figure on the right shows how the bipartite graph can be converted into a max-flow network by imposing a capacity of 1 on arcs out of s and into t.

The network is constructed as follows: We orient each edge in G from A to B and assign them a capacity of 1 (any capacity greater than 1 works too). We also add two new vertices, s and t, and arcs from s to every vertex in A, and from every vertex in B to t. All the new arcs are given unit capacity.

**Theorem 1** Let G = (V, E) be a bipartite graph with vertex partition  $V = A \cup B$ , and let G' = (V', E') be the capacitated network constructed as above. If M is a matching in G, then there is an integer-valued flow f in G' with value |f| = |M|. Conversely, if f is an integer-valued flow in G', then there is a matching M in G with cardinality |M| = |f|.

**Proof:** Given M, define a flow f in G' as follows: if  $(u,v) \in M$ , then set f(s,u) = f(u,v) = f(v,t) = 1 and f(u,s) = f(v,u) = f(t,v) = -1. For all other edges  $(u,v) \in E'$ , let f(u,v) = 0. Each edge  $(u,v) \in M$  corresponds to 1 unit of flow in G' that traverses the path  $s \to u \to v \to t$ . The paths in M have distinct vertices, aside from s and t. The net flow across the cut  $(A \cup s : B \cup t)$  is equal to |M|. We know that the net flow across any cut is the same, and equals the value of the flow. Thus, we can conclude that |M| = |f|. To prove the converse, let f be an integer-valued flow in G'. By flow conservation and the choice of capacities, the net flow in each arc must be -1, 0 or 1. Let f be the set of edges f capacities, where f is for which f capacities are argument as before, that f is indeed a matching and, using the same argument as before, that f is indeed a matching and, using the same argument as before, that

Since all the capacities of this maximum flow problem are integer valued, we know that there always exists an *integer-valued* maximum flow, and therefore the theorem shows that this maximum flow formulation correctly models the maximum cardinality bipartite matching.

### 2.2 Flow Decomposition

In an (raw) s-t flow, we have the following building blocks:

- Unit flow on an s-t directed path.
- Unit flow on a directed cycle.

Any (raw) s-t flow can be written as a linear combination of these building blocks.

**Theorem 2** Any (raw) s-t flow r can be decomposed into at most m flows along either paths from s to t or cycles, where m is the number of edges in the network. More precisely, it can be decomposed into at most  $|\{e: r(e) > 0\}| \le m$  paths and cycles.

**Proof:** By tracing back the flow on an edge e and tracing forward the flow on e, we either get an s-t path T, or a cycle T with r(e) > 0 for all  $e \in T$ . Denote the min flow on T by  $\Delta(T)$ :

$$\Delta(T) = \min_{e \in T} r(e).$$

We want to decrease the flow on T such that at least one edge goes to 0 (by subtracting out  $\Delta(T)$ ), and keep doing that until there are no more edges with non-zero flows. More precisely, the following algorithm extracts at most m paths and cycles.

- (i) While there is a directed cycle C with positive flow:
  - (a) Decrease the flow on this cycle by  $\Delta(C)$
  - (b) Add this cycle as an element of the flow decomposition
- (ii) (The set of arcs with positive flow now form an acyclic graph.) While there is a path P from s to t with positive flow:

- (a) Decrease the flow on this path by  $\Delta(P)$ .
- (b) Add this path as an element of the flow decomposition.

Each time we decrease the flow on a path or a cycle T, we zero out the flow on some edge. When we do this, the new raw flow is  $r^{\text{new}}(e) = r(e) - \Delta(T)$  if  $e \in T$ , or r(e) otherwise. Since there are  $|\{e: r(e) > 0\}| \le m$  edges with positive flow in the graph, there will be at most that number of decreases in the flow, and consequently, at most that number of paths or cycles in the flow decomposition.

## 2.3 Fattest Augmenting Path Algorithm (Edmonds-Karp '72)

Flow decomposition is a key tool in the analysis of network flow algorithms, as we will illustrate now.

As we saw in the last lecture, the Ford-Fulkerson algorithm for finding a maximum flow in a network may take exponential time, or even not terminate at all, if the augmenting path is not chosen appropriately. We proposed two specific choices of augmenting paths, both due to Edmonds and Karp, that provide a polynomial running time. One was the shortest augmenting path, the other was the *fattest* augmenting path or *maximum-capacity augmenting path*: the augmenting path that increases the flow the most. This is the variant we analyze now.

For an augmenting s-t path  $P \in G_f$ , define

$$\varepsilon(P) = \min_{(v,w)\in P} u_f(v,w)$$

where the  $u_f$  are the residual capacities. The minimum residual capacity  $\varepsilon(P)$  (the bottleneck) is the maximum flow that can be pushed along the path P. We wish to find the fattest augmenting path P such that  $\varepsilon(P)$  is maximized. The fattest augmenting path P can be efficiently found with Dijkstra's algorithm in  $O(m + n \log n)$  time <sup>1</sup>.

**Theorem 3** Assuming that capacities are integral and bounded by U, the optimal flow for a network can be found in  $O(m \log(mU)) = O(m \log(nU))$  iterations of augmenting along the fattest path.

**Proof:** Start with a zero flow, f = 0. Consider a maximum flow  $f^*$ . Its value is at most the value of any cut, which is bounded by mU:

$$|f^*| < mU$$
.

Consider the flow  $f^* - f$  (this is,  $f^*(e) - f(e)$  for all edges e) in the residual graph  $G_f$  with residual capacities  $u_f = u - f$ .

We can decompose  $f^* - f$  into  $\leq m$  flows using flow decomposition. As a result, at least one of these paths carry a flow of value at least  $\frac{1}{m}(|f^*| - |f|)$ . Suppose now that we push  $\varepsilon(P)$  units of flow along the fattest path in the residual graph  $G_f$  and obtain a new flow  $f^{\text{new}}$  of value:

$$|f^{\text{new}}| = |f| + \varepsilon(P).$$

Since the fattest path provides the greatest increase in flow value, we must have that  $\varepsilon(P) \geq \frac{1}{m}(|f^*| - |f|)$ . Thus we have the following inequality

$$|f^{\text{new}}| \ge |f| + \frac{1}{m}(|f^*| - |f|),$$

<sup>&</sup>lt;sup>1</sup>Actually, it can be found in O(m) time under the condition that we have the capacities sorted beforehand, see the forthcoming problem set.

which implies

$$\begin{split} |f^*| - |f^{\text{new}}| &= |f^*| - |f| + |f| - |f^{\text{new}}| \\ &\leq \left(1 - \frac{1}{m}\right) (|f^*| - |f|) \,. \end{split}$$

After k iterations, we get a flow  $\hat{f}$  such that

$$|f^*| - |\hat{f}| \le \left(1 - \frac{1}{m}\right)^k mU.$$

Eventually  $|f^*| - |\hat{f}| < 1$  which implies  $f^* = \hat{f}$  since, for integral capacities, all intermediate flows will be integral. Since  $(1 - \frac{1}{m})^m \le \frac{1}{e}$  for all  $m \ge 2$ , the number of iterations required for the difference to go below 1 is

$$k = m \log(mU)$$
.

Combining the results mentioned above we have the following corollary.

**Corollary 4** We can find a maximum flow in an integer-capacitated network with maximum capacity U in  $O((m + n \log n)m \log(nU))$  time <sup>2</sup>.

# 3 Minimum Cost Circulation Problem (MCCP)

A *circulation* is simply a flow where the net flow into every vertex (there are no sources or sinks) is zero. Notice that we can easily transform an s-t flow to a circulation by adding one arc from t to s (with infinite capacity) which carries a flow equal to the s-t flow value.

**Definition 1** A circulation f satisfies

- (i) Skew-Symmetry:  $\forall (v, w) \in E, f(v, w) = -f(w, v).$
- (ii) Flow Conservation:  $\forall v \in V, \sum_{w} f(v, w) = 0.$
- (iii) Capacity Constraints:  $\forall (v, w) \in E, f(v, w) \leq u(v, w).$

**Definition 2** A cost function  $c: E \mapsto \mathbb{R}$  assigns a cost per unit flow to each edge. We assume the cost function satisfies skew symmetry: c(v, w) = -c(w, v). For a set of edges C (e.g. a cycle), we denote the total cost of C by:

$$c(C) = \sum_{(v,w)\in C} c(v,w).$$

**Definition 3** The goal of the Minimum Cost Circulation Problem (MCCP) is to find a circulation f of minimum cost c(f) where

$$c(f) = \sum_{(v,w)} c(v,w) f(v,w).$$

The MCCP is a special case of a Linear Programming (LP) problem (an optimization problem with linear constraints and a linear objective function). But while no strongly polynomial time algorithms are known for linear programming, we will be able to find one for MCCP.

<sup>&</sup>lt;sup>2</sup>Using the previous footnote, we can do this in  $O(m^2 \log(nU))$  time.

### 3.1 Vertex Potentials

Before we can solve MCCP, it is necessary to introduce the concept of *vertex potentials*, or simply *potentials*.

**Definition 4** A vertex potential is a function  $p: V \mapsto \mathbb{R}$  that assigns each vertex a potential. The vertex potential defines a reduced cost function  $c_p$  such that

$$c_p(v, w) = c(v, w) + p(v) - p(w).$$

**Proposition 5** The function  $c_p$  satisfies the following properties:

- (i) Skew-Symmetry:  $c_p(v, w) = -c_p(w, v)$ .
- (ii) Cycle Equivalence: for a cycle C,  $c(C) = c_p(C)$ ; i.e., the reduced cost function agrees with the cost function.
- (iii) Circulation Equivalence: for all circulations, the reduced cost function agrees with the cost function,  $c(f) = c_p(f)$ .

**Proof:** The first property is trivial. The second property follows since all the potential terms cancel out. And we'll prove the third property. By definition

$$c_{p}(f) = \sum_{(v,w)} (c(v,w) + p(v) - p(w))(f(v,w))$$

$$= c(f) + \sum_{v} p(v) \sum_{w:(v,w) \in E} f(v,w) - \sum_{w} p(w) \sum_{v:(w,v) \in E} f(v,w).$$

Now by flow conservation, the inner sums are all zero. Hence  $c_p(f) = c(f)$ . (The third property also follows easily from flow decomposition, as the decomposition of a circulation only contains cycles and thus the cost and the reduced cost of a circulation are the same because of (ii).)

#### 3.2 Klein's Cycle-Cancelling Algorithm

We present a pseudo-algorithm for removing negative-cost cycles. While there exists a negative-cost cycle C in  $G_f$ , push a flow  $\varepsilon$  along the cycle C, where  $\varepsilon$  is the minimum residual flow:

$$\varepsilon = \min_{(v,w) \in C} u_f(v,w).$$

Of course, this doesn't lead to a straight-forward implementation, since we haven't specified which negative-cost cycle to select or how to find them. We should also consider whether the algorithm is efficient and whether it will terminate. We'll answer these questions in the next lecture. However, we will show now that if it terminates, then the circulation output is of minimum cost.

### 3.3 Optimality Conditions

We now present a theorem that specifies the conditions required for f to be a minimum cost circulation.

**Theorem 6 (Optimality Condition)** Let f be a circulation. The following are equivalent:

- (i) f is of minimum cost.
- (ii) There exists no negative-cost cycle in the residual graph  $G_f$ .

(iii) There exists a potential function p such that for all  $(v, w) \in E_f$ ,  $c_p(v, w) \ge 0$ .

**Proof:** To show that (i) implies (ii), we'll prove the contrapositive. Suppose there exists a negative cost cycle C in the residual graph  $G_f$  where f is the optimal circulation. Denote by C' the reverse cycle (i.e. following the arcs in the reverse order). We define a new circulation f' for any edge e as follows. If  $e \in C$ ,  $f'(e) = f(e) + \varepsilon$ . And if  $e \in C'$ , then  $f'(e) = f(e) - \varepsilon$ . Otherwise, let f'(e) = f(e).

Then we compute the cost of this new flow as

$$\begin{array}{rcl} c(f') & = & c(f) + (\varepsilon)(c(C)) + (-\varepsilon)(-c(C)) \\ & = & c(f) + 2\varepsilon c(C) \\ & < & c(f), \end{array}$$

where the last step follows since C is a negative cost cycle. Thus we've shown that f is indeed not optimal. Hence (i) implies (ii).

Now we show that (ii) implies (iii). Add zero-cost (or of arbitrary cost) arcs from a new vertex s to every vertex in  $G_f$  (this is to make sure that s can reach every vertex in V). Define a potential p such that p(v) is the length of the shortest simple path from s to v. Then, since there are no negative cost cycle, we have the optimality conditions for the shortest-path lengths:

$$p(w) \le p(v) + c(v, w) \ \forall (v, w) \in E_f$$

as one way to go from s to w is to go to v by a shortest path and then go directly to w.

Here, we have implicitly used the fact that  $G_f$  has no negative cost cycles. For if the shortest path from s to v already goes through w then adding (v, w), we create a cycle C (and the resulting path is not simple). However, this cycle can't be of negative cost by assumption. Thus, by removing it, we obtain a simple path to w of cost less or equal to p(v) + c(v, w). Rearranging the inequality gives the desired result

$$c_p(v, w) \ge 0 \ \forall (v, w) \in E_f$$
.

Now we prove that (iii) implies (i) by showing the contrapositive. Suppose we have an optimal circulation  $f^*$  and a suboptimal one f:  $c(f^*) < c(f)$ . Consider the cost of the circulation  $f^* - f$ :

$$\begin{split} c(f^*-f) &= c_p(f^*-f) \\ &= \sum_{(v,w)\in E} c_p(v,w)[f^*(v,w)-f(v,w)] \\ &= 2\sum_{(v,w):f^*-f>0} c_p(v,w)[f^*(v,w)-f(v,w)] \\ &\geq 0 \end{split}$$

by (iii). Note that in the second to last step, we utilized the skew-symmetry of the cost of reverse arcs (with flows of opposite parity). But since  $f^*$  is supposed to be strictly better than f, we have a contradiction.

## References

[EK72] Jack Edmonds, and Richard M. Karp, Theoretical improvements in algorithmic efficiency for network flow problems, Journal of the ACM 19 (2): 248–264, 1972.

[Klein67] Klein, M. A primal method for minimum cost flows with application to the assignment and transportation problem. Management Science 14: 205-220, 1967.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# Goldberg-Tarjan Min-Cost Circulation Algorithm

Lecturer: Michel X. Goemans

### 1 Introduction

In this lecture we shall study Klein's cycle cancelling algorithm for finding the circulation of minimum cost in greater detail. We will pay particular attention to the choice of cycle to cancel and we will rigorously prove two bounds on the number of iterations required, the first of which depends on the magnitude of the cost and is valid only for integer-valued costs, and the second of which is strongly polynomial and works even for irrational costs.

Recall from last time that for a given circulation f, the following are equivalent:

- i. f is of minimum cost
- ii. There is no negative cost cycle in the residual graph  $G_f$
- iii. There exist potentials  $p: V \to \mathbb{R}$  such that the reduced costs

$$c_p(v, w) = c(v, w) + p(v) - p(w) \ge 0$$

for all  $(v, w) \in E_f$ , where  $E_f = \{e : u_f(e) > 0\}$ .

## 2 Klein's cycle cancelling algorithm

#### **Algorithm 1** Kleins-Cycle-Cancel( $G_f$ )

```
Let f be any circulation (e.g., f = 0)
while there exists a negative cost cycle \Gamma \in G_f do
Push \epsilon(f) = \min_{(v,w) \in \Gamma} u_f(v,w) along \Gamma
```

end while

It is important to note that the Ford-Fulkerson algorithm for the maximum flow problem is a special case of Klein's cycle cancelling algorithm, by defining zero costs for all edges in the original graph and by adding an extra edge from the sink to the source with cost -1.

#### 2.1 Choice of cycle $\Gamma$

As in the Ford-Fulkerson algorithm, the question is which negative-cost cycle to choose.

1. (Weintraub 1972). One idea is to try choosing the **maximum improvement cycle**, where the difference in cost is as large as possible. One can show that the number of iterations is polynomial for rational costs, but finding such a cycle is NP-hard. For irrational costs, one can show that this algorithm may never terminate (Queyranne 1980) even for the maximum flow problem (the fattest augmenting path algorithm of Edmonds and Karp), although the solution converges to a minimum cost flow.

2. (Goldberg-Tarjan 1986). Alternatively, we can choose the **cycle of minimum mean cost**, defined as follows:

$$\mu(f) = \min_{\text{directed cycles } \Gamma \in G_f} \frac{c(\Gamma)}{|\Gamma|}$$

where  $c(\Gamma) = \sum_{(v,w) \in \Gamma} c(v,w)$  and  $|\Gamma|$  is the number of edges in the cycle.

Notice that there exists a negative cost cycle in  $G_f$  if and only if  $\mu(f)$  is negative.

To see that we can indeed find the minimum mean-cost cycle efficiently, suppose we replace the costs c with c' such that  $c'(v, w) = c(v, w) + \Delta$  for each edge (v, w). Then  $\mu'(f) = \mu(f) + \Delta$ , so if  $\Delta = -\mu(f)$  then we would have  $\mu'(f) = 0$ . In particular,

$$\mu(f) = -\inf\{\Delta : \text{ there is no negative cost cycle in } G_f \text{ with respect to costs } c + \Delta\}.$$

For any  $\Delta$ , we can decide if there is a negative cost cycle by using the Bellman-Ford algorithm. Now, perform binary search to find the smallest  $\Delta$  for which no such cycle exists. In the next problem set we will show a result by Karp, which finds the cycle of minimum mean cost in O(nm) time by using a variant of Bellman-Ford.

#### 2.2 Bounding the number of iterations

We will give two bounds on the number of iterations for the algorithm. The first depends on the magnitude of the cost and is valid only for integer-valued costs; it is polynomial but not strongly polynomial. The second bound is strongly polynomial and works even for irrational costs.

We first need a measure of 'closeness' to the optimal circulation. The following definition gives such a measure, and will be key in quantifying the progress of the algorithm.

**Definition 1 (Relaxed optimality)** A circulation f is said to be  $\epsilon$ -optimal if there exists a potential  $p: V \to \mathbb{R}$  such that  $c_p(v, w) \ge -\epsilon$  for all edges  $(v, w) \in E_f$ .

Note that an 0-optimal circulation is of minimum cost.

**Definition 2** For a circulation f, let

$$\epsilon(f) = \min\{\epsilon : f \text{ is } \epsilon\text{-optimal}\}.$$

One important thing about this that we will prove soon is that when we push some flow in a circulation f along some cycle  $\Gamma$  and obtain a new circulation f', we get that  $\epsilon(f') \leq \epsilon(f)$ . This means that  $\epsilon$  is monotonically non-increasing in general. First, we need the following strong relationship between  $\epsilon(f)$  and  $\mu(f)$ , and this really justifies the choice of cycle of Goldberg and Tarjan.

**Theorem 1** For all circulations f,  $\epsilon(f) = -\mu(f)$ .

**Proof:** We first show that  $\mu(f) \geq -\epsilon(f)$ . From the definition of  $\epsilon(f)$  there exists a potential  $p: V \to \mathbb{R}$  such that  $c_p(v, w) \geq -\epsilon(f)$  for all  $(v, w) \in E_f$ . For any cycle  $\Gamma \subseteq E_f$  the cost  $c(\Gamma)$  is equal to the reduced cost  $c_p(\Gamma)$  since the potentials cancel. Therefore  $c(\Gamma) = c_p(\Gamma) \geq -|\Gamma|\epsilon(f)$  and so  $\frac{c(\Gamma)}{|\Gamma|} \geq -\epsilon(f)$  for all cycles  $\Gamma$ . Hence  $\mu(f) \geq -\epsilon(f)$ .

so  $\frac{c(\Gamma)}{|\Gamma|} \geq -\epsilon(f)$  for all cycles  $\Gamma$ . Hence  $\mu(f) \geq -\epsilon(f)$ . Next, we show that  $\mu(f) \leq -\epsilon(f)$ . For this, we start with the definition of  $\mu(f)$ . For every cycle  $\Gamma \in E_f$  it holds that  $\frac{c(\Gamma)}{|\Gamma|} \geq \mu(f)$ . Let  $c'(v, w) = c(v, w) - \mu(f)$  for all  $(v, w) \in E_f$ . Then,  $\frac{c'(\Gamma)}{|\Gamma|} = \frac{c(\Gamma)}{|\Gamma|} - \mu(f) \geq 0$  for any cycle  $\Gamma$ . Now define p(v) as the cost of the shortest path from an added source s to v with respect to c' in  $G_f$  (see Fig. 1); the reason we add a vertex s is to make sure that every vertex can be reached (by the direct path). Note that the shortest paths are well-defined since there are no negative cost cycles with respect to c'. By the optimality property of shortest

Figure 1: p(v) is the length of the shortest path from s to v.

paths,  $p(w) \le p(v) + c'(v, w) = p(v) + c(v, w) - \mu(f)$ . Therefore  $c_p(v, w) \ge \mu(f)$  for all  $(v, w) \in E_f$  which implies that f is  $-\mu(f)$ -optimal and thus  $\epsilon(f) \le -\mu(f)$ .

By combining 
$$\mu(f) \geq -\epsilon(f)$$
 and  $\epsilon(f) \leq -\mu(f)$  we conclude  $\epsilon(f) = -\mu(f)$  as required.

The nature of the algorithm is to push flow along negative cost cycles. We would like to know if this actually gets us closer to optimality. This is shown in the following remark.

**Remark 1 (Progress)** Let f be a circulation. If we push flow along the minimum mean cost cycle  $\Gamma$  in  $G_f$  and obtain circulation f' then  $\epsilon(f) \geq \epsilon(f')$ .

**Proof:** By definition  $\frac{c_p(\Gamma)}{|\Gamma|} = \frac{c(\Gamma)}{|\Gamma|} = \mu(f)$ . Now,  $\epsilon(f) = -\mu(f)$  implies that there exists a potential p such that  $c_p(v, w) \geq \mu(f)$  for all  $(v, w) \in E_f$ . Furthermore for all  $(v, w) \in \Gamma$  the reduced cost  $c_p(v, w) = \mu(f) = -\epsilon(f)$ . If flow is pushed along  $\Gamma$  some arcs may be saturated and disappear from the residual graph. On the other hand, new edges may be created with a reduced cost of  $+\epsilon(f)$ . More formally,  $E_{f'} \subseteq E_f \cup \{(w, v) : (v, w) \in \Gamma\}$ . So for all  $(v, w) \in E_{f'}$  it holds that  $c_p(v, w) \geq -\epsilon(f)$ . Thus we have that  $\epsilon(f') \leq \epsilon(f)$ .

#### 2.3 Analysis for Integer-valued Costs

We now prove a polynomial bound on the number of iterations for an integer cost function  $c: E \to \mathbb{Z}$ . At the start, for any circulation, the following holds for all  $(v, w) \in E$ :

$$\epsilon(f) \le C = \max_{(v,w) \in E} |c(v,w)|.$$

Now we can continue with the rest of the analysis.

**Lemma 2** If costs are integer valued and  $\epsilon(f) < \frac{1}{n}$  then f is optimal.

**Proof:** Consider  $-\epsilon(f) = \mu(f) > -\frac{1}{n}$ . For any cycle  $\Gamma \in G_f$  we have  $c(\Gamma) = c_p(\Gamma) > -\frac{1}{n}|\Gamma| \ge -1$ . Since the cost is an integer,  $c(\Gamma) \ge 0$ . By the optimality condition, if there is no negative cycle in the graph, the circulation is optimal.

**Lemma 3** Let f be a circulation and let f' be the circulation after m iterations of the algorithm. Then  $\epsilon(f') \leq (1 - \frac{1}{n})\epsilon(f)$ .

**Proof:** Let p be the potential such that  $c_p(v, w) \geq -\epsilon(f)$  for all  $(v, w) \in E_f$  and let  $\Gamma_i$  and  $f_i$  be the cycle that is cancelled and the circulation obtained at the ith iteration, respectively. Let A be the set of edges in  $E_{f_i}$  such that  $c_p(v, w) < 0$  (we should emphasize that this is for the p corresponding to the circulation f we started from). We now show that as long as  $\Gamma_i \subseteq A$ , then |A| strictly decreases. This is because cancelling a cycle removes at least one arc with a negative reduced cost from A and any new arc added to  $E_{f_i}$  must have a positive reduced cost. Hence after

 $k \leq m$  iterations we will find an edge  $(v, w) \in \Gamma_{k+1}$  such that  $c_p(v, w) \geq 0$ . So by Theorem 1,  $-\epsilon(f_k)$  is equal to the mean cost of  $\Gamma_{k+1}$  and thus

$$\epsilon(f_k) = -\mu(f_k) = -\frac{c(\Gamma_{k+1})}{|\Gamma_{k+1}|} = -\frac{c_p(\Gamma_{k+1})}{|\Gamma_{k+1}|}$$

$$\leq -\frac{0 + (-\epsilon(f))(|\Gamma_{k+1}| - 1)}{|\Gamma_{k+1}|}$$

$$\leq \left(1 - \frac{1}{n}\right)\epsilon(f).$$

Corollary 4 If the costs are integer, then the number of iterations is at most  $mn \log(nC)$ .

**Proof:** We have that

$$\epsilon(f_{end}) \le \left(1 - \frac{1}{n}\right)^{n\log(nC)} \epsilon(f = 0) < e^{-\log(nC)}|C| = \frac{1}{nC}|C| = \frac{1}{n},$$

and thus the resulting circulation is optimal.

The time per iteration will be shown to be O(nm) (see problem set), hence the total running time of the algorithm is  $O(m^2n^2\log(nC))$ .

#### 2.4 Strongly Polynomial Analysis

In this section we will remove the dependence on the costs. We will obtain a strongly polynomial bound for the algorithm for solving the minimum cost circulation problem. In fact we will show that this bound will hold even for irrational capacities. The first strongly polynomial-time analysis is due to Tardos; the one here is due to Goldberg-Tarjan. This result was very significant, since it was the most general subclass of Linear Programming (LP) for which a strongly polynomial-time algorithm was shown to exist. It remains a big open problem whether a strongly polynomial-time algorithm exists for general LP.

**Definition 3** An edge e is  $\epsilon$ -fixed if for all  $\epsilon$ -optimal circulations f we have that f(e) maintains the same value.

Note that (v, w) is  $\epsilon$ -fixed if and only if (w, v) is  $\epsilon$ -fixed, by skew-symmetry of edge-costs.

**Theorem 5** Let f be a circulation and p be a potential such that f is  $\epsilon(f)$ -optimal with respect to p. Then if  $|c_p(v,w)| \geq 2n\epsilon$  for some edge  $(v,w) \in E$ , the edge (v,w) is  $\epsilon$ -fixed.

**Proof:** Suppose (v, w) is not  $\epsilon(f)$ -fixed. There exists an f' that is  $\epsilon(f)$ -optimal and  $f'(v, w) \neq f(v, w)$ ; without loss of generality assume f'(v, w) < f(v, w). Let  $E_{<} = \{(x, y) : f'(x, y) < f(x, y)\}$ . We can see that  $E_{<} \subseteq E_{f'}$  by definition of  $E_{f'}$ . Furthermore, from flow conservation, we know that there exists a cycle  $\Gamma \in E_{f'}$  containing the edge (v, w). Indeed, by flow decomposition, we know that the circulation f - f' can be decomposed into (positive net) flows along cycles of  $E_{f'}$ , and thus one of these cycles must contain (v, w)

Now we have the following.

$$c(\Gamma) = c_p(\Gamma) \le -2n\epsilon(f) + (n-1)\epsilon(f) < -n\epsilon(f).$$

Consequently,  $\frac{c(\Gamma)}{|\Gamma|} < -\epsilon$  and so  $\mu(f') < -\epsilon$ . As a result, f' is not  $\epsilon(f)$ -optimal and thus we have a contradiction.

**Lemma 6** After  $O(mn \log n)$  iterations, another edge becomes fixed.

**Proof:** Let f be a circulation and f' be another circulation after application of  $mn\log(2n)$  iterations of the Goldberg-Tarjan algorithm. Also suppose that  $\Gamma$  is the first cycle cancelled and p,p' are the potentials for f,f' respectively. From the previous lemma, we have that  $\epsilon(f') \leq (1-\frac{1}{n})^{n\log(2n)}\epsilon(f) < e^{-\log(2n)} = \frac{1}{2n}\epsilon(f)$ . Now from the definition of  $\mu$  we get the following,

$$\frac{c_{p'}(\Gamma)}{|\Gamma|} = \frac{c(\Gamma)}{|\Gamma|} = \mu(f) = -\epsilon(f) < -2n\epsilon(f')$$

This means that there exists an edge  $(v, w) \in \Gamma$  such that  $c_{p'}(v, w) < -2n\epsilon(f')$  which means that it was not  $\epsilon(f)$ -fixed. Thus (v, w) becomes  $\epsilon(f')$ -fixed and the claim is proven.

Notice that if e is fixed, it will remain fixed as we iterate the algorithm. An immediate consequence of the above lemma then is a bound on the number of iterations in the Goldberg-Tarjan algorithm.

**Corollary 7** The number of iterations of the Goldberg-Tarjan algorithm, even with irrational costs, is  $O(m^2 n \log n)$ .

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### 18.415/6.854 Advanced Algorithms

September 17, 2008

## Lecture 5

Lecturer: Michel X. Goemans

Today, we continue the discussion of the minimum cost circulation problem. We first review the Goldberg-Tarjan algorithm, and improve it by allowing more flexibility in the selection of cycles. This gives the Cancel-and-Tighten algorithm. We also introduce splay trees, a data structure which we will use to create another data structure, dynamic trees, that will further improve the running time of the algorithm.

# 1 Review of the Goldberg-Tarjan Algorithm

Recall the algorithm of Golberg and Tarjan for solving the minimum cost circulation problem:

- 1. Initialize the flow with f = 0.
- 2. Repeatedly push flow along the minimum mean cost cycle  $\Gamma$  in the residual graph  $G_f$ , until no negative cycles exist.

We used the notation

$$\mu(f) = \min_{\text{cycle } \Gamma \subseteq E_f} \frac{c(\Gamma)}{|\Gamma|}$$

to denote the minimum mean cost of a cycle in the residual graph  $G_f$ . In each iteration of the algorithm, we push as much flow as possible along the minimum mean cost cycle, until  $\mu(f) \geq 0$ .

We used  $\epsilon(f)$  to denote the minimum  $\epsilon$  such that f is  $\epsilon$ -optimal. In other words

$$\epsilon(f) = \min\{\epsilon : \exists \text{ potential } p : V \to \mathbb{R} \text{ such that } c_p(v, w) \ge -\epsilon \text{ for all edges } (v, w) \in E_f\}.$$

We proved that for all circulations f,

$$\epsilon(f) = -\mu(f).$$

A consequence of this equality is that there exists a potential p such that any minimum mean cost cycle  $\Gamma$  satisfies  $c_p(v, w) = -\epsilon(f) = \mu(f)$  for all  $(v, w) \in \Gamma$ , since the cost of each edge is bounded below by mean cost of the cycle.

### 1.1 Analysis of Goldberg-Tarjan

Let us recall the analysis of the above algorithm. This will help us to improve the algorithm in order to achieve a better running time. Please refer to the previous lecture for the details of the analysis.

We used  $\epsilon(f)$  as an indication of how close we are to the optimal solution. We showed that  $\epsilon(f)$  is a non-increasing quantity, that is, if f' is obtained by f after a single iteration, then  $\epsilon(f') \leq \epsilon(f)$ . It remains to show that  $\epsilon(f)$  decreases "significantly" after several iterations.

**Lemma 1** Let f be any circulation, and f' be the circulation obtained after m iterations of the Goldberg-Tarjan algorithm. Then

$$\epsilon(f') \le \left(1 - \frac{1}{n}\right)\epsilon(f).$$

We showed that if the costs are all integer valued, then we are done as soon as we reach  $\epsilon(f) < \frac{1}{n}$ . Using these two facts, we showed that the number of iterations of the above algorithm is at most  $O(mn\log(nC))$ . An alternative analysis using  $\epsilon$ -fixed edges provides a strongly polynomial bound of  $O(m^2n\log n)$  iterations. Finally, the running time per a single iteration is O(mn) using a variant of Bellman-Ford (see problem set).

## 1.2 Towards a faster algorithm

In the above algorithm, a significant amount of time is used to compute the minimum cost cycle. This is unnecessary, as our goal is simply to cancel enough edges in order to achieve a "significant" improvement in  $\epsilon$  once every several iterations.

We can improve the algorithm by using a more flexible selection of cycles to cancel. The idea of the Cancel-and-Tighten algorithm is to push flows along cycles consisting entirely of negative cost edges. For a given potential p, we push as much flow as possible along cycles of this form, until no more such cycles exist, at which point we update p and repeat.

## 2 Cancel-and-Tighten

## 2.1 Description of the Algorithm

**Definition 1** An edge is admissible with respect to a potential p if  $c_p(v, w) < 0$ . A cycle  $\Gamma$  is admissible if all the edges of  $\Gamma$  are admissible.

#### Cancel and Tighten Algorithm (Goldberg and Tarjan):

- 1. Initialization:  $f \leftarrow 0, p \leftarrow 0, \epsilon \leftarrow \max_{(v,w) \in E} c(v,w)$ , so that f is  $\epsilon$ -optimal respect to p.
- 2. While f is not optimum, i.e.,  $G_f$  contains a negative cost cycle, do:
  - (a) Cancel: While  $G_f$  contains a cycle  $\Gamma$  which is admissible with respect to p, push as much flow as possible along  $\Gamma$ .
  - (b) Tighten: Update p to p' and  $\epsilon$  to  $\epsilon'$ , where p' and  $\epsilon'$  are chosen such that  $c_{p'}(v, w) \geq -\epsilon'$  for all edges  $(v, w) \in E_f$  and  $\epsilon' \leq \left(1 \frac{1}{n}\right)\epsilon$ .

**Remark 1** We do not update the potential p every time we push a flow. The potential p gets updated in the tighten step after possibly several flows are pushed through in the Cancel step.

**Remark 2** In the tighten step, we do not need to find p' and  $\epsilon'$  such that  $\epsilon'$  is as small as possible; it is only necessary to decrease  $\epsilon$  by a factor of at least  $1 - \frac{1}{n}$ . However, in practice, one tries to decrease  $\epsilon$  by a smaller factor in order to obtain a better running time.

Why is it always possible to obtain improvement factor of  $1 - \frac{1}{n}$  in each iteration? This is guaranteed by the following result, whose proof is similar to the proof used in the analysis during the previous lecture.

**Lemma 2** Let f be a circulation and f' be the circulation obtained by performing the Cancel step. Then we cancel at most m cycles, and

$$\epsilon(f') \le \left(1 - \frac{1}{n}\right)\epsilon(f).$$

**Proof:** Since we only cancel admissible edges, after any cycle is canceled in the Cancel step:

- All new edges in the residual graph are non-admissible, since the edge costs are skew-symmetric;
- At least one admissible edge is removed from the residual graph, since we push the maximum possible amount of flow through the cycle.

Since we begin with at most m admissible edges, we cannot cancel more than m cycles, as each cycle canceling reduces the number of admissible edges by at least one.

After the cancel step, every cycle  $\Gamma$  contains at least one non-admissible edge, say  $(u_1, v_1) \in \Gamma$  with  $c_p(u_1, v_1) \geq 0$ . Then the mean cost of  $\Gamma$  is

$$\frac{c(\Gamma)}{|\Gamma|} \ge \frac{1}{|\Gamma|} \sum_{(u_1, v_1) \ne (u, v) \in \Gamma} c_p(u, v) \ge \frac{-(|\Gamma| - 1)}{|\Gamma|} \epsilon(f) = -\left(1 - \frac{1}{|\Gamma|}\right) \epsilon(f) \ge -\left(1 - \frac{1}{n}\right) \epsilon(f).$$

Therefore, 
$$\epsilon(f') = -\mu(f') \leq \left(1 - \frac{1}{n}\right) \epsilon(f)$$
.

## 2.2 Implementation and Analysis of Running Time

#### 2.2.1 Tighten Step

We first discuss the Tighten step of the Cancel-and-Tighten algorithm. In this step, we wish to find a new potential function p' and a constant  $\epsilon'$  such that  $c_{p'}(v,w) \geq -\epsilon'$  for all edges  $(v,w) \in E_f$  and  $\epsilon' \leq \left(1 - \frac{1}{n}\right)\epsilon$ . We can find the smallest possible  $\epsilon'$  in O(mn) time by using a variant of the Bellman-Ford algorithm. However, since we do not actually need to find the best possible  $\epsilon'$ , it is possible to vastly reduce the running time of the Tighten step to O(n), as follows.

When the Cancel step terminates, there are no cycles in the admissible graph  $G_a = (V, A)$ , the subgraph of the residual graph with only the admissible edges. This implies that there exists a topological sort of the admissible graph. Recall that a topological sort of a directed acyclic graph is a linear ordering  $l: V \to \{1, \ldots, n\}$  of its vertices such that l(v) < l(w) if (v, w) is an edge of the graph; it can be achieved in O(m) time using a standard topological sort algorithm (see, e.g., CLRS page 550). This linear ordering enables us to define a new potential function p' by the equation  $p'(v) = p(v) - l(v)\epsilon/n$ . We claim that this potential function satisfies our desired properties.

**Claim 3** The new potential function  $p'(v) = p(v) - l(v)\epsilon/n$  satisfies the property that f is  $\epsilon'$ -optimal with respect to p' for some constant  $\epsilon' \leq (1 - 1/n)\epsilon$ .

**Proof:** Let  $(v, w) \in E_f$ , then

$$c_{p'}(v, w) = c(v, w) + p'(v) - p'(w)$$
  
=  $c(v, w) + p(v) - l(v)\epsilon/n - p(w) + l(w)\epsilon/n$   
=  $c_p(v, w) + (l(w) - l(v))\epsilon/n$ .

We consider two cases, depending on whether or not l(v) < l(w).

Case 1: l(v) < l(w). Then

$$c_{p'}(v, w) = c_p(v, w) + (l(w) - l(v))\epsilon/n$$
  

$$\geq -\epsilon + \epsilon/n$$
  

$$= -(1 - 1/n)\epsilon.$$

Case 2: l(v) > l(w), so that (v, w) is not an admissible edge. Then

$$c_{p'}(v, w) = c_p(v, w) + (l(w) - l(v))\epsilon/n$$
  

$$\geq 0 - (n - 1)\epsilon/n$$
  

$$= -(1 - 1/n)\epsilon.$$

In either case, we see that f is  $\epsilon'$ -optimal with respect to p', where  $\epsilon' \leq (1 - 1/n)\epsilon$ .

#### 2.2.2 Cancel Step

We now shift our attention to the implementation and analysis of the Cancel step. Naïvely, it takes O(m) time to find a cycle in the admissible graph  $G_a = (V, A)$  (e.g., using Depth-First Search) and push flow along it. Using a more careful implementation of the Cancel step, we shall show that each cycle in the admissible graph can be found in an "amortized" time of O(n).

We use a Depth-First Search (DFS) approach, pushing as much flow as possible along an admissible cycle and removing saturated edges, as well as removing edges from the admissible graph whenever we determine that they are not part of any cycle. Our algorithm is as follows:

Cancel  $(G_a = (V, A))$ : Choose an arbitrary vertex  $u \in V$ , and begin a DFS rooted at u.

- 1. If we reach a vertex v that has no outgoing edges, then we backtrack, deleting from A the edges that we backtrack along, until we find an ancestor r of v for which there is another child to explore. (Notice that every edge we backtrack along cannot be part of any cycle.) Continue the DFS by exploring paths outgoing from r.
- 2. If we find a cycle  $\Gamma$ , then we push the maximum possible flow through it. This causes at least one edge along  $\Gamma$  to be saturated. We remove the saturated edges from A, and start the depth-first-search from scratch using  $G'_a = (V, A')$ , where A' denotes A with the saturated edges removed.

Every edge that is not part of any cycle is visited at most twice (since it is removed from the admissible graph the second time), so the time taken to remove edges that are not part of any cycle is O(m). Since there are n vertices in the graph, it takes O(n) time to find a cycle (excluding the time taken to traverse edges that are not part of any cycle), determine the maximum flow that we can push through it, and update the flow in each of its edges. Since at least one edge of A is saturated and removed every time we find a cycle, it follows that we find at most m cycles. Hence, the total running time of the Cancel step is O(m + mn) = O(mn).

#### 2.2.3 Overall Running Time

From the above analysis, we see that the Cancel step requires O(mn) time per iteration, whereas the Tighten step only requires O(m) time per iteration. In the previous lecture, we determined that the Cancel-and-Tighten algorithm requires  $O(\min(n \log(nC), mn \log n))$  iterations. Hence the overall running time is  $O(\min(mn^2 \log(nC), m^2 n^2 \log n))$ .

Over the course of the next few lectures, we will develop data structures that will enable us to reduce the running time of a single Cancel step from O(mn) to  $O(m \log n)$ . Using dynamic trees, we can reduce the running time of the Cancel step to an amortized time of  $O(\log n)$  per cycle canceled. This will reduce the overall running time to  $O(\min(mn \log(nC) \log n, m^2 n \log^2 n))$ .

# 3 Binary Search Trees

In this section, we review some of the basic properties of binary search trees and the operations they support, before introducing splay trees. A Binary Search Tree (BST) is a data structure that maintains a dictionary. It stores a collection of objects with ordered keys. For an object (or node) x, we use key[x] to denote the key of x.

**Property of a BST.** The following invariant must always be satisfied in a BST:

- If y lies in the left subtree of x, then  $key[y] \leq key[x]$
- If z lies in the right subtree of x, then  $key[z] \ge key[x]$

**Operations on a BST.** Here are some operations typically supported by a BST:

- FIND(k): Determines whether the BST contains an object x with key[x] = k; if so, returns the object, and if not, returns false.
- INSERT(x): Inserts a new node x into the tree.
- Deletes x from the tree.
- MIN: Finds the node with the minimum key from the tree.
- Max: Finds the node with the minimum key from the tree.
- Successor(x): Find the node with the smallest key greater than key[x].
- PREDECESSOR(x): Find the node with the greatest key less than key[x].
- Split(x): Returns two BSTs: one containing all the nodes y where key[y] < key[x], and the other containing all the nodes z where  $key[z] \ge key[x]$ .
- JOIN $(T_1, x, T_2)$ : Given two BSTs  $T_1$  and  $T_2$ , where all the keys in  $T_1$  are at most key[x], and all the keys in  $T_2$  are at least key[x], returns a BST containing  $T_1, x$  and  $T_2$ .

For example, the procedure FIND(k) can be implemented by traversing through the tree, and branching to the left (resp. right) if the current node has key greater than (resp. less than) k. The running time for many of these operations is linear in the height of the tree, which can be as high as O(n) in the worst case, where n is the number of nodes in the tree.

A balanced BST is a BST whose height is maintained at  $O(\log n)$ , so that the above operations can be run in  $O(\log n)$  time. Examples of BSTs include Red-Black trees, AVL trees, and B-trees.

In the next lecture, we will discuss a data structure called *splay trees*, which is a self-balancing BST with amortized cost of  $O(\log n)$  per operation. The idea is that every time a node is accessed, it gets pushed up to the root of the tree.

The basic operations of a splay tree are *rotations*. They are illustrated the following diagram.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### 18.415/6.854 Advanced Algorithms

September 24, 2008

# Lecture 6 - Splay Trees

Lecturer: Michel X. Goemans

## 1 Introduction

In this lecture, we investigate **splay trees**, a type of binary search tree (BST) first formulated by Sleator and Tarjan in 1985. Splay trees are self-adjusting BSTs that have the additional helpful property that more commonly accessed nodes are more quickly retrieved. They have good behavior when compared to many other types of self-balancing BSTs, even when the operations are unknown and non-uniform. While in the worst case, operations can take O(n) time, splay trees maintain  $O(\log n)$  amortized cost for basic BST operations, and are within a constant factor to the cost of any static BST.

We first give an overview of the operations used in splay trees, then give an amortized analysis of its behavior. We conclude by noting its behavior relative to other Binary Search Trees.

# 2 Splay Tree Structure

A splay tree is a dynamic binary search tree, meaning that it performs additional operations to optimize behavior. Because they are BSTs, given a node x in a splay tree and a node y in the left subtree of x, we have key(y) < key(x). Similarly, for a node z in the right subtree of x, we have key(z) < key(z). This is the binary search tree property. A well-balanced splay tree will have height  $\Theta(\log(n))$ , where n is the number of nodes.

Splay trees achieve their efficiency through use of the following operations:

#### 2.1 Rotation

The basic operation used in splay trees (or any other dynamic BST) is the **rotation**. A rotation involves rearranging the nodes of a subtree rooted at y so that one of the children x of y becomes the new root of the subtree, while maintaining the binary search tree property. This is illustrated in Figure 1.

When the left child becomes the new root, the rotation is a right rotation. When the right child becomes the new root, the rotation is a left rotation. We call a right rotation a **zig** and a left rotation a **zag**.

The key idea of the splay tree is to bring node x to the root of the tree when accessing x via rotations. This brings the most recently accessed nodes closer to the top of the tree.

However, there are many ways of bringing a node to the root via rotations, and we must therefore specify in which order we perform them. Consider a linear tree (effectively a linked list) of the values  $1, \ldots, n$ , rooted at n. Suppose we access the value 1. If we use the naive (and most natural) method of repeatedly performing a zig to bring 1 at the top, we proceed as illustrated in Figure 2. The resulting tree has the same height as the original tree, and is clearly not better balanced. We must try a more clever approach than successive, single rotations.

Figure 1: Rotation via zigs and zags.

Figure 2: When we access node 1 and try to bring it up via pure rotations, the result is a tree that is just as unbalanced as before.

### 2.2 Splay-Step

We now define an operation called SPLAY-STEP. In one splay-step on a node x, x is brought up 2 levels with rotations (or just 1 level if x's parent is the root). When some node x is accessed in the splay tree, we bring x up with a series of splay-steps until it is the root.

We separate the actions performed for the splay-step into the following categories. Call the node that we are trying to access x, its parent y, and y's parent z.

- Case 0: x is the root. Do nothing in this case.
- Case 1: y is the root. If x is the left child of the root, perform a zig on x and y. If not, perform a zag.
- Case 2: x and y are both left children (or both right children). Let us look at the case when both x and y are left children. We first do a zig on the y-z connection. Then, we do a zig on the x-y connection. If x and y are right children, we do the same thing, but with zags instead. (See Figure 3.)
- Case 3: x is a left child and y is a right child, or vice versa. Consider the case where x is a right child, and y is a left child. We first do a zag on the x-y edge, and then a zig on the x-z edge. In the case where x is a left child and y a right child, we do the same thing, but with a zig on the first move, followed by a zag. (See Figure 4.)

Figure 3: Case 2 of the splay-step is when x and y are the same type of children. In this figure, we first do a zig on y-z, and then a zig on x-z.

Figure 4: In Case 3, x and y are not the same type of children. In this case, we do a zag on the x-y edge, and then a zig on the x-z edge.

Note that in the case of the earlier example with the chain of nodes, using splay-step instead of direct rotations results in a much more balanced tree, see Figure 5.

### 2.3 Splay

With the splay-step operation, we can bring the node x to the root of the splay tree with the procedure:

splay(x):
WHILE x≠root:
DO splay-step(x)

The described procedure performs the splay operation in a bottom-up order. It is possible to perform the splay operation in a top down fashion, which would result in the same running time.

Figure 5: When splaying node 1, the resulting tree has half its original height.

# 3 Running-Time Analysis

### 3.1 Potential Function

We define a class of potential functions for the amortized analysis of operations on a splay tree. The potential function depends on weights that we can choose. For each node x in the tree, make the following definitions:

- T(x) is the subtree rooted at x (and it includes teh node x itself),
- weight function: w(x) > 0 is the weight of node x (we can choose what this is; we'll often take w(x) = 1 for all nodes x)
- weight-sum function:  $s(x) = \sum_{y \in T(x)} w(y)$ ,
- rank function:  $r(x) = \log_2 s(x)$ .

Then we define the potential function as:

$$\phi = \sum_{x \in T(root)} r(x).$$

### 3.2 Amortized Cost of Splay(x)

Using the potential function described above, we can show that the amortized cost of the splay operation is  $O(\log n)$ . For the purposes of cost analysis, we assume a rotation takes 1 unit of time.

**Lemma 1** For a splay-step operation on x that transforms the rank function r into r', the amortized cost is  $a_i \leq 3(r'(x) - r(x)) + 1$  if the parent of x is the root, and  $a_i \leq 3(r'(x) - r(x))$  otherwise.

**Proof of Lemma 1:** Let the potential before the splay-step be  $\phi$  and the potential after the splay-step be  $\phi'$ . Let the worst case cost of the operation be  $c_i$ . The amortized cost  $a_i$  is  $a_i = c_i + \phi' - \phi$ . We consider the three cases of splay-step operations.

Case 1: In this case, the parent of x is the root of the tree. Call it y. After the splay-step, x becomes the root and y becomes a child of x. The operation involves exactly one rotation, so  $c_i = 1$ .

The splay step only affects the rank for x and y. Since y was the root of the tree and x is now the root of the tree, r'(x) = r(y). Additionally, since y is now a child of x, (the new) T(x) contains (the new) T(y), so  $r'(y) \le r'(x)$ . Thus the amortized cost is:

$$a_{i} = c_{i} + \phi' - \phi$$

$$= 1 + r'(x) + r'(y) - r(x) - r(y)$$

$$= 1 + r'(y) - r(x)$$

$$\leq 1 + r'(x) - r(x)$$

$$\leq 1 + 3(r'(x) - r(x)),$$

since  $r'(x) \ge r(x)$ .

Case 2: In this case, we perform two zigs or two zags, so  $c_i = 2$ . Let the parent of x be y and the parent of y be z. Node x takes the place of z after the splay-step, so r'(x) = r(z). Also, we see in Figure 3 that  $r(y) \ge r(x)$  (since y was the parent of x) and  $r'(y) \le r'(x)$  (since y is now a child of x). Then the amortized cost is:

$$a_{i} = c_{i} + \phi' - \phi$$

$$= 2 + r'(x) + r'(y) + r'(z) - r(x) - r(y) - r(z)$$

$$= 2 + r'(y) + r'(z) - r(x) - r(y)$$

$$\leq 2 + r'(x) + r'(z) - r(x) - r(x).$$

Next, we use the fact that the log function is concave, or  $\frac{\log a + \log b}{2} \leq \log(\frac{a+b}{2})$ . If the splay-step operation transforms the weight-sum function s into s', we have:

$$\frac{\log_2(s(x)) + \log_2(s'(z))}{2} \le \log_2\left(\frac{s(x) + s'(z)}{2}\right).$$

The left side is equal to  $\frac{r(x)+r'(z)}{2}$ . On the right side, note that

$$s(x) + s'(z) \le s'(x);$$

indeed the old subtree T(x) and the new subtree T'(z) cover all nodes of T'(x), except y (thus s(x) + s'(z) = s'(x) - w(y)). Thus, we have:

$$\frac{r(x) + r'(z)}{2} \le \frac{\log_2(s'(x))}{2} = r'(x) - 1,$$

or

$$r'(z) < 2r'(x) - r(x) - 2.$$

Therefore, the amortized cost is:

$$a_i \le 2 + r'(x) + 2r'(x) - r(x) - 2 - r(x) - r(x)$$
  
=  $3(r'(x) - r(x)).$ 

Case 3: In this case, we perform a zig followed by a zag, or vice versa, so  $c_i = 2$ . Let the parent of x be y and the parent of y be z. Again, r'(x) = r(z) and  $r(y) \ge r(x)$ . Then the amortized cost is:

$$a_i = c_i + \phi' - \phi$$
  
= 2 + r'(x) + r'(y) + r'(z) - r(x) - r(y) - r(z)  
< 2 + r'(y) + r'(z) - r(x) - r(x).

Note in Figure 4 that  $s'(y) + s'(z) \le s'(x)$ . Using the fact that the log function is concave as before, we find that  $r'(y) + r'(z) \le 2r'(x) - 2$ . Then we conclude

$$a_i \le 2 + 2r'(x) - 2 - r(x) - r(x)$$
  
 $\le 2(r'(x) - r(x))$   
 $\le 3(r'(x) - r(x)).$ 

**Lemma 2** The amortized cost of the splay operation on a node x in a splay tree is  $O(1 + \log \frac{s(root)}{s(x)})$ .

**Proof of Lemma 2:** The amortized cost  $a(\operatorname{splay}(x))$  of the splay operation is the sum of all of the splay-step operations performed on x. Suppose that we perform k splay-step operations on x. Let  $r_0(x)$  be the rank of x before the splay operation. Let  $r_i(x)$  be the rank of x after the  $i^{th}$  splay-step operation. Then we have  $r_k(x) = r_0(root)$  and:

$$a(\operatorname{splay}(x)) \leq 3(r_k(x) - r_{k-1}(x)) + 3(r_{k-1}(x) - r_{k-2}(x)) + \dots + 3(r_1(x) - r_0(x)) + 1$$

$$= 3(r_k(x) - r_0(x)) + 1$$

$$= 3(r_0(root) - r_0(x)) + 1.$$

The added 1 comes from the possibility of a case 1 splay-step at the end. The definition of r gives the result.

The above lemma gives the amortized cost of a splay operation, for any settings of the weights. To be able to get good bounds on the total cost of any sequence of operations, we set w(x) = 1 for all nodes x. This implies that  $s(root) \leq n$  where n is the total number of nodes ever in the BST, and by Lemma 2, the amortized cost of any splay operation is  $a(\operatorname{splay}(x)) = O(\log n)$ .

6 - Splay Trees-6

### 3.3 Amortized Cost of BST operations

We now need to show how to implement the various BST operations, and analyze their (amortized) cost (still with the weights set to 1).

#### **3.3.1** Find

Finding an element in the splay tree follows the same behavior as in a BST. After we find our node, we splay it, which is  $O(\log n)$  amortized cost. The cost of going down the tree to find the node can be charged to the cost of splaying it. Thus, the total amortized cost of FIND is  $O(\log n)$ . (Note: if the node is not found, we splay the last node reached.)

#### **3.3.2** FIND-MIN

This operation will only go down the left children, until none are left, and this cost will be charged to the subsequent splay operation. After we find the min node, we splay it, which takes  $O(\log n)$  amortized cost. The total amortized cost is then  $O(\log n)$ .

#### 3.3.3 FIND-MAX

The process for this is the same as for FIND-MIN, except we go down the right child. The total amortized cost of this is  $O(\log n)$  as well.

#### **3.3.4** Join

Given two trees  $T_1$  and  $T_2$  with  $\text{key}(x) < \text{key}(y) \, \forall x \in T_1, y \in T_2$ , we can join  $T_1$  and  $T_2$  into one tree with the following steps:

- 1. FIND-MAX $(T_1)$ . This makes the max element of  $T_1$  the new root of  $T_1$ .
- 2. Make  $T_2$  the right child of this.

The amortized cost of the first step is  $O(\log n)$ . For the second step, the actual cost is 1, but we need to take into account in the amortized cost the increase in the potential function value. Before step 2,  $T_1$  and  $T_2$  had a potential function value of  $\phi(T_1)$  and  $\phi(T_2)$ . After it, the resulting tree has a potential function value  $\leq \phi(T_1) + \phi(T_2) + \log n$ , since the rank of the new root is  $\leq \log(n)$ . So the amortized cost of Join is  $O(\log n)$ .

#### **3.3.5** Split

Given a tree T and a pivot i, the split operation partitions T into two BSTs:

$$T_1: \{x \mid \ker(x) \le i\},\$$

$$T_2: \{x \mid \text{key}(x) > i\}.$$

We split the tree T by performing FIND(i). This FIND will then splay on a node, call it x, which brings it to the root of the tree. We can then cut the tree; everything on the right of x belongs to

 $T_2$ , and everything on the left belongs to  $T_1$ . Depending on its key, we add x to either  $T_1$  or  $T_2$ . Thus, we either make the right child or the left child of x a new root by simply removing its pointer to its parent.

The amortized cost of the FIND operation is  $O(\log n)$ . The actual cost of creating the second BST (by cutting off one of the children) is just O(1), and the potential function does not increase (as the rank of the root does not increase). Thus the total amortized time of a SPLIT is also  $O(\log n)$  time.

Join and Split make insertion and deletion very simple.

#### **3.3.6** Insert

Let i be the value we want to insert. We can first split the tree around i. Then, we let node i be the new root, and make the two subtrees the left and right subtrees of i respectively. The amortized cost again is  $O(\log n)$ .

#### **3.3.7** Delete

To delete a node i from a tree T, we first FIND(i) in the tree, which brings node i to the root. We then delete node i, and are left with its left and right subtrees. Because everything in the left subtree has key less than everything in the right subtree, we can then join them. It is easy to see that this has amortized cost  $O(\log n)$  as well.

#### 3.3.8 Total cost of m operations

The next theorem shows that the cost of any sequence of operations on a splay tree has worst-case time similar to any balanced BST (unless the number of operations m is o(n) where n is the number of keys).

**Theorem 3** For any sequence of m operations on a splay tree containing at most n keys, the total cost is  $O((m+n)\log n)$ .

**Proof of Theorem 3:** Let  $a_i$  be the amortized cost of the  $i^{th}$  operation. Let  $c_i$  be the real cost of the  $i^{th}$  operation. Let  $\phi_0$  be the potential before and  $\phi_m$  be the potential after the m operations. The total amortized cost of m operations is:

$$\sum_{i=1}^{m} a_i = \sum_{i=1}^{m} c_i + \phi_m - \phi_0.$$

Then we have:

$$\sum_{i=1}^{m} c_i = \sum_{i=1}^{m} a_i + \phi_0 - \phi_m.$$

Since we chose w(x) = 1 for all x, we have that, for any node x,  $r(x) \le \log n$ . Thus  $\phi_0 - \phi_m \le n \log n$ , so we conclude:

$$\sum_{i=1}^{m} c_i = \sum_{i=1}^{m} a_i + O(n \log n) = O(m \log n) + O(n \log n) = O((m+n) \log n).$$

# 4 Comparison to other BSTs

### 4.1 Static Optimality Property

We will show that splay trees are competitive against any binary search tree that does not involve any rotations. We consider BSTs containing n keys, and sequences of operations that contain only FIND operations (thus, no INSERT or DELETE for example).

**Theorem 4** Define a static binary search tree to be one that uses no rotation operations. Let  $m_i$  be the number of times element i is accessed for i = 1, ..., n. We assume  $m_i \ge 1$  for all i. Then the total cost for accessing every element i  $m_i$  times is at most a constant times the total cost of any static binary search tree.

**Proof of Theorem 4:** Consider any binary search tree T rooted at t. Let l(i) be the height of of i in T, or the number of nodes on the path from i to the root of T, so l(t) = 1. In T, the cost for accessing an element i is l(i), so the total cost for accessing every element i  $m_i$  times is  $\sum_i l(i)m_i$ . We want to show that the total cost of operations on a splay tree, irrespective of the

starting configuration, is  $O(\sum_{i} l(i)m_i)$ .

We choose a different weight function that earlier. Here, we define the weights to be  $w(i) = 3^{-l(i)}$  for all i. Note that  $s(t) \leq \frac{1}{3} + 2(\frac{1}{3^2}) + 2^2(\frac{1}{3^3}) + \ldots = 1$ . Then, by Lemma 2, the amortized cost of finding i is:

$$a(i) = O(1 + \log_2 \frac{s(t)}{s(i)}) = O(1 + \log_2 \frac{1}{3^{-l(i)}}) = O(1 + l(i)).$$

The total amortized cost of accessing every element  $i m_i$  times on a splay tree is thus:

$$O(m + \sum_{i} l(i)m_i) = O\left(\sum_{i} l(i)m_i\right).$$

This is the amortized cost, we now need to argue about the actual cost. Let  $\phi$  be the potential before the beginning of the sequence, and  $\phi$ ' be the potential after the sequence of operations. For a node i, let r(i) be the rank of i before and r'(i) be the rank after the operations. Note that (since  $r(i) \leq \log_2 1$  and  $r'(i) \geq \log_2 w(i)$ ):

$$\phi - \phi' = \sum_{i} r(i) - r'(i) \le \sum_{i} \log_2 \frac{1}{3^{-l(i)}} = O\left(\sum_{i} l(i)\right).$$

Then we have:

$$\sum c_i = \sum a_i + \phi - \phi' = O\left(\sum_i l(i)m_i\right) + O\left(\sum_i l(i)\right) = O\left(\sum_i l(i)m_i\right),$$

since our assumption  $m_i \ge 1$  implies that  $\sum_i l(i) \le \sum_i l(i)m(i)$ .

### 4.2 Dynamic Optimality Conjecture

The Dynamic Optimality Conjecture claims that Splay Trees are efficient up to a constant factor to any self-adjusting Binary Search Tree (allowing an arbitrary number of (arbitrary) rotations between accesses). This conjecture was first put forth in the Tarjan and Sleater's original Splay Tree paper in 1985, and has withstood attempts to prove or disprove it since.

### 4.3 Scanning Theorem

The scanning theorem states that, for a splay tree that contains the values [1, 2, ..., n], accessing all of those elements in sequential order takes O(n) time, regardless of the initial arrangement of the tree. An interesting point is that, even though the Scanning Theorem has been proved, if the Dynamic Optimality Conjecture were true, then it would follow directly from the fact that one can create dynamic BST's that perform sequential access in linear time.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### Lecture 7 - Dynamic Trees

Lecturer: Michel X. Goemans

#### 1 Overview

In this lecture, we discuss dynamic trees, a sophisticated data structure introduced by Sleator and Tarjan. Dynamic trees allow to provide the fastest worst-case running times for many network flow algorithms. In particular, it will allow us to efficiently perform the Cancel operation in the Cancel and Tighten algorithm. Dynamic trees build upon splay trees, which we introduced in the previous lecture.

Dynamic trees manage a set of node-disjoint (not necessarily binary) **rooted trees**. With each node v is associated a cost. In our use of dynamic trees, the cost will be coming from the edge (p(v), v), where p(v) denotes the parent of v; the cost of the root in that case will be set arbitrarily large (larger than the cost of any other node), say  $+\infty$ .

Figure 1: Example of Dynamic Tree.

Dynamic trees will support the following operations:

- MAKE-TREE(V): Creates a tree with a single node v, whose cost is  $+\infty$ .
- FIND-ROOT(V): Finds and returns the root of the tree containing the node v.
- FIND-COST(V): Returns the cost of node v. (This may sound like a trivial operation, but in fact there is real work to be done, because we will not explicitly maintain the costs of all nodes.)
- FIND-MIN(V): Finds and returns the ancestor of w of v with minimum cost. Ties go to the node closest to the root.
- ADD-COST(V, X): Adds x to the cost of all nodes w on the path from FIND-ROOT(v) to v.
- CUT(V): Breaks the rooted tree in two by removing the link to v from its parent. The node v is now the root of a new tree, and its cost is set to  $+\infty$ .
- LINK(V, W, X): Assumes that (1) w is a root, and (2) v and w are not in the same tree, i.e. FIND-ROOT(v)  $\neq w$ . Combines two trees by adding an edge (v, w), i.e. p(w) = v. Sets the cost of w equal to x.

We will later show that all of these operations run in  $O(\log n)$  amortized time.

Figure 2: CUT(v) operation.

Figure 3: LINK(v, w, x) operation.

**Theorem 1** The total running time of any sequence of m dynamic tree operations is  $O((m + n) \log n)$ , where n is the number of nodes.

We defer the proof of this theorem until the next lecture.

## 2 Implementation of Cancel with dynamic trees

Recall the setting for the Cancel step in the algorithm Cancel and Tighten for the minimum cost flow problem. We have a circulation f and node potentials p in an instance defined on graph G. Recall that an edge (v, w) is admissible if  $c_p(v, w) < 0$ , and the admissible graph  $(V, E_a)$ , is the subgraph of  $E_f$  (the residual graph corresponding to our circulation) containing only the admissible edges. Our aim is to repeatedly find a cycle in the admissible graph and saturate it. Each time we do this, all of the saturated edges disappear from the graph. Also recall that no edges are added to the admissible graph during this process, because any new edge in the residual graph must have positive reduced cost and are therefore is not admissible.

We represent the problem with dynamic trees, where the nodes in the dynamic trees correspond to nodes in G and the edges of the dynamic trees are a subset of the admissible edges. We maintain two (disjoint) sets of admissible edges: those which are currently in the dynamic tree, and those which still need to be considered. The cost of a node v will correspond to the residual capacity  $u_f(p(v), v)$  of the edge (p(v), v), unless v is a root node, in which case it will have  $\cos t + \infty$ . We will also mark some of the roots (denoted graphically with a (\*)) to indicate that we dealt with them and concluded they can't be part of any cycle. For the edges not in the dynamic tree, we also maintain the flow value. (We don't need to maintain the flow explicitly for the edges in the trees, since we can recover the flow from the edge capacities in G and the residual capacity.)

To summarize, we begin with a set of n singleton trees. All of the edges start out in the remaining pool. In each iteration, we try to find an admissible edge leading to the root r of one of the dynamic trees. If we fail to find such an edge, this implies there are no admissible cycles which include r,

and so we mark it and remove it from consideration. Suppose, on the other hand, that we do find an edge (w, r) leading into the root. If w is in a different tree, we join the two trees by adding an edge connecting w and r. On the other hand, if w and r are part of the same tree, it means we have found a cycle. In this case, we push flow along the cycle and remove the saturated edges from the data structure.

In more detail, we keep repeating the following procedure as long as there still exist unmarked roots:

- $\triangleright$  Choose an unmarked root r.
- $\triangleright$  Among admissible edges, try to find one which leads to r.
- $\triangleright$  CASE 1: there is no such  $(v,r) \in E_a$ .
  - $\triangleright$  Mark r, since we know it cannot possibly be part of a cycle.
  - $\triangleright$  Cut all the children v of r.
  - ▷ Set

$$\begin{array}{lcl} f(r,v) & \leftarrow & u(r,v) - u_f(r,v) \\ & = & u(r,v) - \text{FIND-COST}(v) \end{array}$$

- $\rightharpoonup$  CASE 2: there is an admissible edge (w,r) from a different tree, i.e. FIND-ROOT $(w) \neq r$ .
  - $\triangleright$  Link the two trees: LINK(w, r, u(w, r) f(w, r))
- $\triangleright$  CASE 3: there is an admissible edge (w,r) from the same tree, i.e. FIND-ROOT(w)=r.
  - ▶ We've found a cycle, so push flow along the cycle. The amount we can push is

$$\delta = \min(u(w, r) - f(w, r), \text{FIND-COST}(\text{FIND-MIN}(w)))$$

- $\triangleright$  ADD-COST $(w, -\delta)$
- $\triangleright$  Increase f(w,r) by  $\delta$
- $\triangleright$  If f(w,r) = u(w,r), then (u,r) is inadmissible, so we get rid of it.
- $\triangleright$  While FIND-COST(FIND-MIN(w)) = 0:
  - $\triangleright \quad z \leftarrow \text{FIND-MIN}(w)$
  - $\rightharpoonup f(p(z),z) \leftarrow u(p(z),z)$
  - $\triangleright$  CUT(z)

The last while loop is to delete all the edges that became inadmissible along the path from r to w.

#### 2.1 Running time

In a cancel step, we end up cancelling at most O(m) cycles, where m is the number of edges. In addition, each edge gets saturated at most once (if it does, it becomes inadmissible); therefore the number of CUT(z) and FIND-MIN(w) over all cases 3 is O(m). Thus the total number of dynamic tree (and also other arithmetic or control) operations is at most O(m). Hence, by Theorem 1, the running time of each Cancel operation is  $O((m+n)\log n) = O(m\log n)$ . The overall running time of CANCEL-AND-TIGHTEN is therefore  $O(m^2n\log^2 n)$  (strongly polynomial running time bound) or  $O(mn\log n\log(nC))$ .

# 3 Dynamic trees implementation

We now turn to the implementation of dynamic trees. Here we present the definitions; we will cover the running time analysis in the next lecture. The dynamic trees data structure is a collection of rooted trees. We decompose each rooted tree into a set of node-disjoint (directed) paths, as shown in Figure 4. Each node is in precisely one path (possibly containing that node only). We will refer

Figure 4: Decomposition of rooted tree.

to the edges on these paths as **solid edges**, and we will refer to the remaining edges as **dashed edges**, or **middle edges**. Each path is directed from its *tail* (highest in the tree) to its *head* lowest in the tree).

There are many possible ways to partition a tree into solid paths. For instance, if we are given a solid edge and a dashed edge which are both children of a single parent, we can swap the solid and dashed edges. This follows from the basic observation that, for any middle edge (v, w), w is the tail of a solid path. This operation is known as **splicing** as shown in Figure 5.

Figure 5: Splicing in the rooted tree.

In a dynamic tree, each solid path is represented by a splay tree, where the nodes are sorted in increasing order from the *head* to the *tail*, as shown in Figure 6. In other words, the node with smallest key is the head (the lowest in the tree), and the node with largest key is the tail (the highest in the tree)

In addition, we will maintain links between the different splay trees. The root of each splay tree is attached to the parent of the tail of the path in the rooted tree, as shown in Figure 7. For example, the edge (e, f) in the original rooted tree becomes the edge (e, i) linking e to the root i of the splay tree corresponding to the solid path  $f \to i$ . The entire data structure — with the splay trees corresponding to the same rooted tree being connected to each other — forms what is called a *virtual tree*. Any given node of the virtual tree may have at most one left child and at most one right child (of a splay tree), as well as any number of children attached by dashed edges. Children attached by dashed edges are known as **middle children**, and we draw them in between the left and right children.

Notice that we can reconstruct the rooted tree from the virtual tree. Each splay tree corresponds to a solid path from the node of lowest key to the node of highest key. In addition, for any middle

Figure 6: Representation of solid path from head to tail in BST (Splay Tree).

Figure 7: Rooted tree on the left and corresponding virtual tree on the right.

edge, we get an edge of the original rooted tree; for example, to (e, i) in the virtual tree, corresponds the edge (e, f) in the original tree where f is the node with highest key in the splay tree in which i resides.

Note that there are many different ways to represent rooted trees as virtual trees, and we can modify virtual trees in various ways which don't affect the rooted trees.

In particular, we define the Expose(v) operation, which brings a given node v to the root of the virtual tree. This operation involves three main steps:

- 1. Make sure that the path from v to the root only uses *roots* of splay trees. This can be done by performing splay operations whenever we enter a new splay tree.
- 2. Make sure that the path from v to the root consists entirely of solid edges. We can ensure this through repeated splicing.
- 3. Do the splay operation to bring v to the top of the resulting splay tree. This is justified since v is now in the same splay tree as the root of the original rooted tree.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

#### 18.415/6.854 Advanced Algorithms

October 1, 2008

## Lecture 8

Lecturer: Michel X. Goemans

Previously, we introduced the dynamic tree data structure and the operations that dynamic trees must support. Today, we take a more detailed look at dynamic trees and describe the efficient implementation of the operations. In doing so, much of our focus will be on the EXPOSE method, an extended splay operation that is essential in all these operations. We show that any sequence of m operations on a dynamic tree with n nodes takes  $O((m+n)\log n)$  time.

# 1 Dynamic Trees

Dynamic trees (also known as link-cut trees) introduced by Sleator and Tarjan are a data structure intended to maintain a representation of a set of rooted trees. We will be able to perform various operations on these trees, to be discussed later. Figure 1 shows an example tree as a virtual tree (left) and a rooted tree (right).

#### 1.1 Rooted Trees

We view rooted trees as unions of node-disjoint (directed) paths. This divides the edges of the tree into two sets. Solid edges are those that are on the node-disjoint paths that the tree is composed of, and dashed edges are those that are not on these paths. Note that each path consisting of solid edges is a directed path (we omit the arrows here) from top to bottom.

#### 1.2 Virtual Trees

The union of disjoint paths described above can be used to represent virtual trees. In a virtual tree, each solid path is represented by a splay tree such that the following conditions hold:

- A successor node in a splay tree is an ancestor in the rooted tree.
- For each splay tree, its largest node is linked to the parent of the root in the rooted tree.
- In the virtual tree, each node has at most one left child, at most one right child, and any number of middle (virtual) children.

There are three kinds of edges in a virtual tree, corresponding to the three types of children a node can have. Left and right children of a node are connected to the node by solid edges, and middle children of a node are connected to it by dashed edges. Note that there can be many virtual trees corresponding to a rooted tree, because there are two different degrees of freedom involved in constructing a virtual tree — the union of disjoint paths could be different, as could the structure of the splay trees corresponding to the paths.

An important consequence of this setup is that rotations in a splay tree do not affect the structure of the rooted tree.

# 2 The Expose Operation

The Expose(v) operation is an extended splay operation that brings v to the root of the virtual tree without changing the structure of the rooted tree. The important parts of this operation are to

Figure 1: Virtual tree (left) and corresponding rooted tree (right).

make sure that the path from v to the root is solid and that the splay tree representing the path to which v belongs is rooted at v. We can describe this operation in three steps. In our example, we run Expose on node 15.

#### 2.1 Step 1

Step 1 consists of walking from v to the root of the virtual tree. Whenever the walk enters a splay tree (solid edges) at some node w, a SPLAY(w) operation is performed, bringing w to the root of that tree. Middle children are not affected in this step. For instance, we splay nodes 11 and 5 in our example tree as in figure 2. Note that at the end of step 1 of an EXPOSE(v) operation, v will be connected to the root of the virtual tree only by dashed edges.

#### 2.2 Step 2: Splicing

Step 2 consists of walking from v to the root of the virtual tree exchanging along the way each middle edge with the left subtree of the parent. This is illustrated in Figure 3 and called splicing. A middle child of a node w and its left child can be exchanged (without changing the rooted tree) only if w is the root of its splay tree. This justifies our execution of step 1 first since at the end of step 1 all edges from v to the root are middle edges.

Splicing is a valid operation on virtual trees. Indeed, referring to Figure 3, the left subtree of w in the splay tree corresponds to the part of the solid path that is below w in the rooted tree; this is because w is the root of its splay tree. Exchanging that solid subpath with the solid path corresponding to the splay tree rooted at v still leaves the rooted tree decomposed into a node-disjoint union of paths.

Note that after performing this operation on every edge to the root of the virtual tree, there will be a solid path from the root of the rooted tree to the node being exposed.

Figure 2: Walking Up and Splaying. The virtual tree after splaying 15 and 11 is shown on the left. The virtual tree on the right is at the end of step 1, after splaying also node 5.

Figure 3: Splicing. w needs to be the root of its splay tree.

Figure 4: Left virtual tree is after first splicing, the right virtual tree is the one at the end of step 2.

The result of splicing every node on the path to the root for our example is illustrated in Figure 4.

#### 2.3 Step 3

Step 3 consists of walking from v to the root in the virtual tree, splaying v to the root. Note that in the analysis, we can charge the entire cost of step 2 to the final splaying operation in step 3. Figure 5 shows the relevant splay tree before and after this step.

# 3 Operations on Dynamic Trees

We will now describe the desired operations on a dynamic tree and how to implement them efficiently using the EXPOSE method just defined. Some of these operations require keeping track of different costs in the tree, so we first consider an efficient way of doing this.

#### 3.1 Maintaining Cost Information

When performing operations on the dynamic tree, we need to keep track of cost(x) for each node x, and we need to be able to find the minimum cost along paths to the root of the rooted tree. If such a path is the prefix of a path corresponding to a splay tree, it seems that, knowing the minimum cost in any subtree of any our splay trees might be helpful. So, in addition to cost(x), we would like to keep track of the value mincost(x), given by

 $mincost(x) = min\{cost(y) \mid y \text{ in the subtree rooted at } x \text{ of } x\text{'s splay tree}\}.$ 

We'll see that, instead of maintaining cost(x) and mincost(x), that it will be easier to maintain the following two quantities for every node x:

$$\Delta \min(x) = \cot(x) - \min\cot(x)$$

Figure 5: Splaying on Virtual Tree.

Figure 6: Rotation.

and

$$\Delta \cot(x) = \begin{cases} \cot(x) & \text{if } x \text{ is the root of a splay tree,} \\ \cot(x) - \cot(p(x)) & \text{otherwise.} \end{cases}$$

Observe that, if x is the root of a splay tree, then  $cost(x) = \Delta cost(x)$  and  $mincost(x) = \Delta cost(x) - \Delta min(x)$ . This fact, combined with the Expose operation, shows that we can find cost(x) and mincost(x) given  $\Delta min(x)$  and  $\Delta cost(x)$ , so it is sufficient to maintain the latter.

We now claim that we can update  $\Delta \min(x)$  and  $\Delta \cot(x)$  in O(1) time after a rotation or a splice, which will allow us to maintain  $\cot(x)$  and  $\operatorname{mincost}(x)$  in O(1) time.

We first consider a rotation, see Figure 6 for the labelling of the nodes. Let  $\Delta \cot(x)$  and  $\Delta \cot'(x)$  correspond to before and after the rotation, respectively. Similarly define  $\Delta \min(x)$  and  $\Delta \min'(x)$ . Observe that during a rotation, only the nodes b, w and v have their  $\Delta \cot(x)$  change. One can check that the updates are as follows:

$$\begin{array}{lcl} \Delta \cot'(v) & = & \Delta \cot(w) + (\cot(v) - \cot(w)) \\ & = & \Delta \cot(w) + \Delta \cot(v), \\ \Delta \cot'(w) & = & -\Delta \cot(v), \\ \Delta \cot'(b) & = & \Delta \cot(b) + (\cot(v) - \cot(w)) = \Delta \cot(b) + \Delta \cot(v). \end{array}$$

Before showing the corresponding updates for  $\Delta \min(x)$ , observe that  $\Delta \min(x)$  and  $\Delta \cot(x)$ 

satisfy the following equation; here x is any node and l is its left child and r is its right child:

$$\Delta \min(x) = \cos(x) - \min(\cot(x))$$

$$= \cos(x) - \min(\cot(x), \min(\cot(l), \min(\cot(r)))$$

$$= \max(0, \cot(x) - \min(\cot(l), \cot(x) - \min(\cot(r)))$$

$$= \max(0, \Delta \min(l) - \Delta \cot(l), \Delta \min(r) - \Delta \cot(r)). \tag{1}$$

Furthermore, the minimum of the subtree can be located by knowing which term attains the maximum in the last expression.

Back to the updates for  $\Delta \min(x)$ . The only subtrees that change are those of w and v, and so only those  $\Delta \min$  values change. Using (1), one can see that

```
\Delta \min'(w) = \max(0, \Delta \min(b) - \Delta \cot'(b), \Delta \min(c) - \Delta \cot(c))
\Delta \min'(v) = \max(0, \Delta \min(a) - \Delta \cot(a), \Delta \min'(w) - \Delta \cot'(w)).
```

Notice that  $\Delta \min'(v)$  depends on  $\Delta \min'(w)$  that was just computed.

Similar when we perform the splicing step given in Figure 3,  $\Delta$  cost only change for v and u and only  $\Delta \min(w)$  changes. The updates are:

```
\begin{array}{lcl} \Delta \cos t'(v) & = & \Delta(\cos t(v)) - \Delta(\cos t(w)), \\ \Delta \cos t'(u) & = & \Delta \cos t(u) + \Delta \cos t(w), \\ \Delta \min'(w) & = & \max(0, \Delta \min(v) - \Delta \cos t'(v), \Delta \min(z) - \Delta \cos t(z)). \end{array}
```

## 3.2 Implementation of Operations

We now describe the implementation of each of the desired operations on a dynamic tree, making extensive use of the Expose operation.

- MAKE-TREE(v)
  - Simply create a tree with the single node v.
- FIND-ROOT(v)

First, run EXPOSE(v). Then follow right children until a leaf w of the splay tree containing v is reached. Now, SPLAY(w), and then return w.

- FIND-COST(v)
  - First, run Expose(v). Now v is the root, so return  $\Delta \cos(v) = \cos(v)$ . Note that the actual computations here were done by the updates of  $\Delta \cos(v)$  and  $\Delta \min(x)$  within the SPLAY and SPLICE operations.
- FIND-MIN(v)

First, run Expose(v). Now, let's rewrite (1):

```
\Delta \min(v) = \max\{0, -\Delta \operatorname{cost}(\operatorname{left}(v)) + \Delta \min(\operatorname{left}(v)), -\Delta \operatorname{cost}(\operatorname{right}(v)) + \Delta \min(\operatorname{right}(v))\}.
```

If  $\Delta \min(v) = 0$ , then  $\mathrm{SPLAY}(v)$  and then return v, as the minimum is achieved at v. Else, if  $-\Delta \cot(\mathrm{left}(v)) + \Delta \min(\mathrm{left}(v)) > -\Delta \cot(\mathrm{right}(v)) + \Delta \min(\mathrm{right}(v))$ , then the minimum is contained in the left subtree and we walk down it recursively. Otherwise, the minimum is contained in the right subtree, so we recurse down the right. Once we have found the minimum, we splay it.

- ADD-COST(v, x)First, run Expose(v). Add x to  $\Delta \cos(v)$  and subtract x from  $\Delta \cos(\operatorname{left}(v))$ . Also update  $\Delta \min(v)$  (using (1)). (The  $\Delta \min$  value of other nodes is unchanged.)
- CUT(v)First, run Expose(v). Add  $\Delta cost(v)$  to  $\Delta cost(right(v))$ . Remove the edge (v, right(v)).
- LINK(v, w, x)First, run Expose(v) and Expose(w). Then, add the root w as a middle child of v. Add  $\Delta \cot(w) - x$  to  $\Delta \cot(\operatorname{right}(v))$  and to  $\Delta \cot(\operatorname{left}(v))$ . Also update  $\Delta \min(w)$ .

# 4 Analysis of Dynamic Trees

We now give an amortized analysis of cost of operations in these dynamic trees. We will see that any sequence of m dynamic tree operations on n nodes will take  $O((m+n)\log n)$  time.

## 4.1 Potential Function

We will use the following potential function in our analysis, motivated by our analysis of splay trees. For each node x, let w(x) = 1 be the weight assigned to x, and define

$$s(x) = \sum_{y \in T_x} w(y),$$

where  $T_x$  is the entire virtual tree subtree attached at x. Then, consider  $r(x) = \log_2 s(x)$  and take our final potential function to be

$$\phi(T) = 3\sum_{x \in T} r(x).$$

This differs from the potential function for splay trees in 2 ways. First  $T_x$  is defined over the entire virtual tree and secondly we have this additional factor 3. We will see later why the constant factor of 3 was chosen here.

#### 4.2 Runtime of the Expose Operation

We first analyze the runtime of Expose(v), since it is used in all other operations. We look at each step of Expose(v) separately. Let k be the number of middle edges separating v from the root of the entire virtual tree. Equivalently, k is the number of SPLAY operations performed during Step 1.

• Step 1: Let t(v) be the root of the splay tree containing v. Recall that the amortized cost of SPLAY(v) was 3(r(t(v)) - r(v)) + 1 when we used the potential function

$$\phi_{\text{splay}}(T) = \sum_{x \in T} r(x).$$

We now have the potential function  $\phi(T) = 3\phi_{\text{splay}}(T)$ , so the 3(r(t(v)) - r(v)) term here should be multiplied by 3 to obtain an amortized runtime of 9(r(t(v)) - r(v)) + 1 for each call of SPLAY(v) (the +1 corresponds to the cost of the last zig, if any, and so we do not need to multiply it by 3).

We are using the SPLAY operation on the k nodes  $v, p(t(v)), \ldots, (p \circ t)^{k-1}(v)$  in this step, meaning that we get a total amortized runtime of

$$\sum_{i=0}^{k-1} 9 \left[ r(t((p \circ t)^i(v))) - r((p \circ t)^i(v)) \right] + 1 \le 9 [r(\text{root}) - r(v)] + k,$$

since we have that  $r(t(p \circ t)^{i-1}(v)) \le r((p \circ t)^i(v))$ , so the sum telescopes. The amortized cost of step 1 is therefore  $O(\log n) + k$  (since  $r(\text{root}) - r(v) \le \log n$ ).

- Step 2: Splicing does not change the value of  $\phi(T)$ , so the amortized cost for this step is the same as its actual cost of k.
- Step 3: We are using the SPLAY operation once on node v at distance k from the root, so this has an actual cost of k. Using the fact that our potential  $\phi$  has an additional factor 3 in its definition compared to the splay tree version, we get from the amortized analysis of splaying that:

$$k + \frac{1}{3}\Delta\phi(T) \le 3[r(\text{root}) - r(v)] + 1 = O(\log n).$$

Multiplying by 3, we see that we can also account for the additional cost of 2k from steps 1 and 2, and have an amortized time of  $O(\log n)$ .

• Total: We get  $O(\log n) + k$  in step 1, k in step 2, and these 2k plus step 3 gives  $O(\log n)$ , for a total of  $O(\log n)$ .

## 4.3 Runtimes of all Operations

We can now briefly summarize the runtimes of all other operations in terms of EXPOSE.

- FIND-COST, FIND-ROOT, FIND-MIN, ADD-COST
  - Each of these operations requires at most one use of EXPOSE, at most one run of SPLAY, and at most one search of the tree which can be charged to the last splay. Therefore, they each run in  $O(\log n)$  amortized time.
- CUT

We again use EXPOSE once. We now consider the effect of the other actions on the potential function. Removing the edge (v, right(v)) decreases s(v) by s(right(v)) and leaves s(x) unchanged for all other x, so it decreases  $\phi(T)$ , which we can safely ignore. This gives an amortized runtime of  $O(\log n)$ .

• LINK

We use EXPOSE twice. Now, when we link w to v, we see that r(v) increases by  $O(\log n)$ , and all other r(x) remain unchanged. Hence, this operation increases  $\phi(T)$  by  $O(\log n)$ , giving a total amortized runtime of  $O(\log n)$ .

With this analysis, we see that every operation has amortized time  $O(\log n)$ . A sequence of m operations has therefore amortized time  $O(m \log n)$ . Furthermore, the potential function satisfies

$$\phi(T) = \sum_{x \in T} r(x) \le \sum_{x \in T} \log n \le n \log n,$$

meaning that any increase in potential is at most  $O(n \log n)$ , implying that the total cost is at most  $O((m+n) \log n)$ . We now have the following theorem.

**Theorem 1** Any m operations on a dynamic tree with n nodes run in  $O((m+n)\log n)$  time.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# Lecture 9

Lecturer: Michel X. Goemans

# 9 Linear Programming

Linear programming is the class of optimization problems consisting of optimizing the value of a linear objective function, subject to linear equality or inequality constraints. These constraints are of the form

$$a_1x_1 + \dots + a_nx_n \quad \{\leq, =, \geq\} \quad b,$$

where  $a_i, b \in \mathbb{R}$ , and the goal is to maximize or minimize an objective function of the form

$$c_1x_1 + \cdots + c_nx_n$$
.

In addition, we constrain the variables  $x_i$  to be nonnegative.

The problem can be expressed in matrix form. Given these constraints

$$\mathbf{Ax} \quad \{ \leq, =, \geq \} \quad \mathbf{b}$$

$$\mathbf{x} \qquad > \qquad 0$$

maximize or minimize the value of

$$\mathbf{c}^T \mathbf{x}$$
,

where  $\mathbf{x} \in \mathbb{R}^n$ ,  $\mathbf{A} \in \mathbb{R}^{m \times n}$ ,  $\mathbf{b} \in \mathbb{R}^m$ ,  $\mathbf{c} \in \mathbb{R}^n$ .

Linear programming has many applications and can also be used as a proof technique. In addition, it is important from a complexity point-of-view, since it is among the hardest of the class of polynomial-time solvable problems.

# 9.1 Algorithms

Research in linear programming algorithms has been an active area for over 60 years. In this class, we will discuss three major (classes of) algorithms:

- Simplex method (Dantzig 1947).
  - Fast in practice.
  - Still the most-used LP algorithm today.
  - Can be nonpolynomial (exponential) in the worst case.
- Ellipsoid algorithm (Shor, Khachian 1979).
  - Polynomial time; this was the first polynomial-time algorithm for linear programming.
  - Can solve LP (and other more general) problems where the feasible region  $P = \{x : Ax = b, x \ge 0\}$  is not explicitly given, but instead, given a vector x, one can efficiently decide whether  $x \in P$  or if not, find an inequality satisfied by P but not by x.
  - Very useful for designing polynomial time algorithms for other problems.
  - Not fast in practice.

- Interior-point algorithms (Karmarkar 1984).
  - This is a class of algorithms which maintain a feasible point in the interior of P; many variants (by many researchers) have been developed.
  - Polynomial time.
  - Fast in practice.
  - Can beat the simplex method for larger problems.

# 9.2 Equivalent forms

A linear programming problem can be modified to fit a preferred alternate form by changing the objective function and/or the linear constraints. For example, one can easily transform any linear program into the standard form:  $\min\{c^Tx: Ax=b, x\geq 0\}$ . One can use the following simple transformations.

$$\begin{array}{lll} \text{Maximize to minimize} & \max\{\mathbf{c}^T\mathbf{x}\} & \longrightarrow & \min\{-\mathbf{c}^T\mathbf{x}\} \\ \text{Equality to inequality} & \mathbf{a}_i^T\mathbf{x} = b_i & \longrightarrow & \begin{cases} \mathbf{a}_i^T\mathbf{x} \leq b_i \\ \mathbf{a}_i^T\mathbf{x} \leq b_i \end{cases} \\ \text{Inequality to nonnegativity constraint} & \mathbf{a}_i^T\mathbf{x} \leq b_i & \longrightarrow & \begin{cases} \mathbf{a}_i^T\mathbf{x} \leq b_i \\ \mathbf{a}_i^T\mathbf{x} + s = b_i \\ s \geq 0 \end{cases} & (s \in \mathbb{R}^n) \end{cases}$$
 Variables unrestricted in sign 
$$x_j \text{ unrestricted in sign} & \longrightarrow & \begin{cases} replace \ x_j \text{ everywhere by } x_j^+ - x_j^- \\ x_j^+ \geq 0 \\ x_j^- \geq 0 \end{cases}$$

## 9.3 Definitions

Here is some basic terminology for a linear program.

**Definition 1** A vector x is feasible for an LP if it satisfies all the constraints.

**Definition 2** An LP is feasible if there exists a feasible solution x for it.

**Definition 3** An LP is infeasible if there is no feasible solution x for it.

**Definition 4** An  $LP \min \{ \mathbf{c}^T \mathbf{x} : \mathbf{A} \mathbf{x} = \mathbf{b}, \mathbf{x} \geq 0 \}$  is unbounded if, for all  $\lambda \in \mathbb{R}$ ,  $\exists \mathbf{x} \in \mathbb{R}^n$  such that

$$\mathbf{A}\mathbf{x} = \mathbf{b}$$
$$\mathbf{x} \ge 0$$
$$\mathbf{c}^T \mathbf{x} \le \lambda.$$

## 9.4 Farkas' lemma

If we have a system of equations  $\mathbf{A}\mathbf{x} = \mathbf{b}$ , from linear algebra, we know that either  $\mathbf{A}\mathbf{x} = \mathbf{b}$  is solvable, or the system  $\mathbf{A}^T\mathbf{y} = 0$ ,  $\mathbf{b}^Ty \neq 0$  is solvable. Indeed, since  $Im(\mathbf{A}) = ker(\mathbf{A}^T)^{\perp}$ , either  $\mathbf{b}$  is orthogonal to  $ker(\mathbf{A}^T)$  (in which case it is in the image of  $\mathbf{A}$ , i.e.  $\mathbf{A}\mathbf{x} = \mathbf{b}$  is solvable) or it is not orthogonal to it in which case one can find a vector  $\mathbf{y} \in \ker(\mathbf{A}^T)$  with a non-zero inner product with  $\mathbf{b}$  (i.e.  $\mathbf{A}^T\mathbf{y} = 0$ ,  $\mathbf{b}^Ty \neq 0$  is solvable).

Farkas' lemma generalizes this when we have also linear inequalities:

Lemma 1 ((Farkas' lemma)) Exactly one of the following holds:

1. 
$$\exists \mathbf{x} \in \mathbb{R}^n : \mathbf{A}\mathbf{x} = \mathbf{b}, \mathbf{x} > 0$$
.

2. 
$$\exists \mathbf{y} \in \mathbb{R}^m : \mathbf{A}^T \mathbf{y} \ge 0, \mathbf{b}^T \mathbf{y} < 0.$$

Clearly, both cannot simultaneously happen, since the existence of such an  ${\bf x}$  and a such a  ${\bf y}$  would mean:

$$\mathbf{y}^T \mathbf{A} \mathbf{x} = \mathbf{y}^T (\mathbf{A} \mathbf{x}) = y^T \mathbf{b} < 0,$$

while

$$\mathbf{y}^T \mathbf{A} \mathbf{x} = (\mathbf{A}^T \mathbf{y})^T \mathbf{x} \ge 0,$$

as the inner product of two nonnegative vectors is nonnegative. Together this gives a contradiction.

## 9.4.1 Generalizing Farkas' Lemma

Before we provide a proof of the (other part of) Farkas' lemma, we would like to briefly mention other possible generalizations of the solvability of system of equations.

First of all, consider the case in which we would like the variables  $\mathbf{x}$  to take integer values, but don't care whether they are nonnegative or not. In this case, the natural condition indeed is necessary and sufficient. Formally, suppose we take this set of constraints:

$$\mathbf{Ax} = \mathbf{b}$$
$$\mathbf{x} \in \mathbb{Z}^n$$

Then if  $\mathbf{y}^T \mathbf{A} \mathbf{x} = \mathbf{y}^T \mathbf{b}$ , and we can find some  $\mathbf{y}^T \mathbf{A} \in \mathbb{Z}^n$  and some  $\mathbf{y}^T \mathbf{b}$  that is not integral, then the system of constraints is infeasible. The converse is also true.

**Theorem 2** Exactly one of the following holds:

1.  $\exists \mathbf{x} \in \mathbb{Z}^n : \mathbf{A}\mathbf{x} = \mathbf{b}$ .

2.  $\exists \mathbf{y} \in \mathbb{R}^m : \mathbf{A}^T \mathbf{y} \in \mathbb{Z}^n \text{ and } \mathbf{b}^T \mathbf{y} \notin \mathbb{Z}$ .

One could try to combine both nonnegativity constraints and integral restrictions but in that case, the necessary condition for feasibility is not sufficient. In fact, for the following set of constraints:

$$\mathbf{Ax} = \mathbf{b}$$

$$\mathbf{x} \geq 0$$

$$\mathbf{x} \in \mathbb{Z}^n,$$

determining feasibility is an NP-hard problem, and therefore we cannot expect a *good characteriza-*tion (a necessary and sufficient condition that can be checked efficiently).

### 9.4.2 Proof of Farkas' lemma

We first examine the projection theorem, which will be used in proving Farkas' lemma (see Figure 1).

**Theorem 3 (The projection theorem)** If K is a nonempty, closed, convex set in  $\mathbb{R}^m$  and  $\mathbf{b} \notin K$ , define

$$\mathbf{p} = \operatorname{proj}_{K}(\mathbf{b}) = \arg\min_{\mathbf{z} \in K} \|\mathbf{z} - b\|_{2}. \tag{1}$$

Then, for all  $\mathbf{z} \in K : (\mathbf{z} - \mathbf{p})^T (\mathbf{b} - \mathbf{p}) \le 0$ .

Figure 1: The projection theorem.

**Proof of Lemma 1:** We have seen that both systems cannot be simultaneously solvable.

So, now assume that  $\nexists \mathbf{x} : \mathbf{A}\mathbf{x} = \mathbf{b}, \mathbf{x} \ge 0$  and we would like to show the existence of  $\mathbf{y}$  satisfying the required conditions. Define

$$K = {\mathbf{A}\mathbf{x} : \mathbf{x} \in \mathbb{R}^n, \mathbf{x} \ge 0} \subseteq \mathbb{R}^m.$$

By assumption,  $\mathbf{b} \notin K$ , and we can apply the projection theorem. Define  $\mathbf{p} = \operatorname{proj}_K(\mathbf{b})$ . Since  $\mathbf{p} \in K$ , we have that  $\mathbf{p} = \mathbf{A}\mathbf{x}$  for some vector  $\mathbf{x} \geq 0$ . Let  $\mathbf{y} = \mathbf{p} - \mathbf{b} \in \mathbb{R}^m$ . We claim that  $\mathbf{y}$  satisfies the right conditions.

Indeed, consider any point  $\mathbf{z} \in K$ . We know that  $\exists \mathbf{w} \geq 0 : \mathbf{z} = \mathbf{A}\mathbf{w}$ . By the projection theorem, we have that  $(\mathbf{A}\mathbf{w} - \mathbf{A}\mathbf{x})^T \mathbf{y} \geq 0$ , i.e.

$$(\mathbf{w} - \mathbf{x})^T \mathbf{A}^T \mathbf{y} \ge 0, \tag{2}$$

for all  $\mathbf{w} \geq 0$ . Choosing  $\mathbf{w} = \mathbf{x} + e_i$  (where  $e_i$  is the *i*th unit vector), we see that  $\mathbf{A}^T \mathbf{y} \geq 0$ . We still need to show that  $\mathbf{b}^T \mathbf{y} < 0$ . Observe that  $\mathbf{b}^T \mathbf{y} = (\mathbf{p} - \mathbf{y})^T \mathbf{y} = \mathbf{p}^T \mathbf{y} - \mathbf{y}^T \mathbf{y} < 0$  because  $\mathbf{p}^T \mathbf{y} \leq 0$  and  $\mathbf{y}^T \mathbf{y} > 0$ . The latter follows from  $y \neq 0$  and the former from (2) with  $\mathbf{w} = 0$ :  $-\mathbf{x}^T \mathbf{A}^T \mathbf{y} \geq 0$ , i.e.  $-\mathbf{p}^T \mathbf{y} \geq 0$ .

#### 9.4.3 Corollary to Farkas' lemma

Farkas' lemma can also be written in other equivalent forms.

**Corollary 4** Exactly one of the following holds:

1.  $\exists \mathbf{x} \in \mathbb{R}^n : \mathbf{A}\mathbf{x} \leq \mathbf{b}$ ,

2. 
$$\exists \mathbf{y} \in \mathbb{R}^m : \mathbf{y} \ge 0, \mathbf{A}^T y = 0, \mathbf{b}^T y < 0.$$

Again,  $\mathbf{x}$  and  $\mathbf{y}$  cannot simultaneously exist. This corollary can be either obtained by massaging Farkas' lemma (to put the system of inequalities in the right form), or directly from the projection theorem.

## 9.5 Duality

Duality is one of the key concepts in linear programming. Given a solution  $\mathbf{x}$  to an LP of value z, how do we decide whether or not  $\mathbf{x}$  is in fact an optimum solution? In other words, how can we calculate a lower bound on  $\min \mathbf{c}^T \mathbf{x}$  given that  $\mathbf{A}\mathbf{x} = \mathbf{b}, \mathbf{x} \geq 0$ ?

Suppose we have  $\mathbf{y}$  such that  $\mathbf{A}^T\mathbf{y} \leq \mathbf{c}$ . Then observe that  $\mathbf{y}^T\mathbf{b} = \mathbf{y}^T\mathbf{A}\mathbf{x} \leq \mathbf{c}^T\mathbf{x}$  for any feasible solution  $\mathbf{x}$ . Thus  $\mathbf{y}^T\mathbf{b}$  provides a lower bound on the value of our linear program. This conclusion is true for all  $\mathbf{y}$  satisfying  $\mathbf{A}^T\mathbf{y} \leq \mathbf{c}$ , so in order to find the best lower bound, we wish to maximize  $\mathbf{y}^T\mathbf{b}$  under the constraint of  $\mathbf{A}^T\mathbf{y} \leq \mathbf{c}$ .

We can see that this is in fact itself another LP. This new LP is called the dual linear program of the original problem, which is called the primal LP.

- Primal LP:  $\min \mathbf{c}^T \mathbf{x}$ , given  $\mathbf{A}\mathbf{x} = \mathbf{b}, \mathbf{x} \geq 0$ ,
- Dual LP:  $\max \mathbf{b}^T \mathbf{y}$ , given  $\mathbf{A}^T \mathbf{y} \leq \mathbf{c}$ .

### 9.5.1 Weak Duality

The argument we have just given shows what is known as weak duality.

**Theorem 5** If the primal P is a minimization linear program with optimum value  $\mathbf{z}$ , then it has a dual D, which is a maximization problem with optimum value  $\mathbf{w}$  and  $\mathbf{z} \geq \mathbf{w}$ .

Notice that this is true even if either the primal or the dual is infeasible or unbounded, provided we use the following convention:

```
infeasible min. problem \longrightarrow value = +\infty unbounded min. problem \longrightarrow value = -\infty infeasible max. problem \longrightarrow value = -\infty unbounded max. problem \longrightarrow value = +\infty
```

## 9.5.2 Strong Duality

What is remarkable is that one even has strong duality, namely both linear programs have the same values provided at least one of them is feasible (it can happen that both the primal and the dual are infeasible).

**Theorem 6** If P or D is feasible, then  $\mathbf{z} = \mathbf{w}$ .

**Proof:** We assume that P is feasible (the argument if D is feasible is analogous; or one could also argue that the dual of the dual is the primal and therefore one can exchange the roles of primal and dual).

If P is unbounded,  $\mathbf{z} = -\infty$ , and by weak duality,  $\mathbf{w} \leq \mathbf{z}$ . So it must be that  $\mathbf{w} = -\infty$  and thus  $\mathbf{z} = \mathbf{w}$ .

Otherwise (if P is not unbounded), let  $\mathbf{x}^*$  be the optimum solution to P, i.e.:

$$\mathbf{z} = \mathbf{c}^T \mathbf{x}^*$$

$$\mathbf{A} \mathbf{x}^* = \mathbf{b}$$

$$\mathbf{x}^* \geq 0$$

We would like to find a dual feasible solution with the same value as (or no worse than)  $\mathbf{x}^*$ . That is, we are looking for a  $\mathbf{y}$  satisfying:

$$\mathbf{A}^T \mathbf{y} \leq \mathbf{c}$$
 $\mathbf{b}^T \mathbf{y} \geq \mathbf{z}$ 

If no such  $\mathbf{y}$  exists, we can use Farkas' lemma to derive:  $\exists \mathbf{x} \in \mathbb{R}^n, \mathbf{x} \geq 0$ , and  $\exists \lambda \in \mathbb{R}, \lambda \geq 0$ :  $\mathbf{A}\mathbf{x} - \lambda \mathbf{b} = 0$  and  $\mathbf{c}^T \mathbf{x} - \lambda \mathbf{z} < 0$ .

We now consider two cases.

• If  $\lambda \neq 0$ , we can scale by  $\lambda$ , and therefore assume that  $\lambda = 1$ . Then we get that

$$\exists \mathbf{x} \in \mathbb{R}^n : \left\{ \begin{array}{l} \mathbf{A}\mathbf{x} = \mathbf{b}, \\ \mathbf{x} \geq 0 \\ \mathbf{c}^T \mathbf{x} < \mathbf{z}. \end{array} \right.$$

This result is a contradiction, because  $\mathbf{x}^*$  was the optimum solution, and therefore we should not be able to further minimize  $\mathbf{z}$ .

• If  $\lambda = 0$  then

$$\exists \mathbf{x} \in \mathbb{R}^m : \left\{ \begin{array}{l} \mathbf{x} \geq 0 \\ \mathbf{A}\mathbf{x} = 0 \\ \mathbf{c}^T \mathbf{x} < 0. \end{array} \right.$$

Consider now  $\mathbf{x}^* + \mu \mathbf{x}$  for any  $\mu > 0$ . We have that

$$\mathbf{x}^* + \mu \mathbf{x} \ge 0$$
  
 $\mathbf{A}(\mathbf{x}^* + \mu \mathbf{x}) = \mathbf{A}\mathbf{x}^* + \mu \mathbf{A}\mathbf{x} = \mathbf{b} + 0 = \mathbf{b}.$ 

Thus,  $\mathbf{x}^* + \mu \mathbf{x}$  is feasible for any  $\mu \geq 0$ . But, we have that

$$\mathbf{c}^T(\mathbf{x}^* + \mu \mathbf{x}) = \mathbf{c}^T \mathbf{x}^* + \mu \mathbf{c}^T \mathbf{x} < z,$$

a contradiction.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### Lecture 10

Lecturer: Michel X. Goemans

Last lecture we introduced the basic formulation of a linear programming problem, namely the problem with the objective of minimizing the expression  $c^Tx$  (where  $c \in \mathbb{R}^n, x \in \mathbb{R}^n$ ) subject to the constraints Ax = b where  $A \in \mathbb{R}^{mxn}, b \in \mathbb{R}^m$ ) and  $x \geq 0$ . We then introduced the dual linear program, with the objective of maximizing  $b^Ty$ , subject to the constraints that  $A^Ty \leq c$ . Eventually, we were able to relate the two forms via the Theorem of Strong Duality, which states that if either the primal or the dual has a feasible solution then their values are equal:

$$w := \min\{c^T x : Ax = b, x \ge 0\} = \max\{b^T y : A^T y \le c\} =: z.$$

Today, we further explore duality by justifying the Theorem of Strong Duality via a physical argument, introducing rules for constructing dual problems for non-standard linear programming formulations, and further discussing the notion of complementary slackness mentioned in the last lecture. We then shift gears and discuss the geometry of linear programming, which leads us to the Simplex Method of solving linear programs.

## 1 The Dual

#### 1.1 Physical Justification of the Dual

Consider the standard dual form of a linear program. The set of feasible solutions y that satisfy the constraints  $A^Ty \leq c$  form a polyhedron in  $\mathbb{R}^n$ ; this is the intersection of m halfspaces. Consider a tiny ball within this polyhedron at position y. To maximize  $b^Ty$ , we move the ball as far as possible in the direction of b within the confines of our polyhedron. This is analogous to having a force, say gravity, acting on the ball in the b direction.

We now switch over entirely to the physical analogy. At equilibrium, the ball ends up at a point y maximizing  $b^Ty$  over  $A^Ty \leq c$ , and the gravity force b is in equilibrium with the forces exerted against the ball by the 'walls' of our polyhedron. These wall forces are normal to the hyperplanes defining them, so for the hyperplane defined by  $a_j^Ty \leq c$  (where  $a_j$  is the jth column of A), the force exerted on the ball can be expressed as  $-x_ja_j$  for some magnitude multiplier  $x_j \geq 0$ . As stated previously, our ball is at equilibrium (there is no net force on it), and so we find

$$b - \sum_{j} x_j a_j = 0.$$

We also note that for any wall which our ball is not touching, there is no force exerted by that wall on the ball. This is equivalent to saying

$$x_j = 0 \text{ if } a_j^T y < c_j.$$

We now argue that these multipliers  $x_j$  form an optimum solution to the primal linear program. We first note that

$$b - \sum_{j} x_j a_j = 0$$

is equivalent to Ax = b, and that the multipliers  $x_j$  are either zero or positive, and thus  $x \ge 0$ . This shows that our  $x_j$ 's yield a feasible solution to the primal, now we need to prove that the  $x_j$ 's

Figure 1: Physical visualization of the dual with n = 2 (two dimensions), m = 6 (six hyperplanes), and b as gravity. The dual is maximized when our  $b^T y$  ball is at the lowest point of the polyhedron.

minimize the primal. For this, we will show that the value  $c^T x$  equals  $b^T y$ , and therefore by weak duality, this will mean that x is a minimizer for the primal. The value  $c^T x$  is:

$$c^T x = \sum_j c_j x_j = \sum_j (a_j^T y) x_j,$$

since  $x_j$  is non-zero only where  $a_j^T y = c_j$  (a non-zero force is only exerted by a wall on our ball if the ball is touching that wall), and thus

$$c^T x = \sum_{j} (a_j^T y) x_j = y^T (\sum_{j} a_j x_j) = y^T b = b^T y.$$

#### 1.2 Rules for Writing a Dual

So far, we have dealt only with the dual of the standard primal linear programming problem, minimizing  $c^Tx$  such that Ax = b and  $x \ge 0$ . What if we are confronted with a non-standard linear program, such as a program that involves inequalities on the  $a_{ij}x_j$ , or non-positivity constraints on the  $x_j$ ? We have two options. The first is to massage the linear program into the standard primal form, immediately convert to the standard dual, and then potentially massage the dual problem into a form more suitable to our original problem. This can be a long, frustrating process, however, and so instead we present a set of standard rules for converting any linear program into its dual form.

Consider a linear problem with the objective of minimizing  $\sum_j c_j x_j$  subject to the following constraints:

$$\sum_{j} a_{ij} x_{j} \begin{cases} = b_{i} & i \in I_{=} \\ \geq b_{i} & i \in I_{\geq} \\ \leq b_{i} & i \in I_{\leq} \end{cases}$$
 (1)

$$x_{j} \begin{cases} \geq 0 & j \in J_{+} \\ \leq 0 & j \in J_{-} \\ \in \mathbb{R} & j \in J_{0}. \end{cases}$$
 (2)

Earlier, the way we obtained the dual was to get a lower bound (or an upper bound if it was a maximization problem) on the objective function of the primal, and to maximize this upper bound. We claim that the same process leads to the dual of maximizing  $\sum_i b_i y_i$  subject to the constraints:

$$\sum_{i} a_{ij} y_{i} \begin{cases} \leq c_{j} & j \in J_{+} \\ \geq c_{j} & j \in J_{-} \\ = c_{j} & j \in J_{0} \end{cases}$$

$$(3)$$

$$y_i \begin{cases} \geq 0 & i \in I_{\geq} \\ \leq 0 & i \in I_{\leq} \\ \in \mathbb{R} & i \in I_{=} \end{cases}$$
 (4)

Weak duality is pretty straightforward. Constraints (4) on  $y_i$  guarantee that, when multiplying constraint (1) by  $y_i$  and summing them over i, we get

$$\sum_{i} y_i \sum_{j} a_{ij} x_j \ge \sum_{i} y_i b_i. \tag{5}$$

Similarly, constraints (3) together with constraints (2) imply that

$$\sum_{j} c_j x_j \ge \sum_{i} x_j \sum_{i} a_{ij} y_i. \tag{6}$$

The left-hand-side of (5) being equal to the right-hand-side of (6) (after rearranging the summation), we get weak duality that

$$c^T x > b^T y$$
.

And strong duality also holds provided that either the primal or the dual has a feasible solution.

#### 1.3 Complementary Slackness

Complementary slackness allows to easily check when a feasible primal and dual solutions are simultaneously optimal. Consider the primal

$$\min\{c^T x : Ax = b, x > 0\}.$$

Consider an alternative definition of the dual LP obtained by adding slack variables:

$$\max\{b^T y : A^T y + Is = c, s \ge 0\},\$$

where  $s \in \mathbb{R}^n$ . Given a feasible primal solution x and a feasible dual solution (y, s), we see that the difference in their value is

$$c^T x - b^T y = s^T x + y^T A x - y^T b = s^T x,$$

and this quantity better be 0 if x is optimum for the primal and (y, s) is optimal for the dual. Notice that  $x \geq 0$  and  $s \geq 0$ , and therefore  $x^T s = 0$  if and only if  $x_j s_j = 0$  for all j. Thus, for the 2 solutions to be simultaneously optimum in the primal and in the dual, we need that, for all j,  $x_j = 0$  whenever  $s_j > 0$  (or equivalently that  $s_j = 0$  whenever  $x_j > 0$ ).

Summarizing, we have:

**Theorem 1** Let  $x^*$  be feasible in the primal, and  $(y^*, s^*)$  be feasible in the dual. Then the following are equivalent.

- 1.  $x^*$  is optimal in the primal, and  $(y^*, s^*)$  is optimal in the dual,
- 2. For all  $j: x_i^* > 0 \implies s_i^* = 0$ ,

3. For all  $j: x_i^* s_i^* = 0$ ,

4. 
$$\sum_{j} x_{j}^{*} s_{j}^{*} = 0.$$

For a general pair of primal-dual linear programs as given in (1)-(2) and (3)-(4), complementary slackness says that, for x to be optimal in the primal and for y to be optimal in the dual, we must have that

- 1.  $y_i = 0$  whenever  $\sum_i a_{ij} x_i \neq b_i$  and,
- 2.  $x_i = 0$  whenever  $\sum_i a_{ij} y_i \neq c_i$ .

# 2 The Geometry of Linear Programming

We now switch gears and discuss the geometry of linear programming. First, we define a polyhedral set  $P = \{x \in \mathbb{R}^n : Ax \leq b\}$  as the finite intersection of halfspaces. We then define a vertex of polyhedral set P to be any  $x \in P$  such that  $x + y \in P \land x - y \in P \implies y = 0$ . Intuitively, a vertex is a "corner" of a polyhedral set. We can state this geometric definition also algebraically. Given an index set  $J \subseteq \{1, 2, \dots, n\}$ ,  $A_J$  denotes the  $m \times |J|$  submatrix of A consisting of all columns of A indexed by J.

**Lemma 2** For  $P = \{x : Ax = b, x \ge 0\}$  and  $x \in P$ , x is a vertex of P if and only if  $A_J$  has linearly independent column for  $J = \{j : x_j > 0\}$ .

**Proof:** For both directions, we prove the contrapositive.

 $\Leftarrow$ : Assuming x is not a vertex implies that  $\exists y \neq 0: x+y, x-y \in P$ . Therefore A(x+y)=b, A(x-y)=b, which implies that Ay=0. However, because membership in P requires points to be non-negative, we have that if  $x_j=0$  then  $y_j=0$ . Thus, if we let  $w=y_J$  (i.e. w corresponds to the components of y in J), we see that  $w\neq 0$  and  $A_Jw=0$ , which implies that  $A_J$  has linearly dependent columns.

 $\Rightarrow$ : If  $A_J$  has linearly dependent columns, then  $\exists w \neq 0: A_J w = 0$ . This implies you can construct a y via zero padding such that  $y \neq 0$  and  $Ay = 0, y_j = 0$  for  $j \notin J$ . Thus,  $A(x + \epsilon y) = A(x - \epsilon y) = b$  for any  $\epsilon \in \mathbb{R}$ . We also note that  $x_j \pm \epsilon y_j \geq 0$  if  $\epsilon \leq \frac{x_j}{|y_j|}$ , which is strictly greater than 0. Therefore,

if we choose 
$$\epsilon = \min_{j: y_j \neq 0} \frac{x_j}{|y_j|}$$
, we have that  $x \pm \epsilon y \in P$ , and thus  $x$  is a not a vertex of  $P$ .

We can take the notions in this lemma a step further by introducing the notions of a basis, a basic solution, and a basic feasible solution. For what follows, we assume that rank(A) = m (if that's not the case, then either there is no solution to Ax = b and our problem is infeasible, or there exists a redundant constraint (possibly more than one) in Ax = b which can be removed).

**Definition 1** For a polyhedral set  $P = \{x : Ax = b, x \ge 0\}$ , a basis B is a subset of  $\{1...n\}$  such that |B| = m and  $A_B$  is invertible (i.e.  $rank(A_B) = m$ ).

**Definition 2** x is a basic solution of P if  $\exists$  basis  $B: x_B = A_B^{-1}b, x_N = 0$  for  $N = \{1...n\} \setminus B$ .

Note that by this definition,  $A_B x_B + A_N x_N = b$  must be true, but x could be negative and therefore infeasible.

**Definition 3** x is a basic feasible solution (bfs) if it is a basic solution such that  $x \geq 0$ .

We are now ready to prove the following theorem relating vertices to basic feasible solutions.

**Theorem 3** Given a polyhedral set  $P = \{x : Ax = b, x \ge 0\}$  such that rank(A) = m, and a point  $x \in P$ , x is a vertex of P if and only if it is a basic feasible solution of P.

**Proof:** Will be provided in Lecture 11.

There are several notable remarks to make pertaining to this theorem:

• The vertex to basic feasible solution relationship is one-to-many, or in other words, there may be multiple basic feasible solutions that correspond to a single vertex.

• The number of vertices of P is less than or equal to the number of bases of P. This follows from the first remark, and the fact that some bases may be infeasible. Therefore, the number of vertices of P is upper bounded by  $\binom{n}{m}$ . However, a stricter upper bound has been shown using a more detailed analysis, namely the number of vertices of P is upper bounded approximately by  $\binom{n-\frac{m}{2}}{\frac{m}{2}}$ .

We now know that finding basic feasible solutions of P is equivalent to finding vertices of P. Why is this important? Because there must an optimum solution to our linear programming problem that is a vertex of the polyhedral set defined by the linear constraints. More formally,

**Theorem 4** Given a polyhedral set  $P = \{x : Ax = b, x \geq 0\}$ , if  $\min\{c^Tx : x \in P\}$  is finite (the program is feasible and bounded), and  $x \in P$ , then  $\exists$  vertex x' of  $P : c^Tx' \leq c^Tx$ .

**Proof:** Will be provided in Lecture 11.

This theorem directly leads us to the insight behind the Simplex Method for solving linear programs by finding the best vertex.

## 3 Sketch of the Simplex Method

Here is a very basic sketch of how the simplex method works.

- 1. Choose a basic feasible solution x corresponding to the basis B.
- 2. While x is not an optimal solution, choose j and k such that the new basis  $B' = B \setminus \{j\} \cup \{k\}$  forms a bfs x' with  $c^T x < c^T x$ .

There are several important remarks to make about this method:

- It is not clear that j and k will always exist. But they do, and this can be shown.
- As defined, x and x' will either be equal or will be 'adjacent' vertices on P.
- The reason it is called a 'method' and not an algorithm is because we haven't specified yet how to choose j and k if several choices exist. The choice of j and k is referred to as a pivoting rule; many pivoting rules have been proposed.
- As such, there is no guarantee that  $c^Tx' < c^Tx$ , namely we could have  $c^Tx' = c^Tx$ ; in fact we could even have x' = x since we could switch from one basis to another representing the same vertex. There is therefore the risk that we repeat the same basis and the algorithm never terminates. And this can happen for some of the pivoting rules. There exist however anticycling pivoting rules which guarantee that the same basis is never repeated. With such a rule, the simplex method will terminate since there are finitely many bases.
- The running time of the simplex method depends on the number of bases considered before finding an optimal one.

• For all currently known pivoting rules, there is at least one instance that will cause the simplex method to run in exponential time. (This is in contrast with the simplex method in practice for which the number of iterations is usually good. A partial explanation of this sharp contrast between the worst-case behavior and a typical behavior is highlighted in the work of Spielman and Teng on smoothed analysis.)

We will cover other algorithms that will guarantee a polynomial running time in the worst-case; they will however not proceed from vertex to vertex of the polyhedral set.

There is a lower bound on the number of iterations of the Simplex Method, which is the number of edges in the path from the starting vertex of P to the optimum vertex of P. For a given P, this lower bound will be the diameter of P, the maximum over all pairs of vertices of the length of the shortest path between them. In 1957, Hirsch conjectured that the diameter of a polyhedral set is upper bounded by n-d, where d is the dimension of the space, and n is the number of hyperplanes defining P. While this has not been proven true in the general case, the following results have been found:

- The conjecture is not true in the unbounded case, namely there exist unbounded polyhedra with diameter  $n d + \lfloor \frac{d}{5} \rfloor$ .
- No polynomial bound on the diameter is known for the general case (even for just bounded polyhedra).
- Kalai and Kleitman derived a subexponential bound  $n^{O(\log d)}$  on the diameter.
- If the Hirsch Conjecture can be proven for n=2d, then the conjecture holds for all n.
- The Hirsch Conjecture is true for polytopes with all their vertces in  $\{0,1\}^d$ .

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### 18.415/6.854 Advanced Algorithms

October 15, 2008

Lecture 11

Lecturer: Michel X. Goemans

In this lecture, we will start continuing from where we left in the last lecture on linear programming. We then argue that  $LP \in NP \cap co - NP$ . In the end of this lecture, we introduce the first polynomial algorithm to solve LP, known as the *Ellipsoid Algorithm*.

## 1 LP continuation

Last time, we had proved that, given a polyhedral set  $P = \{x : Ax = b, x \geq 0\}$ , a point x is a vertex of P if and only if  $A_{\{j: x_j > 0\}}$  has linearly independent columns. Now assume that rank(A) = m, where m is the number of rows. We had then defined the notion of a basic feasible solution (bfs) corresponding to a basis B, see last lecture for details.

**Theorem 1** Consider the polyhedral set  $P = \{x : Ax = b, x \geq 0\}$  where rank(A) = m. A point x is a vertex of P if and only if it is a basic feasible solution.

**Proof:** If x is a vertex of P, then we know that  $A_{\{j:x_j>0\}}$  has linearly independent columns. Let  $J == \{j: x_j > 0\}$ . Thus  $rank(A_J) = |J|$ . Since rank(A) = m, we can add columns to J to get a set B with |B| = m and  $rank(A_B) = m$ , i.e.  $A_B$  is invertible. We must have that:

$$x_B = A_B^{-1}b$$
$$x_N = 0.$$

Therefore, x is a basic feasible solution.

Conversely, assume x is a basic feasible solution, that is,

$$x_B = A_B^{-1}b$$
$$x_N = 0.$$

By definition,  $J = \{j : x_j > 0\} \subseteq B$  and the fact that  $rank(A_B) = |B|$  implies that  $A_J$  has linearly independent columns. Thus, x is a vertex of P.

**Theorem 2** Let  $P = \{x : Ax = b, x \ge 0\}$ . Assume  $min\{c^Tx : x \in P\}$  is finite. Then, for any  $x \in P$ , there exists a vertex  $x' \in P$  such that  $c^Tx' \le c^Tx$ 

**Proof:** If x is a vertex, we are done. Otherwise, there exists  $y \neq 0$  such that  $x \pm y$  is in P. Note that, as Ay = 0 (because A(x + y) = b = Ax), for any  $\alpha \in \mathbb{R}$ ,  $A(x + \alpha y) = b$ . Observe that,

$$(x + \alpha y)_j \ge 0$$
 for  $\alpha \le \frac{x_j}{-y_j}$ , if  $y_j < 0$  always, if  $y_j \ge 0$ 

We may assume that  $c^T y \leq 0$  (otherwise choose -y). Moreover, if  $c^T y = 0$ , we can assume that there exists j such that  $y_j < 0$ .

Assume, by contradiction, that for all  $j, y_j \ge 0$ . Then,  $c^T y < 0$ . But this implies that

$$c^T(x + \alpha y) \to -\infty \text{ as } \alpha \to \infty$$

Then  $\min\{c^Tx:x\in P\}$  is not finite. Contradiction!

Therefore, there exists j such that  $y_i < 0$ . Choose

$$\alpha = \min_{j: \ y_j < 0} \frac{x_j}{-y_j}.\tag{1}$$

This implies that  $x + \alpha y$  is in P, and  $c^T(x + \alpha y) \leq c^T x$ . Moreover, one more component of x is 0. We can apply the same procedure to  $x' = x + \alpha y$ , and eventually we are going to get to a vertex. (Formally, we could apply induction on the number of nonzero entries of x).

## 2 Size of LP

In order to be able to discuss the complexity for solving a linear program, we need first to discuss the size of the input. We assume that every integer data is given in binary encoding, thus for  $n \in \mathbb{Z}$ , we need

$$size(n) = 1 + \lceil \log_2(|n| + 1) \rceil$$

bits, for  $v \in \mathbb{Z}^p$ , we need

$$size(v) = \sum_{i=1}^{p} (v_i)$$

bits, and for  $A \in \mathbb{Z}^{nxm}$ , we need

$$size(A) = \sum_{i=1}^{n} \sum_{j=1}^{m} (a_{i,j}).$$

bits. As a result, to represent all the data of a linear program, we need a size equal to

$$size(LP) = size(b) + size(c) + size(A).$$

The above size is not very convenient when proving the complexity of a linear program-ming algorithm. Instead, we will be considering another size, defined by

$$L = m + n + \log_2(det_{max}) + \log_2(b_{max}) + \log_2(c_{max}),$$

where  $\det_{max} = \max |\det(A')|$  over all submatrices A' of A,  $b_{max} = \max_i |b_i|$  and  $c_{max} = \max_i |c_i|$ .

In the following two lemmas, we show that L is polynomially comparable with size(LP), which implies that an algorithm has a running time polynomially bounded in terms of L if, and only if, it is polynomial in size(LP).

**Lemma 3** If  $A' \in \mathbb{Z}^{n \times n}$  then  $|det(A')| \leq 2^{size(A')-n^2} - 1$ .

**Proof:** Recall that for  $A' = [a_1, a_2, ..., a_k]$ ,  $|\det(A')|$  can be visualized as the volume of the parallelipiped spanned by the column vectors. Hence,

$$1 + |det(A')| \le 1 + \prod_{i=1}^{n} ||a_i|| \le \prod_{i=1}^{n} (1 + ||a_i||) \le \prod_{i=1}^{n} 2^{size(a_i) - n} = 2^{size(A') - n^2}.$$

**Lemma 4**  $L \leq \text{size}(LP) \leq mnL$ .

**Proof:** Using the fact that  $size(n) \leq 2 + \log_2(n)$  for  $n \geq 1$ , we have that the second inequality holds because:

$$size(A) \le mn \max_{i,j} (size(a_{ij})) \le mn(2 + \log_2(\det_{\max})),$$
  
 $size(b) \le m(2 + \log_2(b_{\max})),$ 

and

$$size(c) \le n(2 + \log_2(c_{\max})).$$

Adding these together gives the desired inequality for  $m \geq 2$ ,  $n \geq 2$ . The first  $\leq$  holds because, by the previous lemma, the determinant of any minor of A is bounded by the size of A. Hence,

$$det_{\text{max}} \leq 2^{\text{size(A)}}$$

Also,

$$m + \log b_{\text{max}} \le \text{size(b)},$$

and

$$n + \log c_{\text{max}} < \text{size(c)}.$$

Finally,

$$2^L = 2^m 2^n \det_{\max} c_{\max} b_{\max} \le 2^{\text{size(LP)}}$$

From the definition of L, the following remark follows; this is what we will need mostly when analyzing running times or sizes.

Remark 1  $det_{max} * b_{max} * c_{max} * 2^{m+n} = 2^L$ .

# 3 Complexity of LP

Here is the decision problem corresponding to linear programming.

Given  $A \in \mathbb{Z}^{m \times n}$ ,  $b \in \mathbb{Z}^m$ ,  $c \in \mathbb{Z}^n$ , and  $\lambda$ , determine whether

$$\min\{c^T x : Ax = b, x \ge 0\} \le \lambda. \tag{2}$$

To show that LP is in NP, we need to be able to provide a concise (i.e. polynomially bounded in the size of the input) certificate for yes instances. A feasible point of cost less or equal to  $\lambda$  will clearly be a certificate, but will it be concise?

### Claim 5 $LP \in NP$

We now show that if we take not just any feasible solution, but a basic feasible solution, then its size will be polynomially bounded in the size of the input.

**Theorem 6** Let x be a vertex (or basic feasible solution) of  $Ax = b, x \ge 0$ . Then  $x_i = \frac{p_i}{q}$ . for i=1,...,n where  $p_i, q \in \mathbb{N}$  and  $p_i < 2^L$  and  $q < 2^L$ .

**Proof:** Since x is a vertex, then x is a basic feasible solution with basis B such that  $x_B = A_B^{-1}b$  and  $x_N = 0$  (notice that  $A_B$  is square). By Cramer's rule:

$$x_B = A_B^{-1}b = \frac{1}{\det(A_B)}cof(A_B)b,$$

where cof(A) is a matrix whose entries are all determinants of submatrices of A. Letting  $q = \det(A_B)$ , we get that  $q \leq \det_{\max} < 2^L$  and  $p_i \leq m \det_{\max} b_{\max} < 2^L$ .

Now, to prove Claim 5, for yes instances, the certificate will be a vertex of  $\{x : Ax = b, x \geq 0\}$  such that  $c^T x \leq \lambda$ .

However, to be precise, we also have to deal with the case in which the LP is unbounded, since in that case, there might not be any such vertex. But in that case, we can give a certificate of unboundedness by (i) exhibiting a vertex of  $\{x: Ax = b, x \geq 0\}$  (showing it is not empty, and it is concise by the above theorem) and (ii) showing that the dual feasible region  $\{y: A^Ty \leq c\}$  is empty by using Farkas' lemma and exhibiting a vertex of  $Ax = b, x \geq 0, c^Tx = -1$  which is also concise by the above theorem.

Alternatively, one can show a concise feasible solution to

$$\min\{c^T x : Ax = b, x \ge 0, c^T x \le \lambda - 1\}.$$
(3)

#### Claim 7 $LP \in co - NP$ .

Indeed, for the complement instances of LP, we can use strong duality and exhibit a basic feasible solution of  $A^Ty \leq c$  s.t.  $b^Ty > \lambda$  (or show that  $\{x \geq 0 : Ax = b\}$  is empty using Farkas' lemma). In the case when  $\{x : Ax = b, x \geq 0\}$  is feasible, the correctness follows from strong duality saying that

$$\min\{c^T x : Ax = b, x \ge 0\} = \max\{b^T y : A^T y \le c\}.$$

Thus,  $LP \in NP \cap co - NP$  which makes it likely to be in P. And indeed, LP was shown to be polynomially solvable through the ellipsoid algorithm.

Figure 1: One iteration of the ellipsoid algorithm.

## 4 The Ellipsoid Algorithm

The Ellipsoid algorithm was proposed by the Russian mathematician Shor in 1977 for general convex optimization problems, and applied to linear programming by Khachyan in 1979. The problem being considered by the ellipsoid algorithm is:

Given a bounded, convex, non-empty and full-dimensional set  $P \in \mathbb{R}^n$  find  $x \in P$ .

We will see that we can reduce linear programming to an instance of this problem.

The ellipsoid algorithm works as follows. We start with a big ellipsoid E that is guaranteed to contain P. We then check if the center of the ellipsoid is in P. If it is, we are done, we found a point in P. Otherwise, we find an hyperplane passing through the center of the ellipsoid, so that P is contained in one of the half spaces defined by it. One iteration of the ellipsoid algorithm is illustrated in Figure 1. The ellipsoid algorithm is the following.

- Let  $E_0$  be an ellipsoid containing P
- while center  $a_k$  of  $E_k$  is not in P do:
  - Let  $c_k^T x \leq c_k^T a_k$  be such that  $\{x : c_k^T x \leq c_k^T a_k\} \supseteq P$
  - Let  $E_{k+1}$  be the minimum volume ellipsoid containing  $E_k \cap \{x: c_k^T x \leq c_k^T a_k\}$
  - $-k \leftarrow k+1$

The ellipsoid algorithm has the important property that the ellipsoids constructed shrink by, at least, a constant (depending on the dimension) factor in volume as the algorithm proceeds; this is stated precisely in the next lemma. As P is full dimensional, we will eventually find a point in P.

Lemma 8 
$$\frac{Vol(E_{k+1})}{Vol(E_k)} < e^{-\frac{1}{2n+2}}$$
.

Note that the ratio is independent of k.

Before we can state the algorithm more precisely, we need to define ellipsoids.

**Definition 1** Given a center a, and a positive definite matrix A, the ellipsoid E(a,A) is defined as  $\{x \in \mathbb{R}^n : (x-a)^T A^{-1}(x-a) \leq 1\}$ .

One important fact about a positive definite matrix A is that there exists B such that  $A = B^T B$ , and hence  $A^{-1} = B^{-1} (B^{-1})^T$ . Ellipsoids are in fact just affine transformations of unit balls. To see this, consider the (bijective) affine transformation  $T: x \to y = (B^{-1})^T (x-a)$ . It maps  $E(a,A) \to \{y: y^T y \le 1\} = E(0,I)$ , the unit ball.

This gives a motivation for the fact that the ratio  $\frac{Vol(E_{k+1})}{Vol(E_k)}$  is independent of k. Indeed, as linear transformations preserve ratio of volumes, we can reduce to the case when  $E_k$  is the unit ball. In this case, by symmetry of the ball, the volume ratio will be independent of k.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# Lecture 12 - Ellipsoid algorithm

Lecturer: Michel X. Goemans

In this lecture we describe the ellipsoid algorithm and show how it can be applied to the linear programming problem.

## 1 Ellipsoid algorithm

### 1.1 Definitions

An *ellipsoid* is denoted by

$$E(a, A) = \{ x \in \mathbb{R}^n : (x - a)^T A^{-1} (x - a) \le 1 \},$$

with center  $a \in \mathbb{R}^n$  and  $A \in \mathbb{R}^{n \times m}$  that is positive definite.

Recall that A is symmetric if  $A = A^T$ . A matrix is positive definite if it is symmetric and  $\forall x \neq 0$ , we have  $x^T Ax > 0$ . The inverse of a positive definite matrix is also positive definite. Symmetric matrices have only real eigenvalues, and positive definite matrices have only real positive eigenvalues.

#### 1.2 Problem statement

Given  $P \subseteq \mathbb{R}^n$  bounded, closed, *convex*, find  $x \in P$  or show that  $P = \emptyset$ .

### 1.2.1 Assumption: Separation oracle

The first issue is how the convex set P is given. We assume that we have a "separation oracle" for P which does the following. Given a, the oracle either

- 1. affirms that  $a \in P$ , or
- 2. outputs  $c \in \mathbb{R}^n$  such that  $P \subseteq \{x \in \mathbb{R}^n : c^T x < c^T a\}$ .

Think of c as the normal vector of the plane separating a and P, pointing away from P. Such a hyperplane exists because P is convex and closed.

An algorithm for our problem would be judged based on how many times it queries the oracle. We would like the number of queries to be polynomial in terms of the input data.

#### 1.2.2 Assumption: Outer ball and minimum volume

As such, the problem is hopeless, since we do not know where to search for a point  $x \in P$ , and P may even contain just a single point x. So we make two further assumptions. They are

- $P \subseteq$  "big ball", i.e.  $P \subseteq B(0,R)$ , a ball with center 0 and radius R > 0. This tell us where out search can be confined.
- If  $P \neq \emptyset$ , P has "sufficient" volume. Let's say we are given r > 0 such that we are guaranteed that P contains some ball of radius r if P is non-empty.

We consider the size of our input to be  $n + \log R - \log r$ .

### 1.3 Sketch of the algorithm

Here is an outline of the ellipsoid algorithm:

- Start with ellipsoid  $E_0 = (a_0, A_0)$ .
- Maintain an ellipsoid  $E_k = (a_k, A_k) \supseteq P$ . At iteration k, ask the oracle if  $a_k$  belongs to P.
  - If answer is yes, then we are done.
  - If  $a_k$  does not belong to P, then the oracle provides a  $c_k$  such that  $P \subseteq \{x \in \mathbb{R}^n : c^T x < c_k^T a_k\}$ . Thus, the separating hyperplane slices  $E_k$  and P is on one side of this hyperplane. We then determine a smaller ellipsoid  $E_{k+1}$  such that

$$E_{k+1} \supseteq E_k \cap \{x : c_k^T x < c_k^T a_k\}. \tag{1}$$

- (Refer to Fig. (1)).
- Notice that  $E_k \supseteq P$  and we iterate on. If we can show that volume of  $E_{k+1}$  decays exponentially, then in "few" iterations, we either find a point in P, or reach  $Vol(E_{k+1}) < Vol(B(0,r))$  and conclude that  $P = \emptyset$ .

Figure 1: Diagram illustrating a single iteration of the ellipsoid algorithm.

### 1.4 Bounding volume of ellipsoids

**Proposition 1** Given  $E_k = E(a_k, A_k)$  and  $c_k$ , we can find  $E_{k+1}$  such that Eq. (1) is satisfied and

$$\frac{Vol(E_{k+1})}{Vol(E_k)} < \exp\left(-\frac{1}{2(n+1)}\right).$$

Let us first focus on the simple case in which our ellipsoid is the unit ball centered at the origin.

**Claim 2** Proposition 1 holds for the special case where  $E_k = E(0, I)$  and  $c_k = -e_1$ .

12 - Ellipsoid algorithm-2

**Proof:** By symmetry,  $E_{k+1}$  is an axis-aligned ellipsoid with center along the  $x_1$  axis. It has to contain all points with  $x_1 = 0$ . See Fig. (2). Formally, we want  $E_{k+1} \supseteq E_k \cap \{x : x_1 \ge 0\}$ , and one can show that it is enough to guarantee that (i)  $e_1 \in E_{k+1}$  and (ii) for all x with ||x|| = 1 and  $x_1 = 0$ , we have  $x \in E_{k+1}$ .

Figure 2: Diagram illustrating the case where  $E_k = E(0, I)$ .

We propose the following

$$E_{k+1} = \left\{ x : \left( \frac{n+1}{n} \right)^2 \left( x_1 - \frac{1}{n+1} \right)^2 + \frac{n^2 - 1}{n^2} \sum_{i=2}^n x_i^2 \le 1 \right\}$$
$$= E\left( \frac{1}{n+1} e_1, \frac{n^2}{n^2 - 1} \left( I - \frac{2}{n+1} e_1 e_1^T \right) \right).$$

It is easy to verify that this ellipsoid satisfies the constraints above. Since the volume of an ellipsoid is proportional to the product of its axis lengths, we obtain:

$$\frac{\text{Vol}(E_{k+1})}{\text{Vol}(E_k)} = \frac{n}{n+1} \cdot \left(\frac{n^2}{n^2 - 1}\right)^{\frac{n-1}{2}} 
< \exp\left(-\frac{1}{n+1}\right) \exp\left(\frac{1}{n^2 - 1}\frac{n-1}{2}\right) 
= \exp\left(-\frac{1}{2(n+1)}\right),$$

where we have used the fact that  $1 + x < e^x$  whenever  $x \neq 0$  (for x = 0 we have equality). Next, we do a slightly more general case.

Claim 3 Proposition 1 holds when  $E_k = E(0, I)$ ,  $c_k = d$  and ||d|| = 1.

**Proof:** From the previous simple case, it is clear that the following  $E_{k+1}$  works.

$$E_{k+1} = E\left(-\frac{1}{n+1}d, \frac{n^2}{n^2-1}\left(I - \frac{2}{n+1}dd^T\right)\right).$$

12 - Ellipsoid algorithm-3

### **Proof of Proposition 1:**

In general, we can transform  $E(a_k, A_k)$  to E(0, I) and map  $c_k$  into some d. We can then find an ellipsoid E' as in the proof of Claims 2 and 3, and map it back to obtain  $E_{k+1}$ . Denote the linear transformation that maps  $E(a_k, A_k)$  into E(0, I) as T. Here is a picture:

$$E_k \quad \stackrel{T}{\to} \quad E(0,1)$$

$$E_{k+1} \quad \stackrel{T^{-1}}{\leftarrow} \quad E'$$

Recall that we have

$$E(a, A) = \{x : (x - a)^T A^{-1} (x - a) < 1\}.$$

By Cholesky decomposition (since A is positive definite), we can write  $A = B^T B$  for some matrix B. If we let  $y = (B^{-1})^T (x - 1)$ , then we have

$$(x-a)^T B^{-1} (B^{-1})^T (x-a) \le 1$$
  
 $(\Leftrightarrow) \quad y^T y \le 1,$ 

so we have a unit ball in the y space. Thus, our linear transformation T and its inverse are:

$$T(x) = y = (B^{-1})^T (x - a_k),$$
  
 $T^{-1}(y) = a_k + B^T y.$ 

We need an equivalent "half-space" constraint after applying T. From Eq. (1),

$$c_k^T x < c_k^T a_k$$
$$c_k^T (B^T y + a_k) < c_k^T a_k$$
$$c_k^T B^T y < 0.$$

Hence, in the new space, the unit normal vector of the separating plane is

$$d = \frac{Bc_k}{\sqrt{c_k^T B^T B c_k}}.$$

From Claim 3, we can find an ellipsoid E' in the y space. For convenience (and aesthetic pleasure), let  $b = B^T d$ .

Apply  $T^{-1}$  to E' to obtain

$$E_{k+1} = E(a_{k+1}, A_{k+1})$$

$$a_{k+1} = a_k - \frac{1}{n+1}B^T d = a_k - \frac{1}{n+1}b$$

$$A_{k+1} = B^T \left(\frac{n^2}{n^2 - 1} \left(I - \frac{2}{n+1}dd^T\right)\right)B = \frac{n^2}{n^2 - 1} \left(A_k - \frac{2}{n+1}bb^T\right).$$

Since affine transformations preserve the ratios between volumes, we immediately have the desired bound. Here are the details.

$$Vol(E(0,I)) = det((B^{-1})^T)Vol(E_k)$$
$$Vol(E_{k+1}) = det(B^T)Vol(E').$$

Rearranging, we have

$$\frac{Vol(E_{k+1})}{Vol(E_k)} = \frac{Vol(E')}{Vol(E(0,I))} < \exp\left(-\frac{1}{2(n+1)}\right).$$

## 1.5 Running time

From Proposition 1, we know that  $Vol(E_k) < Vol(E_0) \exp\left(-\frac{k}{2(n+1)}\right)$ . If P is nonempty, then the ellipsoid algorithm terminates in

# iterations = 
$$O\left(n\log\frac{\operatorname{Vol}(E_0)}{\operatorname{Vol}(P)}\right)$$
.

By our assumption on P containing a ball of radius r if non-empty, we have that  $\frac{\operatorname{Vol}(E_0)}{\operatorname{Vol}(P)} \leq \left(\frac{R}{r}\right)^n$ , and thus the number of iterations is

# iterations = 
$$O(n^2(\log R - \log r))$$
.

If P is empty, by the same number of iterations, we are guaranteed of its emptyness.

We conclude this section by noting a small subtlety. To compute d, we have to be able to find B such that  $A = B^T B$ . Cholesky decomposition takes  $O(n^3)$  and guarantees that numbers in B have size polynomially bounded by the size of numbers in A. But we have to take square roots (in the calculation of d), so we might have to deal with irrational numbers. As a result, we may have to do some rounding to make  $E_{k+1}$  slightly bigger. We have to argue that the volume decrease factor is still reasonable, say  $\exp\left(-\frac{1}{3(n+1)}\right)$ , but this detail shall be omitted.

# 2 Applying ellipsoid algorithm to linear programming

## 2.1 Linear programming problem

In the linear programming problem, we are asked to find

$$\min\{c^T x : Ax = b, x > 0\}$$

with inputs A, b, c. The size of the input, from last lecture, is

$$L = m + n + \log \det_{\max} + \log b_{\max} + \log c_{\max}$$
.

To apply the ellipsoid algorithm, we will need to

- 1. Go from an optimization problem to a feasibility problem.
- 2. Show that the initial convex set is *bounded* and argue about how big the bounding ellipsoid has to be. Argue about termination and provide an inner ball if P is nonempty. i.e. we want P to be *full-dimensional*.

#### 2.2 Optimization to feasibility

We will convert the optimization problem to a feasibility problem as follows:

- 1. Check feasibility of  $Ax = b, x \ge 0$ .
- 2. If answer is infeasible, we are done because LP is infeasible.
- 3. Otherwise, check feasibility of dual. Dual is  $\max\{b^Ty:A^Ty\leq c\}$ . Check for feasibility of  $A^Ty\leq c$ .
  - If dual is not feasible, we are done because LP is unbounded.
  - Otherwise, both primal and dual are feasible. Their solutions have to match by strong duality. Hence, we check for feasibility of  $Ax = b, x \ge 0, A^Ty \le c, c^Tx = b^Ty$  to find a solution for both primal and dual.

#### 2.3 Outer and inner cubes

Here we describe how to go from a system of linear inequalities to an equivalent one (in terms of feasibility) which if non-empty is full-diemnsional and has enough volume.

**Proposition 4** Let  $P := \{x : Ax \leq b\}$  and e be the vector of all ones. Assume that A has full column rank  $n^1$ . Then P is nonempty iff  $P' = \{x : Ax \leq b + \frac{1}{2^L}e, -2^L \leq x_j \leq 2^L \text{ for all } j\}$  is nonempty.

This proposition allows us to choose  $E_0$  to be a ball centered at the origin containing the cube  $[-2^L, 2^L]^n$ . Also, if there exists a  $\hat{x}$  such that  $A\hat{x} \leq b$  then

$$A\left(\hat{x}\pm\frac{1}{2^{2L}}\right)\leq b+\left(\frac{1}{2^{2L}}na_{\max}\right)e\leq\frac{1}{2^{L}}e\quad\text{ where }a_{\max}\text{ is max entry of }A.$$

That gives us a little cube around  $\hat{x}$ . The time for finding an x in P' is thus  $O(n \cdot nL)$ , because the ratio of the volumes of  $\left[-2^L, 2^L\right]^n$  to  $\left[-\frac{1}{2^{2L}}, \frac{1}{2^{2L}}\right]^n$  is  $8^{Ln}$ . Recall that finding x in P takes  $O(n\log\frac{Vol(E_0)}{Vol(P)})$  iterations. That means LP takes polynomial time in L.

**Proof of Proposition 4:** We first prove the forward direction. Suppose  $P \neq \emptyset$ . Our only worry is whether there is any element in P inside the big box. This has been done in previous lecture. We consider a vertex x in P (this exists because A has full column rank). This implies that x is defined by  $A_S x = b_S$ , where  $A_S$  is a submatrix of A. Using Cramer's rule, we can write x as

$$x = \left(\frac{p_1}{q}, \frac{p_2}{q}, \cdots, \frac{p_n}{q}\right)$$

with  $|p_i| < 2^L$  and  $1 \le q < 2^L$ .

We now work on the converse.  $\{x: Ax \leq b\} = \emptyset$  implies, by Farkas' Lemma, there exists a y such that  $y \geq 0$ ,  $A^Ty = 0$ , and  $b^Ty = -1$ . We can choose a vertex of  $A^Ty = 0$ ,  $b^Ty = -1$ ,  $y \geq 0$ . Rewrite this as

$$\left(\begin{array}{c}A^T\\b^T\end{array}\right)y=\left(\begin{array}{c}0\\-1\end{array}\right),y\geq0.$$

By Cramer's rule, we can bound the components of a basic feasible solution y as:

$$y^T = \left(\frac{r_1}{s}, \cdots, \frac{r_m}{s}\right),$$

with  $0 \leq s, r_i \leq \det_{\max} \left( \begin{array}{c} A^T \\ b^T \end{array} \right)$ . Expanding the determinant along the last row, we see that  $\det_{\max} \left( \begin{array}{c} A^T \\ b^T \end{array} \right) \leq m b_{\max} \det_{\max}(A)$ . Using the fact that  $2^L > 2^m 2^n \det_{\max}(A) b_{\max}$ , we obtain  $0 \leq s, r_i < \frac{m}{2m2^n} 2^L \leq \frac{m}{2^{m+1}} 2^L$ .

$$\left(b + \frac{1}{2^L}e\right)^T y = \underbrace{b^T y}_{1} + \frac{1}{2^L}e^T y = -1 + \frac{m^2}{2^{m+1}} < 0.$$

(The last inequality holds for  $m \ge 1$ .) By Farkas' Lemma again, this y shows that there is no x satisfying  $Ax \le b + \frac{1}{2^L}e$ , i.e. P' is empty.

<sup>&</sup>lt;sup>1</sup>Small detour: We have previously dealt with the constraint problem  $Ax = b, x \ge 0$ . If this is non-empty, then we have a vertex in the feasible solution. However, there is *not* guaranteed if the constraints are of the form  $Ax \le b$ . But if we have  $\operatorname{rank}(A) = n, A \in \mathbb{R}^{m \times n}$ , then a non-empty P will always contain a vertex. In our case, since we convert from the problem with constraints  $x \ge 0$ , we would have inequalities  $-Ix \le 0$  and full column rank.

## 2.4 Obtaining a solution

There is one last problem. If the ellipsoid method returns a x in P', x might not be in P.

One solution is to round the coefficients of the inequalities to rational numbers and "repair" these inequalities to make x fit in P. This is called simultaneous Diophantine approximations, and will not be discussed.

We can solve this problem by another method. We give a general method for finding a feasible solution of a linear program, assuming that we have a procedure that checks whether or not the linear program is feasible, e.g. ellipsoid algorithm.

Assume, we want to find a solution of  $Ax \leq b$ . The inequalities in this linear program can be written as  $a_i^T x \leq b_i$  for  $i = 1, \dots, m$ . We use the following algorithm:

- 1.  $I \leftarrow \emptyset$ .
- 2. For  $i \leftarrow 1$  to m do
  - If the set of solutions of

$$\left\{ \begin{array}{ll} a_j^T x \leq b_j & \forall j = i+1, \cdots, m \\ a_j^T x = b_j & \forall j \in I \cup \{i\} \end{array} \right\}$$

is nonempty, then  $I \leftarrow I \cup \{i\}$ .

3. Finally, solve x in  $a_i^T x = b_i$  for  $i \in I$  with Gaussian elimination.

We assume that the solution is a vertex and satisfies some equalities. If at step 2, making inequality i an equality makes the problem infeasible, then the vertex cannot depend on this inequality and we can discard it.

---

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

#### 18.415/6.854 Advanced Algorithms

October 22, 2008

## Lecture 13

Lecturer: Michel X. Goemans

In the last lecture, we discussed the details of the ellipsoid algorithm and described how to apply the ellipsoid algorithm to a linear program. In this lecture, we will see two applications of the ellipsoid method: linear programming without an explicit linear program, and semidefinite programming.

## 1 Undirected s-t Shortest Path Problem

We are given an undirected graph G=(V,E) with  $s,t\in V$  and cost function  $c:E\to\mathbb{R}$ . We assume that there is no negative cost cycle in G. In the s-t shortest path problem, we find a simple s-t path P minimizing

$$c(P) = \sum_{e \in P} c_e$$

We will apply the ellipsoid method using the following steps:

- 1. Modify the shortest path problem to be a minimum cost perfect matching problem.
- 2. Apply the ellipsoid algorithm to the minimum cost perfect matching problem.

### 1.1 Minimum Cost Perfect Matching Problem

We introduce the following definitions.

**Definition 1** A matching M on a graph H is a set of edges with no common endpoint.

**Definition 2** Matching M is perfect iff  $|M| = \frac{|V|}{2}$ .

The original graph G = (V, E) is transformed into an auxiliary graph  $H = (V', E \cup F)$ . We would like the s - t shortest path problem in G to be equivalent to the minimum cost perfect matching problem in H. The transformation is as follows. For each  $v \in V$ , one of the following cases holds.

- 1.  $v \notin \{s,t\}$  and deg(v) even (where deg(v) is the degree of vertex v),
- 2.  $v \in \{s,t\}$  and deg(v) odd,
- 3.  $v \notin \{s,t\}$  and deg(v) odd,
- 4.  $v \in \{s,t\}$  and deg(v) even.
- For cases 1 and 2, graph H contains deg(v) vertices corresponding to  $v \in G$ . Edges are added so that these vertices are fully connected (they form a clique). The added edges are in F, and  $c_e = 0 \ \forall e \in F$ .
- For cases 3 and 4, graph H contains deg(v) + 1 vertices corresponding to  $v \in G$ . Edges are added so that these vertices form a clique; they are fully connected. The added edges are in F, and  $c_e = 0 \ \forall e \in F$ .

So far, H contains a set of disjoint cliques, one for each vertex  $v \in V$ . To each original edge  $e = (u, v) \in E$ , we create a corresponding edge between one of the copies of u and one of the copies of v. This is done in such a way that these edges in H (which we will denote by E as they correspond to the original edges) form a matching. In other words, for every vertex v, the deg(v) edges in G incident to v become now incident to distinct copies of v in H. These |E| additional edges keep the cost they have in G.

Now we will show that the minimum cost perfect matching problem on H is equivalent to the shortest s-t path problem on G, whenever G does not have any negative cost cycle. First consider the case where we have a simple path P from s to t in G of cost c(P). In H, these edges in P form a (not perfect) matching. We add edges of F to P to make a perfect matching: we show that  $\exists N \subseteq F$  such that  $M = P \cup N$ . Indeed, by construction, the edges of P cover in H all but an even number of vertices corresponding to  $v \in V$  (and thus these remaining vertices can be matched with edges of F of 0 cost), and this is true for any vertex  $v \in V$ :

- 1. For case 1, P uses 0 or 2 edges incident to v in G, and therefore deg(v) or deg(v) 2 copies of v (an even number) are unmatched in H,
- 2. for case 2, P uses precisely 1 edge incident to v in G, and therefore deg(v)-1 (an even number) vertices remain unmatched,
- 3. cases 3 and 4 are similar.

By completing P into a perfect matching  $P \cup N$ , we get a perfect matching whose cost equals the cost of the path P, c(P).

Now we show that this holds if we go in the opposite direction. Start with a perfect matching  $M \subseteq E \cup F$  in H of cost c(M) and consider the set of edges  $J = M \cap E$  in G (one could view J as obtained from M by shrinking all cliques of F). Observe that by construction J is an s-t join:

**Definition 3** A set  $J \subseteq E$  of edges is an s-t join iff, for each vertex v

$$\left\{ \begin{array}{l} v \notin \{s, t\} \to deg_J(v) \text{ even} \\ v \in \{s, t\} \to deg_J(v) \text{ odd} \end{array} \right\}$$

We claim that from this s-t join we can derive an s-t path in G of no greater cost.

**Lemma 1** If there is no negative cost cycle in G then, for any s-t join J, there exists an s-t path P of no greater cost.

**Proof of Lemma 1:** Take optimum s-t join J. Remove as many cycles as possible until J is acyclic; let  $C_i$  be these edge-disjoint cycles. Let P denote what remains:

$$J = (\cup_{i=1}^k C_i) \cup P.$$

P is thus an acyclic graph with odd degree at s and t, and even degree everywhere else. Therefore, P must be an s-t path (if there was a vertex of degree at least 3 in this acyclic graph, there would be at least 3 leaves (each of odd degree), and that would be a contradiction.) Furthermore,

$$c(J) = \sum c(C_i) + c(P) \ge c(P)$$

since all cycles are supposed to be non-negative cost.

This means that by solving the minimum cost s-t join in H (and removing any 0 cost cycles in it), we obtain a minimum cost t-t path in G.

### 1.2 Applying the Ellipsoid Method

We apply the ellipsoid method to the problem of finding a perfect matching M of minimum total cost given a graph H and cost function  $c: E \to \mathbb{R}$ .

The first step is to formulate the problem as an integer program, i.e. a linear program in which variables are restricted to take integer values. To every matching M, we associate a vector  $x \in \mathbb{R}^{|E|}$ :

$$M \to x_e = \begin{cases} 1 & \text{for } e \in M \\ 0 & \text{for } otherwise \end{cases}$$

The matching problem then becomes the following integer program:

min 
$$\sum_{e} c_e x_e$$
  
s.t.  $x_e \in \{0, 1\}$   $\forall e \in E$   

$$\sum_{e \in \delta(v)} x_e = 1 \quad \forall v \in V$$

This is not a valid linear program due to the integrality constraint on  $x_e$ . We can attempt to relax this constraint, replacing  $x_e \in \{0,1\}$  with  $0 \le x_e \le 1$ , to obtain a valid linear program. If this would result in a linear program in which every vertex x had only coordinates taking values 0 or 1, we would be done since we are guaranteed that the optimum of a linear program is at a vertex. However, in this case, there are vertices of this linear program which are not integer valued, and also this linear program might have a non-empty feasible region while there are no perfect matchings. Consider indeed a cycle of length 3 (thus |V| = 3). Clearly, there are no perfect matching but the feasible region of this linear program is non-empty since we can let  $x_e = 1$  for every edge e (this is a vertex of the corresponding linear program).

To be able to use linar programming, we need to add more constraints to guarantee that the linear program has all its vertices corresponding to matchings. This can be done and is an important result due to Edmonds.

Theorem 2 (Edmonds) All vertices of

$$\begin{cases} \sum_{e \in \delta(v)} x_e = 1 & \forall v \in V \\ \sum_{e \in (S:\bar{S})} x_e > = 1 & \forall S \subseteq V \text{ with } |S| \text{ odd} \\ 0 \le x_e \le 1 & \forall e \in E \end{cases}$$

are incidence vectors of perfect matchings, and therefore a minimum cost perfect matching can be obtained by minimizing  $c^Tx$  over the above constraints.

(Recall that the cut  $(S:\bar{S})$  denotes the set of edges with exactly one endpoint in S, and similarly  $\delta(v) = (\{v\}: V \setminus \{v\})$ ). Notice that the second set of constraints are indeed satisfied by the incidence vectors of all perfect matchings. If |S| is odd, no perfect matching can match the vertices together, and thus at least one of them has to be matched to a vertex outside S, leading to the validity of these constraints.

This linear program seems completely impractical because the number of constraints is

$$|V| + |E| + \frac{1}{2}2^{|V|}.$$

This is exponential in the size of the input. However, we can use the ellipsoid method, and avoid having to explicitly list all constraints. Indeed, for the ellipsoid to work to optimize over a convex set  $K \subseteq \mathbb{R}^n$ , we only need to have a separation oracle for K. This is an algorithm which, given  $a \in \mathbb{R}^n$ ,

- either claim  $a \in K$ ,
- or output  $c: \{x: c^T x < c^T a\} \supseteq K$ .

If we have a separation oracle then we can easily extend the ellipsoid algorithm from finding a point in K to minimizing  $c^Tx$  over K. Indeed every time a point a in K is found, we can update the best point found so far and add the inequality  $c^Tx \leq c^Ta$  and proceed with the ellipsoid algorithm. Formally, one would need to argue about the choice of R and r for the starting ellipsoid and for deciding when to stop, but this is omitted here. Since the ellipsoid algorithm makes a polynomial number of calls to the separation oracle, we can derive a polynomial-time algorithm for optimizing over K provided that the separation oracle itself can be implemented in polynomial-time.

For the linear inequality description given in Theorem 2, checking if a vector  $a \in \mathbb{R}^n$  satisfies the first set of constraints is clearly polynomial (just check each of them individually), but for the second set of constraints, the separation problem can be solved by solving the *minimum odd cut* problem: Given a, find

$$\lambda = \min_{S \subseteq V: |S| odd} \sum_{(S:\bar{S})} a_e.$$

Indeed, if  $\lambda \geq 1$  then a satisfies all inequalities  $\sum_{(S:\bar{S})} x_e \geq 1$ . Otherwise, if  $\lambda < 1$ , then we have found a set S for which the inequality  $\sum_{(S:\bar{S})} x_e \geq 1$  is violated by a, and we can return this inequality. In the problem set, we show how the minimum odd cut problem can be solved as a sequence of a polynomial number of minimum s-t cut problems. Through the ellipsoid, this gives a polynomial-time algorithm for solving the minimum cost perfect matching problem. There is also a (much more combinatorial) polynomial-time algorithm due to Edmonds for matching that does not involve the ellipsoid algorithm, but this is a nice illustration of the power of the approach through a separation oracle.

# 2 Semidefinite Programming

Yet another application of the ellipsoid algorithm is in the solution of semidefinite programming problems. Semidefinite programming is a type of convex optimization in which a linear objective function is optimized over the intersection of positive semidefinite matrices with an affine space. It is more general class of problems than linear programming.

Let's denote by  $\mathbb{S}^n$  the class of  $n \times n$  real, symmetric matrices.

**Definition 4** For  $A \in \mathbb{S}^n$  we say that A is positive definite if we have  $x^T A x > 0 \ \forall x \in \mathbb{R}^n, x \neq 0$  and that it is positive semidefinite if  $x^T A x \geq 0 \ \forall x \in \mathbb{R}^n$ .

If A is positive definite, we write that  $A \succeq 0$ ; if it is positive semidefinite, we write that  $A \succeq 0$ . Remember that all eigenvalues of a real symmetric matrix are real. An equivalent definition for positive definiteness is  $A \succ 0$  iff  $\lambda_i > 0 \ \forall$  eigenvalues  $\lambda_i$  of A, and that  $A \succeq 0$  iff  $\lambda_i > 0$ . We define the PSD cone as: PSD =  $\{A \in \mathbb{S}^n : A \succeq 0\}$ .

Lemma 3 PSD is a convex cone.

#### Proof of Lemma 3:

$$\forall x : x^T (\lambda A + (1 - \lambda)B)x = \lambda x^T A x + (1 - \lambda)x^T B x \ge 0.$$

We can see that the first term on the right-hand side of this equality,  $\lambda x^T A x$ , must be nonnegative by our definition of positive semidefiniteness. So too must the second term (since we have  $0 \le \lambda \le 1$ ); therefore, their sum must also be nonnegative.

We need a notion of an inner product over symmetric matrices. The Frobenius inner product,  $A \bullet B$ , of two matrices  $A, B \in \mathbb{S}^n$  is defined as

$$A \bullet B = \sum_{i} \sum_{j} A_{ij} B_{ij} = \text{Tr}(A^T B) = \text{Tr}(AB^T),$$

where Tr denotes trace. The Frobenius inner product is the component-wise inner product of the two matrices as though they were vectors.

In a semidefinite programming problem, we are minimizing over  $X \in \mathbb{S}^n$ ; as such matrices are symmetric, there are n(n+1)/2 unknown and we could view this as optimizing over  $\mathbb{R}^{n(n+1)/2}$ . The primal form of a semidefinite programming problem is as follows. Given  $C \in \mathbb{S}^n$ ,  $A_i \in \mathbb{S}^n$ , and  $b_i \in \mathbb{R}$  for  $i \in \{1, \dots, m\}$ , we are attempting to

$$\min C \bullet X$$

subject to the constraints

$$A_i \bullet X = b_i$$

and

$$X \succeq 0$$
.

Just as with linear programming, a dual semidefinite program also exists; this will be discussed in greater detail in the next lecture.

It is important to note that the (unique) optimum solution may be irrational, so it is not clear how to even concisely output the solution. Consider, for example, the problem of

$$\min \left( \begin{array}{cc} 0 & 1 \\ 1 & 0 \end{array} \right) \bullet X$$

subject to

$$\begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix} \bullet X = 1$$
$$\begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix} \bullet X = 5,$$

and  $X \succeq 0$ . Clearly, the optimum matrix is

$$X = \left( \begin{array}{cc} 1 & -\sqrt{5} \\ -\sqrt{5} & 5 \end{array} \right),$$

with an irrational objective function value.

Given  $A_i$  and  $b_i$ , the semidefinite program is feasible iff  $\exists X \succeq 0 : A_i \bullet X = b_i$ . In fact, the problem of determining whether a semidefinite program is feasible is an open question and is not known to be in NP. As a special case, consider the question of whether, given  $a_1, ...a_n, b \in \mathbb{N}$ ,  $\sum_{i=1}^n \sqrt{a_i} < b$ . This can be formulated as the feasibility question of a semidefinite program. It is easy to evaluate  $\sum_{i=1}^n \sqrt{a_i}$  but it is unclear how many bits or decimal places of accuracy are sufficient to determine whether it is or not less than b. The complexity of this question is open.

With the ellipsoid algorithm, one can in polynomial time find an almost feasible solution X, which is also almost optimum (up to some  $\epsilon$ ). Indeed, the separation problem over

$$\{X \in \mathbb{S}^n : A_i \bullet X = b_i \text{ for } i \in \{1, \dots, m\}, X \succeq 0\},$$

can be solved efficiently. Indeed, the linear constraints are easy to check individually while checking whether  $X \succeq 0$ , i.e.  $X \in PSD$ , can be done by a Cholevsky decomposition. In  $O(n^3)$  time, this either proves that  $X \succeq 0$  or provides a vector  $a \in \mathbb{R}^n$ ,  $a \neq 0$  such that  $a^TXa < 0$ . This means that we have found an inequality violated by our current matrix X (namely the (linear in X) inequality  $a^TXa \geq 0$ ) and we can use it to cut our ellipsoid in half.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

# Lecture 14

Lecturer: Michel X. Goemans

## 1 Introduction

For this lecture we'll look at using interior point algorithms for solving linear programs, and more generally convex programs. Developing originally in 1984 by Narendra Karmarkar, there have been many variants (with some of the keywords 'path following', 'primal-dual', 'potential reduction', etc.) on interior point algorithms, especially through the late 80s and early 90s. In the late 90s, people began to realize that interior point algorithms could also be used to solve semidefinite programs (or, even more generally, convex programs). As much as possible, we will discuss linear programming, semidefinite programming, and even a larger class called conic programming in a unified way.

# 2 Linear Programming

We will start with linear programming. Remember that in linear programming, we have: **Primal:** Given  $A \in \mathbb{R}^{m \times n}$ ,  $c \in \mathbb{R}^n$  and  $b \in \mathbb{R}^m$ , find  $x \in \mathbb{R}^n$ :

$$\begin{array}{ll}
\text{Min} & c^T x \\
\text{s.t.} & Ax = b, x > 0.
\end{array}$$

Its dual linear program is:

**Dual:** Find  $y \in \mathbb{R}^m$ :

$$\begin{array}{ll}
\text{Max} & b^T y \\
\text{s.t.} & A^T y \le c.
\end{array}$$

We can introduce non-negative slack variables and rewrite this as:

**Dual:** Find  $y \in \mathbb{R}^m$ ,  $s \in \mathbb{R}^n$ :

$$\begin{aligned} \text{Max} & b^T y \\ \text{s.t.} & A^T y + s = c, s \ge 0. \end{aligned}$$

We know that, for a feasible solution, x in the primal, and a feasible solution (y, s) in the dual, we know by complementary slackness that they will both be optimal (for the primal and the dual resp.) iff  $x^T s = 0$ . Since this is the component-wise product of two non-negative vectors, we can equivalently say:

$$x_i s_i = 0 \quad \forall j.$$

### 2.1 Using the Interior Point Algorithm

The interior point algorithm will iteratively maintain a strictly feasible solution in the primal, such that for all values of j,  $x_j > 0$ . Similarly in the dual, it will maintain a y and an s such that for all values of j,  $s_j > 0$ . Because of this strict inequality, we can never reach our optimality

condition stated above; however, we'll get very close, and once we do, we can show that a jump from this non-optimal solution (for either the primal or the dual) to a vertex of improved cost (of the corresponding program) will provide an optimal solution to the (primal or dual) program.

In some linear programs, it may not be possible to start with a strictly positive solution. For example, for any feasible solution to the program, it may be that  $x_j = 0$ , so we may be unable to find a strictly feasible solution with which to start the algorithm. This can be dealt with easily, but we will not discuss this. We'll assume that the primal and dual both have strictly feasible solutions.

# 3 Semidefinite Programming

As introduced in the previous lecture, in semidefinite programming, our variables are the entries of a symmetric postitive semidefinite matrix X. Let  $S^n$  denote the set of all real, symmetric and  $n \times n$  matrices. For two such matrices A and B, we define an inner product

$$A \bullet B = \sum_{i} \sum_{j} A_{ij} B_{ij} = Trace(A^{T}B) = Trace(AB).$$

Semidefinite programming (as a minimization problem) is

Min 
$$C \bullet X$$
  
s.t.  $A_i \bullet X = b_i$   $i = 1...m$   
 $X \succ 0$ .

Remember that for a symmetric matrix M,  $M \succeq 0$  means that M is positive semidefinite, meaning that all of its (real) eigenvalues  $\lambda \geq 0$ , or equivalently,  $\forall x, x^T M x \geq 0$ .

### 3.1 Dual for SDP

When working with linear programs, we know the existence of a dual linear program with a strong property: Any feasible dual solution provides a lower bound on the optimum primal value and, if either program is feasible, the optimum primal and optimum dual values are equal. Does a similar dual for a semidefinite program exist? The answer if yes, although we will need some additional condition. We claim that the dual takes the following form.

**Dual:** Find  $y_i \in \mathbb{R}^n$ , and  $S \in S^n$ :

$$\begin{aligned} \text{Max}_{y \in \mathbb{R}^m} & b^T y \\ \text{s.t.} & \sum_i y_i A_i + S = C \\ S \succeq 0. \end{aligned}$$

#### 3.1.1 Weak Duality

For weak duality, consider any feasible solution x in the primal, and any feasible solution (y, S) in the dual. We have:

$$C \bullet X = \left(\sum_{i} y_{i} A_{i} + S\right) \bullet X$$

$$= \sum_{i} y_{i} (A_{i} \bullet X) + S \bullet X$$

$$= \sum_{i} y_{i} b_{i} + S \bullet X$$

$$= b^{T} y + S \bullet X$$

$$\geq b^{T} y,$$

the last inequality following from Lemma 1 below. This is true for any primal and dual feasible solutions, and therefore we have  $z \ge w$ , where:

$$z = \min\{C \bullet X : X \text{ feasible for primal}\},\ w = \max\{b^T y : (y, S) \text{ feasible for dual}\}.$$

**Lemma 1** For any  $A, B \succeq 0$ , we have  $A \bullet B > 0$ .

**Proof of Lemma 1:** Any positive semidefinite matrix A admits a Cholesvky decomposition:  $A = V^T V$  for some  $n \times n$  matrix V. Thus,

$$A \bullet B = Trace(AB) = Trace(V^TVB) = Trace(VBV^T),$$

the last inequality following from the fact that, for (not necessarily symmetric) square matrices C and D, we have Trace(CD) = Trace(DC). But  $VBV^T$  is positive definite (since  $x^TVBV^Tx \ge 0$  for all x), and thus its trace is nonnegative, proving the result.

A similar lemma was used when we were talking about linear programming, namely that if  $a, b \in \mathbb{R}^n$  with  $a, b \ge 0$  then  $a^T b \ge 0$ .

#### 3.1.2 Strong Duality

In general, it's not true that z = w. Several things can go wrong.

In defining z, we wrote:  $z = \min C \bullet X$ . However, that min is not really a min, but rather an infimum. It might happen that the infimum value can be approached arbitrarily closely but no solution may attain that value precisely. Similarly in the dual, the supremum may not be attained.

In addition, in semidefinite programming, it is possible that the primal may have a finite value, but that the dual may be infeasible. In linear programming, this was not the case. If the primal had a finite feasible value and was bounded, the dual was also finite and with the same value. In semidefinite programming, the primal can be finite, while the dual may be infeasible or vice versa.

In addition, both the primal and dual could be finite, but they could be of differing values.

That all said, in the typical case, you do have strong duality (z = w), but only necessarily under certain conditions.

#### 3.1.3 Introducing a Regularity Condition

Assume that the primal and dual have a strictly feasible solution. This means that for the primal:

$$\exists X \quad \text{s.t.} \ A_i \bullet X = b_i \quad i = (1...m).$$
  
 $X \succ 0.$ 

' $A \succ 0$ ' denotes that A is a positive-definite matrix, meaning that  $\forall a \neq 0, a^T X a > 0$ , or equivalently that all its eigenvalues  $\lambda_i$  satisfy  $\lambda_i > 0$ .

Likewise, in the dual, there exists y and S such that:

$$\sum_{i} y_i A_i + S = C$$
$$S \succ 0.$$

If we assume this 'regularity condition' that we've defined above, then the primal value z is finite and attainable (i.e. it is not an infimum, but actually a minimum), and the dual value w is attained and furthermore z=w. This is given without proof.

# 4 Conic Programming

Conic Programming is a generalization of both Linear Programming and Semidefinite Programming. First, we need the definition of a cone:

**Definition 1** A cone is a subset C of  $\mathbb{R}^n$  that has the property that for any  $v \in C$  and  $\lambda \in \mathbb{R}^+$ ,  $\lambda v$  is also in C

Conic Programming is constrained optimization over K, a closed convex cone, with a given inner product  $\langle x,y\rangle$ . We can, for example, take  $K=\mathbb{R}^n$  and  $\langle x,y\rangle=x^Ty$  for any  $x,y\in\mathbb{R}^n$ ; this will lead to linear programming. Conic programming, like LP and SDP, has both a primal and a dual form; the primal is:

**Primal:** Given  $A \in \mathbb{R}^{m \times n}$ ,  $b \in \mathbb{R}^m$ , and  $c \in \mathbb{R}^n$ :

min 
$$\langle c, x \rangle$$
  
s.t.  $Ax = b$   
 $x \in K$ .

More generally, we could view K as a cone in any space, and then A is a linear operator from K to  $\mathbb{R}^m$ . To form the dual of a conic program, we first need to find the *polar cone*,  $K^*$ , of K. The polar cone is defined to be the set of all s such that for all x in K,  $\langle s, x \rangle \geq 0$ . For instance, the polar cone of  $\mathbb{R}^n_+$  is  $\mathbb{R}^n_+$  itself (indeed if  $s_j < 0$  then we have  $s \notin K^*$  since  $\langle e_j, s \rangle < 0$ ; conversely, if  $s \geq 0$  then  $\langle x, s \rangle \geq 0$ ). In the case that  $K = K^*$ , we say that K is *self-polar*. Similarly, the polar cone of PSD, the set of positive semidefinite matrices, is also itself.

We also define the *adjoint* (operator)  $A^*$  of A to be such that, for all x and y,  $\langle A^*y, x \rangle = \langle y, Ax \rangle$ . For example, if the inner product is a standard dot product and A is the matrix corresponding to a linear transformation from  $\mathbb{R}^n$  to  $\mathbb{R}^m$ , then  $A^* = A^T$ . To write the conic dual, we introduce a variable  $y \in \mathbb{R}^m$  and  $s \in \mathbb{R}^n$  and optimize:

Dual:

max 
$$\langle b, y \rangle$$
  
s.t.  $A^*y + s = c$   
 $s \in K^*$ .

#### 4.0.4 Weak Duality

We can prove weak duality – that the value of the primal is at least the value of the dual – as follows. Let x be any primal feasible solution and (y, s) be any dual feasible solution. Then

$$\langle c, x \rangle = \langle A^*y + s, x \rangle = \langle A^*y, x \rangle + \langle s, x \rangle = \langle y, Ax \rangle + \langle s, x \rangle = \langle b, y \rangle + \langle s, x \rangle \ge \langle b, y \rangle,$$

where we have used the definition of  $K^*$  to show that  $\langle s, x \rangle \geq 0$ . This means that z, the infimum value of the primal, is at least the supremum value w of the dual.

#### 4.0.5 Strong Duality

In the general case, we don't know that the two values will be equal. But we have the following statement (analogous to the regularity condition for SDP): if there exists an x in the *interior* of K, such that Ax = b, and a s in the interior of  $K^*$ , with  $A^*y + s = c$ , then the primal and the dual both obtain their optimal values, and those values are equal.

## 4.1 Semidefinite Programming as a Special Case of Conic Programming

LP is a special case of conic programming, if we let  $K = \mathbb{R}^n_+$  and take the inner product to be the standard dot product  $\langle a,b\rangle = a^{\mathrm{T}}b$ . We can also make any SDP into a conic program; first, we need a way of transforming semidefinite matrices into vectors. Since we are optimizing over *symmetric* matrices, we introduce a map svec(M) that only takes the lower triangle of the matrix (including the diagonal). To be able to use the standard dot product with these vectors, svec multiplies all of the off-diagonal matrices by  $\sqrt{2}$ . So svec maps X to

$$(x_{11}, x_{22}, \dots, x_{nn}, \sqrt{2}x_{12}\sqrt{2}x_{13}, \dots, \sqrt{2}x_{(n-1)n}).$$

As a result:

$$\langle svec(X), svec(Y) \rangle = \sum_{i=1}^{n} x_{ii} y_{ii} + \sum_{1 \le i < j \le n} \sqrt{2} x_{ij} \sqrt{2} y_{ij} = \sum_{1 \le i, j \le n} x_{ij} y_{ij} = Tr(AB) = A \bullet B.$$

This means that using the basic dot product as the inner product is compatible with the inner product used in SDP. So we can formulate an SDP as a conic program by letting  $K = \{svec(X) : X \succeq 0\}$ , which is a closed convex cone. To show convexity, we need to show that if A and B are matrices in PSD, then  $\lambda A + (1 - \lambda)B$  is also in PSD for  $0 \le \lambda \le 1$ . Indeed, for any vector v, we have

$$v^{\mathrm{T}}(\lambda A + (1 - \lambda)B)v = \lambda (v^{\mathrm{T}}Av) + (1 - \lambda) (v^{\mathrm{T}}Bv) \ge 0.$$

Then, we can let the matrix A be a matrix that is the composition of the corresponding  $A_i$  of the semidefinite program, so that

$$A \ svec(X) = (A_i \bullet X)_{i=1,\dots,m}$$

Now that the semidefinite program is cast into a conic program, we could write the conic dual, and one could verify that what we get is precisely the dual of the semidefinite program we defined earlier.

Instead of mapping the space of symmetric matrices (say  $p \times p$ ) into  $\mathbb{R}^n$  (with  $n = \binom{p+1}{2}$ ) using  $svec(\cdot)$ , one could simply define  $K = \{X \in S^p : X \succeq 0\}$  and  $\langle X, Y \rangle = X \bullet Y$ . Now our linear operator  $A: S^n \to \mathbb{R}^m$  then maps X into  $(A_i \bullet X)_{i=1,\dots,m}$ . Its adjoint  $A^* : \mathbb{R}^m \to S^n$  is defined by:

$$\langle A^*(y), X \rangle := \langle y, A(X) \rangle = \sum_{i=1}^m y_i A_i \bullet X,$$

implying that  $A^*$  maps y to  $\sum_{i=1}^m y_i A_i$ . The dual SDP now arises as the dual conic program.

### 4.2 Barrier Functions

To solve the conic program, we will require a barrier function F. This is a function from int(K), the interior of K, to  $\mathbb{R}$  such that

- 1. F is strictly convex,
- 2.  $F(x_i) \to \infty$  as  $x_i \to x \in \partial K$ , where  $\partial K$  is the boundary of K.

We will use the barrier function to "punish" candidate solutions that are close to the boundary of K, keeping the current point inside K. "Good" barrier functions, that result in a fast overall algorithm, have more properties that will be described in a later lecture. For  $K = \mathbb{R}^n_+$ , a good barrier function is

$$F(x) = -\sum_{i} \log(x_i).$$

As any one of the coordinates approaches 0, the log approaches  $-\infty$ , so the total function goes to  $\infty$ . One can also check that this function is strictly convex.

For  $K = svec(PSD^p)$  or more simply  $K = PSD^p$  (the set of symmetric  $p \times p$  positive semidefinite matrices), the interior of K is the set of positive definite matrices, which all have strictly positive determinants. (This is because the determinant is equal to the product of the eigenvalues, which are all strictly positive for a positive definite matrix.) So we can use the following barrier function:

$$F(X) = -\log(\det(X)).$$

As X approaches the boundary of K, the determinant goes to zero, and F goes to infinity. One can also check that this function is strictly convex (its Hessian, the matrix of second derivatives, can be shown to be positive definite).

## 4.3 A Primal-Dual Interior-Point Method

Once we have a barrier function, we will set the objective function of the primal to  $\langle c, x \rangle + \mu F(x)$ , where  $\mu$  is a parameter that we will adjust through the course of the algorithm. Assuming that we start with an initial candidate that belongs to int(K), we can ignore the constraint that  $x \in K$ , since that will be enforced through the barrier function, since there will be an infinite penalty for leaving K. Our primal barrier problem  $BP(\mu)$  will be:

$$\min\{\langle c, x \rangle + \mu F(x) : Ax = b\}.$$

Analogously, for the dual, we change the objective function to  $\langle b, y \rangle - \mu F^*(s)$ , where  $F^*$  is a barrier function for the dual; we can also eliminate the constraint that  $s \in K^*$ . Our dual barrier problem,  $BD(\mu)$ , is:

$$\max\{\langle b, y \rangle - \mu F^*(s) : A^*y + s = c\}.$$

The basic method of the algorithm is to have a current value of  $\mu$ , and keep track of the optimal solutions in the primal  $BP(\mu)$  and dual  $BD(\mu)$ . As long as  $\mu$  is not zero, there is a unique optimum solution for both, since the objective function is the sum of a linear function and a strictly-convex function, which results in a strictly-convex function. We will steadily decrease  $\mu$ , and keep track of the optimal solutions as they change; the paths the optimum solutions trace out is called the *central path* (or *central trajectory*). We will show that the (primal and dual) central paths will converge to an optimum value of the primal and dual original programs.

In the special case of linear programming, once we are sufficiently close, we can round the current solution to the nearest vertex to obtain an optimum solution. For semidefinite programming, though, we do not have such an algorithm to convert a solution for small enough  $\mu$  to an optimum solution.

Let's characterize the optimum solution to  $BP(\mu)$  and  $BD(\mu)$ . We derive now the so-called KKT optimality conditions. If there were no constraints in the conic program, then the minimum would be found when the gradient of the objective function is zero. If there are affine constraints like Ax = b, however, the minimum will occur when the gradient is normal to the affine space of feasible solutions. Otherwise, we could move along the projection of the gradient on the feasible space, and improve our objective function.

For simplicity, let's first look at the case when  $K = K^* = \mathbb{R}^n_+$ , and the barrier function is  $F(x) = -\sum_i \log(x_i)$ . The objective function of the primal is  $\langle c, x \rangle - \mu F(x)$ , and the partial derivatives are

$$\frac{\partial}{\partial x_j} \left( \langle c, x \rangle - \mu F(x) \right) = c_j - \frac{\mu}{x_j}$$

so the gradient is  $c - \mu x^{-1}$ , where  $x^{-1}$  denotes the vector  $\{1/x_i\}$ . But since this gradient is normal to the constraint Ax, the gradient must be of the form  $A^Ty$  for some y. So if we let  $s = \mu x^{-1}$ , then we know c - s is of the form  $A^Ty$ , or equivalently,

$$\begin{array}{rcl} A^{\mathrm{T}}y + s & = & c \\ s & = & \mu x^{-1}. \end{array}$$

The last constraint is equivalent to

$$x_i s_i = \mu \tag{1}$$

for all i.

Now, looking at the dual: the gradient with respect to y is b, which must be of the form Ax for some x. The gradient with respect to s is  $\mu s^{-1}$ , which must equal the same x. This means that

$$Ax = b$$
$$s = \mu x^{-1},$$

and the last equality is again equivalent to (1).

So if we denote by  $x(\mu)$  the optimum solution to the primal  $BP(\mu)$  and by  $(y(\mu), s(\mu))$  the optimum solution to the dual  $BD(\mu)$ , one observes that each of them is a certificate of optimality for the other and furthermore:

$$x_i(\mu)s_i(\mu) = \mu.$$

This means that the duality gap in the original primal/dual pair of linear programs is  $x^T s = n\mu$  and therefore the duality gap goes to 0 as  $\mu$  goes to 0. Thus the central path  $(x(\mu), y(\mu), s(\mu))$  will converge to optimum solutions to both the primal and dual linear programs.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 15: Interior Point Algorithms for Conic Programming

Lecturer: Michel X. Goemans

### 1 Introduction

In this lecture, we continue our discussion of the interior-point algorithms for conic programming. In our study of conic programming, we will focus primarily on the following two spaces of possible solutions:

- Linear Programming:  $K = \mathbb{R}_n^+$ ,
- Semi-definite Programming:  $K = PSD_p$ ; that is, K is the cone of positive semi-definite matrices  $(K = \{X : y^*Xy \ge 0, \forall y \in \mathbb{R}^p, y \ne 0\}).$

We begin by revising the conic program for LP. Let K be a closed convex cone in  $\mathbb{R}^n$ . Then,  $K^*$  is the polar cone of K, which is defined as  $K^* = \{s : \langle x, s \rangle \geq 0, \ \forall \ x \in K\}$ .

The primal program for conic programming is

min 
$$\langle c, x \rangle$$
 s.t.  $Ax = b$ ,  $x \in K$ .

The dual program for conic programming is

$$\max \langle b, y \rangle \text{ s.t. } A^*y + s = c,$$
$$s \in K^*,$$

where  $A^*$  is the adjoint matrix of A. This generalizes both LP and SDP.

### 2 Barrier Functions

In the last lecture, we introduced barrier functions, which are useful in computing the optimal of the conic programs.

**Definition 1** A function  $F: int(K) \to \mathbb{R}$  is a barrier function, if

- 1. F is strictly convex, and
- 2.  $(x_k \to x \in \partial_K \ as \ k \to \infty) \Rightarrow (F(x_k) \to \infty \ as \ k \to \infty)$

The last property indicates that F approaches infinity as  $x_k$  moves closer to the boundary of K.

To compute the optimal of the conic programs, we first define the barrier primal  $(BP_{\mu})$  and the barrier dual  $(BD_{\mu})$  programs.

$$\mathrm{BP}_{\mu} : \min \langle c, x \rangle + \mu F(x) \text{ s.t. } Ax = b,$$
 
$$(x \in \mathrm{int}(K)).$$

Figure 1: The central path from  $\mu = \infty$  to  $\mu = 0$ , the optimal solution, in the primal and dual space.

As we will start from an interior point, the condition  $x \in \text{int}(K)$  will remain true because F becomes infinite closer to the boundary of K according to the definition of the barrier function (1).

$$\mathrm{BD}_{\mu} : \max \langle b, y \rangle - \mu F_*(s) \text{ s.t. } A^*y + s = c,$$
  
 $(s \in \mathrm{int}(K^*)),$ 

where  $F_*$  is a barrier function on  $K^*$ .

For the special cases of LP and SDP, we introduce two barrier functions, also known as *canonical* barrier functions, which will help us find an optimal for the initial conic programs efficiently.

For 
$$K = \mathbb{R}_n^+$$
:  $F(X) = -\sum_{j=1}^n \ln(x_j)$  (1)

For 
$$K = PSD_p$$
:  $F(X) = -\ln(\det(X))$ , (2)

and similarly for  $F_*$ .

These functions are in fact very similar. In relation (2), X is a symmetric matrix, so  $\det(X)$  is the product of its eigenvalues, say  $\lambda_i$ . Thus,  $F(X) = -\sum_j \ln(\lambda_j)$  which is similar to the expression in relation (1).

Consider the set of optimal solutions as  $\mu \to 0$ . Note that when  $\mu = 0$ , the barrier programs become the initial conic programs and thus their optimal solutions are optimal solutions for the initial programs as well. The set of solutions as  $\mu \to 0$  represents a path, called the *central path*. The path starts at  $\mu = \infty$  and we show in the next section that as  $\mu$  tends to 0, it converges to an optimal solution as illustrated in Figure 1.

# 3 Optimality Conditions

In this section we show a strong duality relation between the unique optimum solution to  $(BP_{\mu})$  and the unique optimum solution to  $(BD_{\mu})$ . We focus on LP and SDP.

Claim 1 If x is optimum in  $BP_{\mu}$  for  $K = \mathbb{R}_n^+$  (LP), then there exists y and s such that:

1. 
$$A^*y + s = c$$
,

2. 
$$s - \mu x^{-1} = 0$$
.

**Proof:** The gradient of F at an optimum has to be normal to the region of feasible solutions because otherwise we would be able to improve on the optimum. Therefore, we have

$$\exists y, \ c + \mu \nabla F(x) = A^* y \tag{3}$$

Let us define

$$s = -\mu \nabla F(x). \tag{4}$$

By substituting for s in (3), we obtain  $c - s = A^*y$  which proves the first relation.

Next, let us prove the second relation. We substitute F(x) according to its definition (1) in (4) and obtain

$$s_j - \mu \frac{1}{x_j} = 0, j = 1 \dots n$$

and thus

$$s = \mu x^{-1},\tag{5}$$

which proves the second relation. Note that since both x and  $\mu$  are positive, it follows that  $s \in K^*$ .

Claim 2 If X is optimum in  $BP_{\mu}$  for  $K = PSD_{p}$  (SDP) then there exists  $y \in \mathbb{R}^{m}$  and  $S \in PSD_{p}$ :

1. 
$$A^*y + S = C$$
,

2. 
$$S - \mu X^{-1} = 0$$
.

Here  $A^*y = \sum_i y_i A_i$  as we established last lecture.

**Proof:** Similarly to the proof of Claim 1, the gradient of F at X has to be normal on the region of feasible solutions because otherwise X would not be optimal. Therefore,

$$\exists y, c + \mu \nabla F(X) = A^* y, \tag{6}$$

where  $A^*$  is the adjoint. We claim that

$$\nabla F(X) = -X^{-1}. (7)$$

Let us show this if X was not necessarily symmetric; our derivation thus will not be fully correct. Observe that

$$\frac{\partial F(X)}{\partial x_{ij}} = -\frac{1}{\det X} \frac{\partial \det X}{\partial x_{ij}} = -\frac{C_{ij}}{\det X},$$

where  $C_{ij}$  is the cofactor matrix of element (i, j). The last equality follows (for not necessarily symmetric matrices) from the fact that, for any i,

$$\det X = \sum_{i} x_{ij} C_{ij}.$$

(For symmetric matrices  $C_{ij}$  depends on  $x_{ij} = x_{ji}$ .) We can thus deduce our claim (7). By substituting this relation in (6), we have

$$c - \mu X^{-1} = A^* y.$$

By substituting  $S = \mu X^{-1}$  in this relation we obtain the desired relations. Furthermore, note that  $S \in K^*$  (i.e.  $S \succeq 0$ ) because X is positive definite and  $\mu$  is positive.

Note that the dual of the above claims are similar. That is, if y, s are optimal for  $\mathrm{BD}_{\mu}$ , we have  $\exists x$ , s.t. Ax = b and  $x + \mu \nabla F_*(s) = 0$ . For LP, we would have  $x - \mu s^{-1} = 0$  and thus  $xs = \mu$  and for  $\mathrm{SDP}$ ,  $X - \mu S^{-1} = 0$  and thus  $XS = \mu I$ .

### 4 Duality Gap

Recall that the duality gap between a primal feasible solution x and a dual feasible solution (y, s) is defined as the difference between their values. Furthermore, this expression simplifies to  $\langle s, x \rangle$  for conic programs. Let  $x(\mu)$  denote the (unique) optimum solution to  $\mathrm{BP}_{\mu}$  and  $(y(\mu), s(\mu))$  the (unique) optimum solution to  $\mathrm{BD}_{\mu}$ . Since they are feasible for the original primal and dual conic programs, we have that the duality gap is  $\langle x(\mu), s(\mu) \rangle$ . This gives us an indication of how far we are from optimal. We will show now that this duality gap converges to 0 as  $\mu$  tends to 0, and thus the central path converges to an optimum solution.

In the previous section, we found that optimality of the primal implies  $s = \mu x^{-1}$ . For LP, the duality gap will be

$$\langle x(\mu), s(\mu) \rangle = \sum_{j} x_{j}(\mu) \cdot \mu / x_{j}(\mu) = n\mu.$$

Therefore, as  $\mu \to 0$ ,  $\langle x(\mu), s(\mu) \rangle \to 0$ .

For SDP, we have

$$\langle X(\mu), S(\mu) \rangle = X(\mu) \bullet S(\mu) = Tr(X(\mu) \cdot S(\mu)) = Tr(\mu I_p) = p\mu$$

where  $I_p$  is the identity matrix of dimension of dimension p. Thus, as  $\mu \to 0$ ,  $\langle X(\mu), S(\mu) \rangle \to 0$ .

### 5 Barrier Function Properties

Both canonical barrier functions we introduced, (1) and (2), are *self-concordant*. Let us mention the definition of self-concordance, but we shall not elaborate further on this property.

**Definition 2** Let  $Q \subseteq \mathbb{R}^n$  be an open convex set. Function  $F: Q \to \mathbb{R}^n$  is a self-concordant barrier function if it is at least three times differentiable, convex, and satisfies the properties:

- 1.  $|D^3F(x)[h,h,h]| \leq 2(D^2F(x)[h,h])^{3/2}$ ,
- 2.  $|DF(x)[h]|^2 < \vartheta D^2 F(x)[h,h]$ , and
- 3.  $F(x) \to \infty$  as  $x \to \partial Q$ .

Here  $D^k F(x)[h, ..., h]$  is the k-th directional of F at x along the direction  $h \in \mathbb{R}^n$ , and the constant  $\vartheta$  is called the parameter of the barrier function. The parameter  $\vartheta$  determines the speed of the underlying interior point method.

**Definition 3** A function is  $\nu$ -logarithmically homogenous if  $\forall x, \forall \tau > 0, F(\tau x) = F(x) - \nu \ln(\tau)$ .

**Remark 1** The canonical barrier functions defined in (1) and (2) are  $\nu$ -logarithmically homogenous.

**Proof:** First, let us consider the case when  $K = \mathbb{R}^n_+$ .

$$F(\tau x) = -\sum_{j=1}^{n} \ln(\tau x_j)$$
$$= -n \ln(\tau) - \sum_{j=1}^{n} \ln(x_j)$$
$$= -n \ln(\tau) + F(x)$$

which proves the remark for  $\nu = n$ .

Let us consider next  $K = PSD_p$ . We have

$$F(\tau X) = -\ln(\det(\tau X))$$

$$= -\ln(\tau^p \det(X))$$

$$= -p\ln(\tau) - \ln(\det(X))$$

$$= -p\ln(\tau) + F(X)$$

which proves the remark for  $\nu = p$ .

### 6 Interior-Point Algorithms

We begin with an overview of the algorithm.

- 1. Start with point  $x_0$  for the primal and points  $y_0, s_0$  for the dual and a value for  $\mu$  of  $\mu_0$ . These points should be close to the points on the central path:  $x(\mu_0)$  for the primal and  $s(\mu_0), y(\mu_0)$  for the dual for some definition of closeness that we will introduce.
- 2. At every step k, decrease  $\mu$  and compute new points  $x_k, y_k, s_k$  close to the points  $x(\mu_k)$  for the primal and  $s(\mu_k), y(\mu_k)$  for the dual that are located on the central path.
- 3. As  $\mu \to 0$ , the solutions converge to the optimal solution.

We need to define a notion of distance and closeness to the central path.

### 7 Distance to Central Path

To define what we mean by being "close" to the central path, we need a distance function parametrized by  $\mu$  that measures how close x is to s. This distance  $d_{\mu}(x,s)$  should be equal for the primal and for the dual, and furthermore it should be obviously zero if we are on the central path:

$$d_{\mu}(x,s) = 0$$
 if  $s + \mu \nabla F(x) = 0$ .

Similar conditions must hold for the dual as well, hence  $d_{\mu}(x,s) = 0$  if  $x + \mu \nabla F_*(s) = 0$ . Notice that at least for the canonical barrier functions these two conditions are equivalent and hence being on the dual central path implies being on the primal central path and viceversa.

To simplify the calculations we can scale these vectors by  $\frac{1}{\mu}$ , thus we have that  $d_{\mu}(x,s)=0$  if  $\frac{s}{\mu}+\nabla F(x)=0 \iff \frac{x}{\mu}+\nabla F_*(s)=0$ .

Finally we define the distance function as the norm of these vectors, and since we are free to choose what norm to use we define a norm respect to x and a norm with respect to s, such that:

$$d_{\mu}(x,s) = \left\| \frac{s}{\mu} + \nabla F(x) \right\|_{x} = \left\| \frac{x}{\mu} + \nabla F_{*}(s) \right\|_{s}.$$

The norm  $\|a\|_b$  is defined as  $\|a\|_b = \sqrt{\langle (\nabla^2 F(b))^{-1} a, a \rangle}$  where  $\nabla^2 F(b)$  represents the Hessian matrix.

#### 7.1 Distance Function for LP

To compute the Hessian matrix for LP, we plug in the expression for F(x) defined in (1).

$$\nabla F(x) = -x^{-1} = \begin{bmatrix} -\frac{1}{x_1} \\ \vdots \\ -\frac{1}{x_n} \end{bmatrix}.$$

Hence the matrix of second derivatives is,

$$\nabla^2 F(x) = \begin{bmatrix} \frac{1}{x_1^2} & \cdots & 0 \\ \vdots & \ddots & \vdots \\ 0 & \cdots & \frac{1}{x_n^2} \end{bmatrix}.$$

Finally since the Hessian matrix is a diagonal matrix we can calculate its inverse by taking the inverse of each element in its diagonal,

$$(\nabla^2 F(x))^{-1} = \left[ \begin{array}{ccc} x_1^2 & \cdots & 0 \\ \vdots & \ddots & \vdots \\ 0 & \cdots & x_n^2 \end{array} \right].$$

Therefore  $||a||_b = \sqrt{a^T \begin{bmatrix} b_1^2 & \cdots & 0 \\ \vdots & \ddots & \vdots \\ 0 & \cdots & b_n^2 \end{bmatrix}} a$ . We can now evaluate this norm on the vector  $\frac{s}{\mu} + x^{-1}$ 

$$\left\| \frac{s}{\mu} + x^{-1} \right\|_{x} = \sqrt{\sum_{j} x_{j}^{2} \left( \frac{s_{j}}{\mu} - \frac{1}{x_{j}} \right)^{2}} = \sqrt{\sum_{j} \left( \frac{x_{j} s_{j}}{\mu} - 1 \right)^{2}}.$$

The same computation can be performed for the dual, which will result in a similar expression.

#### Distance Function for SDP

Similarly, for SDP we have

$$\left\|\frac{1}{\mu}X - S^{-1}\right\|_{x} = \sqrt{Tr\left(\frac{1}{\mu}X^{\frac{1}{2}}SX^{\frac{1}{2}} - I\right)^{2}} = \sqrt{Tr\left(\frac{1}{\mu}S^{\frac{1}{2}}XS^{\frac{1}{2}} - I\right)^{2}} = \left\|\frac{1}{\mu}S - X^{-1}\right\|_{s}.$$

Here, the the last equality holds since Tr(AB) = Tr(BA) even if A and B do not commute.

We can also write this expression in the more compact (but less symmetric) form  $\sqrt{Tr(\frac{1}{u}SX-I)^2}$ 

Finally, the following lemma concerning this metric has been proved (and we will not go over the proof in this lecture).

**Lemma 3** If 
$$d_{\mu}(x,s) \leq 1$$
 then  $\langle x,s \rangle \leq 2\nu\mu$ .

The lemma suggests that if we keep a distance of at most 1 from the central path, as  $\mu \to 0$ , the duality gap will become 0 as well which means that we will reach the optimal solution.

#### 8 Follow the Central Path

Suppose that at iteration k we have some value  $\mu_k$  and  $x_k$ , which is close to  $x(\mu_k)$ ; we want to compute  $\mu_{k+1} < \mu_k$  and  $x_{k+1}$ , which should be close to  $x(\mu_{k+1})$ .

More concretely at iteration k we have  $x_k, s_k, y_k, \mu_k$  which are close to the central path, and we want to obtain values  $x_{k+1}, x_{k+1}, y_{k+1}, \mu_{k+1}$  which are still close to the central path.

There are several schemes to achieve this goal; one way is to focus on the primal program and on the conditions that we derived in Section 3:

$$Ax_{k+1} = b$$

$$A^*y_{k+1} + s_{k+1} = c$$

$$s_{k+1} + \mu_{k+1}\nabla F(x_{k+1}) = 0$$

Since we do not know the value of  $x_{k+1}$ , we can use the Taylor expansion on  $\nabla F(x_{k+1})$ :

$$\nabla F(x_{k+1}) \sim \nabla F(x_k) + (x_{k+1} - x_k) \nabla^2 F(x_k)$$

Now we have a system of linear equations on  $x_{k+1}$ . To solve the system, consider the following definitions:

$$\Delta x = x_{k+1} - x_k \tag{8}$$

$$\Delta y = y_{k+1} - y_k \tag{9}$$

$$\Delta s = s_{k+1} - s_k \tag{10}$$

One can prove that if at iteration k you are "close" to the central path (as defined by the distance function) there is a way to decrease  $\mu$  by a constant fraction and still remain "close" to the central path. This is formalized by the following theorem, which we will not prove in class.

**Theorem 4** If  $d_{\mu_k}(x_k, s_k) \leq 0.1$  and

$$\mu_{k+1} = \frac{\mu_k}{1 + \frac{0.1}{\sqrt{\nu}}}$$

then  $d_{\mu_k+1}(x_{k+1}, s_{k+1}) \leq 0.1$ .

The method described so far is referred to as **primal path following** since we considered the conditions of  $x(\mu_k)$  as defined by the primal, but we could have done the same thing on the dual which leads to a different set of linearized equations.

#### 9 Number of Iterations

We require  $\sqrt{\nu}$  iterations to decrease  $\mu$  by a constant factor, and  $\mu$  is equal to the duality gap. Therefore decreasing the duality gap to some constant  $\varepsilon$  starting from  $x_0, y_0, s_0$  requires  $O(\sqrt{\nu} \log \frac{\langle x_0, s_0 \rangle}{\varepsilon})$  iterations.

It is interesting to observe that SDP with  $n^2$  variables requires the same number of iterations as LP with n variables. However the resulting system of linear equations that need to be solved per iteration for SDP involves  $n^2$  variables as opposed to n variables as in the case of LP.

### 10 How Do We Start?

Let us assume that we have a point x that is inside the primal and inside the dual, but it could be very far away from the central path. This point is not suitable to start the algorithm since we need to be close to the central path to be guaranteed to stay close to the central path.

However, there is a nice trick that works when the region is bounded; here we will sketch the informal intuition behind it. Observe that as  $\mu \to \infty$  the position of the point  $x(\mu)$  does not depend on the objective function. This means that the central paths of all objective functions can be traced back to a common "origin".

Figure 2: Tracing back from a path that starts at x, jumping to the "correct" central path and starting the algorithm from there.

There is a continuum of central paths and it is easy to find the one that passes through x. Then we can trace this path back towards  $\mu = \infty$  until we are close enough to the desired central path. Next, we can follow the desired central path described by the objective function of interest and start the algorithm from there. Figure 2 illustrates this procedure.

For more information regarding interior-point methods for conic programming and its special cases, the reader is referred to the references below.

## References

- [1] A.S. Nemirovski, Lectures notes on Modern Convex Optimization, 2005. Available at http://www2.isye.gatech.edu/~nemirovs/Lect\_ModConvOpt.pdf.
- [2] A.S. Nemirovski and M.J. Todd, "Interior-point methods for optimization", Acta Numerica 17 (2008), 191–234.
- [3] J. Renegar, "A mathematical view of interior-point methods in convex optimization", SIAM, 2001.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### Lecture 16: Approximation Algorithms

Michel X. Goemans

## 1 Approximation Algorithms

Many optimizations problems arising in practice are NP hard. Under the widely accepted conjecture that  $P \neq NP$ , we cannot compute efficiently and exactly an optimal solution for all possible instances of these problems. Several approaches have been used to deal with this intractability. On one hand, dynamic programming, branch and bound, and implicit enumeration algorithms always find an optimal solution by navigating the space of feasible solutions in a more efficient way than an exhaustive search, but their running time is not guaranteed to be polynomial in the input's size. On the other hand, heuristic algorithms provide a sub-optimal solution to the problem, but their running time is polynomial in the size of the input problem. In this lecture we will focus on approximation algorithms, which are heuristics that always find a solution whose objective value is guaranteed to be within a certain factor of the optimum solution.

**Definition 1 (Approximation Algorithm)** Let  $\mathcal{P}$  be a minimization (resp. maximization) problem with instances  $I \in \mathcal{I}$ . An  $\alpha$ -approximation factor for  $\alpha \geq 1$  (resp.  $\alpha \leq 1$ ) algorithm for  $\mathcal{P}$  is an algorithm  $\mathcal{A}$  whose running time is polynomial in the size of the given instance I, and outputs a feasible solution of cost  $c_A$  such that  $c_A \leq \alpha \cdot OPT_I$  (resp.  $c_A \geq \alpha \cdot OPT_I$ ), where  $OPT_I$  is the cost of the optimal solution for instance I.

In this lecture, we will discuss three general techniques of designing approximation algorithms for NP-hard problems:

- 1. Using optimal value in the analysis without explicitly knowing it.
- 2. Linear programming relaxation and rounding.
- 3. Primal-dual technique.

# 2 A 3/2-Approximation Algorithm for the Metric TSP

The Traveling Salesman Problem is one of the most extensively studied problems in combinatorial optimization. In the metric version of the problem, an instance is a complete undirected graph G=(V,E) and  $c:E\to\mathbb{R}_+$ , where c satisfies the metric property: c(u,v)=c(v,u) for all  $u,v\in V$ , and the triangle inequality,  $c(u,v)\leq c(u,w)+c(w,v)$ , for all  $u,v,w\in V$ . The objective is to find tour, that is a cycle visiting every vertex exactly once (also called a *tour*) minimum cost.

A  $\frac{3}{2}$  approximation algorithm for this problem by Christofides [1] is as follows.

- 1. Find a minimum spanning tree T of G.
- 2. Compute a minimum cost perfect matching M on the set of odd-degree vertices  $V_{odd} \subseteq T$ .
- 3. Find an Eulerian tour C' (a cycle visiting all the edges exactly once) in  $M \cup T$ .
- 4. Output the tour C that visits the vertices of G in the order of their first appearance in the C'.

Figure 1: Execution of Christofides' algorithm on an instance. The first figure shows a minimum cost spanning tree. The second figure shows the addition of a minimum cost matching on odd degree vertices in the tree, and the third figure shows a cycle obtained after "shortcutting" an Eulerian tour in the previous graph, starting from vertex 1.

**Theorem 1** The above algorithm is a 3/2-approximation algorithm for the metric TSP.

**Proof:** It is clear that all steps in the algorithm can be implemented in polynomial time. The minimum spanning tree can be found using a greedy algorithm, and the minimum cost matching for  $V_{odd}$  can be found in polynomial time using the ellipsoid algorithm, as discussed in one of the previous lectures (or by a purely combinatorial algorithm also based on the linear program we discussed). Note that  $c(T) \leq OPT$ , because the optimal tour without an edge becomes a tree. Also,  $c(M) \leq OPT/2$ . To see this, consider any optimal tour, and then short-cut it to get a cycle visiting only vertices in  $V_{odd}$  with cost at most OPT. Since the cycle induces two matchings consisting of alternating edges, at least one of them will have cost at most OPT/2. From this, the total cost of the Eulerian cycle, an upper bound of the cost of the algorithm, is at most  $OPT + OPT/2 = 3/2 \cdot OPT$ .

Note that in the analysis of the algorithm, we used the value of OPT even without explicitly computing it exactly, or getting a lower bound on it. Figure 1 shows an instance of the metric TSP, and the execution of the algorithm on this instance.

A few remarks:

- The above analysis for the algorithm is tight, i.e.  $\forall \varepsilon > 0$  there is an instance I such that the algorithm returns a solution which is  $3/2 \varepsilon$  times the optimal solution.
- $\bullet$  Currently, no algorithm with an approximation factor better than 3/2 is known for metric TSP.
- TSP is known to be MAX-SNP hard [5] even for the case when distances are either 1 or 2. Also, Papadimitriou and Vempala [4] have proved that a 1.01 approximation algorithm for the metric TSP will imply P = NP.

# 3 Designing Approximation Algorithms via Relaxations

One of the most important paradigms in the design of approximation algorithms are relaxations. Consider the following (hard) minimization problem.

 $\min f(x)$ <br/>s.t.  $x \in S$ .

One approach to solve this problem is to extend S to a bigger set  $P \supset S$  where the same problem is easier to solve. Namely, we extend the function f to a function  $g:P\to\mathbb{R}$  satisfying g(x)= $f(x), \forall x \in S \text{ (or } g(x) \leq f(x)).$  If this condition holds, then

$$\min_{x \in S} f(x) \ge \min_{x \in P} g(x),$$

which gives a lower bound for the value of the optimal solution. Therefore, if an algorithm gives a solution  $x^* \in S$  which satisfies  $f(x^*) \leq \alpha \min_{x \in P} g(x)$ , then this is an  $\alpha$ - approximation algorithm for the problem.

For example, many combinatorial optimization problems can be expressed as

$$\min c^T x$$
s.t.  $Ax = b$ ,
$$x \in \{0,1\}^n$$
.

A natural relaxation is to replace the integrality constraint  $x_i \in \{0,1\}$  by the linear constraint  $0 \le x_i \le 1$ , we obtain the *LP relaxation* of the integer program above.

$$\min c^T x$$
s.t.  $Ax = b$ ,
$$0 \le x_i \le 1, \quad \forall i = 1, \dots, n.$$

In some cases, the polytope corresponding to the LP relaxation has all integral extreme points. In such cases, it is sufficient to solve the LP relaxation to solve the original problem exactly. But this is not true in general.

#### LP Relaxation for the Vertex Cover Problem 3.1

Given an undirected graph G = (V, E), a vertex cover of G is a collection of vertices  $C \subset V$  such that all edges e = (u, v) in E satisfy  $C \cap \{u, v\} \neq \emptyset$ . The Vertex Cover problem on an instance  $G = (V, E), c : E \to \mathbb{R}^+$  is to find a cover C of G of minimum cost  $c(C) = \sum_{v \in C} c(v)$ . This is known to be an NP-hard problem.

A natural formulation using integer variables and linear constraints is the following. We define a variable  $x_u \in \{0,1\}$  which takes value 1 if it is in the vertex cover, 0 otherwise. Then the following is an integer programming formulation for the vertex cover problem.

$$\min \sum_{v \in V} c_v x_v$$
s.t.  $x_u + x_v \ge 1$ ,  $\forall (u, v) \in E$ , (1b)

s.t. 
$$x_u + x_v > 1$$
,  $\forall (u, v) \in E$ , (1b)

$$x_u \in \{0,1\}, \quad \forall u \in V. \tag{1c}$$

The LP relaxation for the vertex cover problem is

$$\min \sum_{v \in V} c_v x_v$$

$$\text{s.t.} \quad x_u + x_v \ge 1, \quad \forall (u, v) \in E,$$

$$(2a)$$

s.t. 
$$x_u + x_v \ge 1$$
,  $\forall (u, v) \in E$ , (2b)

$$x_u \geq 0, \quad \forall u \in V.$$
 (2c)

Note that we removed the  $x_u \leq 1$  constraints, since if  $x_u > 1$  we can change it to  $x_u = 1$  without increasing the cost, and still have a feasible solution.

Figure 2: An example where the LP relaxation for the Vertex Cover does not have an integer optimal solution.

The LP relaxation does not necessarily have an optimal integral solution in general. For example, consider the graph given in Figure 3.1 with all costs equal to 1. The optimal solution for this instance has cost OPT=2, but the optimal solution for the LP relaxation has cost LP=3/2, as shown in the figure. What this example shows is not only that LP < OPT in general, but also an interesting fact about the strength of this relaxation. Suppose that we are going to use LP as a lower bound on OPT in order to prove an approximation guarantee. As we will see in the next subsection, we will be able to find a cover C with cost at most 2LP. Therefore, we can say

$$c(C) \le 2LP \le 2OPT$$

to prove an approximation guarantee of 2, However, the example proves that we will not be able to decrease this factor beyond 4/3. This follows from the fact that

$$OPT \le c(C) \le \alpha LP \le \alpha OPT \Rightarrow OPT/LP \le \alpha$$

then the best we can hope for is at most 4/3 by using this relaxation. This important property of the "bad examples" is captured in the concept of integrality gap.

**Definition 2 (Integrality gap)** Given a relaxation  $LP(\Pi)$  for an integer program  $IP(\Pi)$  that formulates a combinatorial (minimization) optimization problem on a collection of instances  $\{\Pi\}$ , the integrality gap of the linear program relaxation is the largest ratio between the optimal solution of both formulations, namely:

Integrality 
$$gap = \sup_{\Pi} \frac{IP(\Pi)}{LP(\Pi)}$$

For the Vertex Cover LP relaxation, the integrality gap is exactly 2. To see that it is at least 2, consider the complete graph  $G = K_n$ , with unitary costs. The minimum vertex cover has cost n-1, while the linear program relaxation can assign 1/2 to all variables, which gives a total cost of n/2. Therefore, the integrality gap is at least  $\frac{2(n-1)}{n} \to 2$ . The upper bound follows from the 2-approximation algorithm we will see in the next subsection.

#### 3.2 A 2-approximation Algorithm for Vertex Cover

A natural approach to get an integral solution from a fractional solution is to round the fractional values. A simple rounding scheme for the vertex cover is as follows.

1. Solve the linear programming relaxation given by (2a)-(2c), to get the fractional solution  $x^*$ .

2. Compute the vertex cover as  $C = \{v \in V, x_v^* \ge 1/2\}$  (i.e., round each fractional variable to the nearest integer).

**Theorem 2** The above rounding scheme is a 2-approximation algorithm for the Vertex Cover problem.

**Proof:** First, we need to check that C is indeed a vertex cover. For each  $e = (u, v) \in E$ ,  $x_u^* + x_v^* \ge 1$ , so at least one of  $x_u^*$ ,  $x_v^*$  has value at least 1/2, and is in C. Next, the cost of this vertex cover satisfies

$$c(C) = \sum_{v:x_v^* > 1/2} c_v \le 2 \sum_{v \in V} c_v x_v^* = 2LP \le 2OPT,$$

hence the LP rounding is a 2-approximation algorithm for the vertex cover problem.

This is a very basic (the simplest) example of rounding; more sophisticated rounding procedures have been used to design approximation algorithms; we'll see some in coming lectures.

### 4 The Primal Dual Technique

Yet another way of designing approximation algorithms for intractable problems is the primal dual method. The basic idea of the primal dual scheme is this: At every point of the algorithm, we keep a feasible dual solution, and a corresponding infeasible integer primal solution. The dual variables are then modified at every step and so is the infeasible primal solution, so as to achieve primal feasibility. At this point, the dual gives a lower bound (for minimization problems) on the optimal primal objective function value, which is used to derive the approximation factor for the algorithm. The interesting thing about this technique is that we do not need to explicitly solve the linear program (as is the case in rounding); the linear program is used only in the analysis of the algorithm.

We illustrate this method for the vertex cover problem. The linear program for the vertex cover problem is given by (2a)-(2c). The dual of this linear program is given by

$$\max \sum_{e \in E} y_e$$
s.t. 
$$\sum_{e \in \delta(v)} y_e \leq c_v \quad \forall v \in V,$$

$$y_e \geq 0 \quad \forall e \in E.$$
(3)

The primal dual algorithm for the vertex cover problem is as follows. In the algorithm, C corresponds to the set of vertices in the (supposed to be) vertex cover, and F is the set of edges in the graph not yet covered by C.

- 1.  $y(v) \leftarrow 0 \quad \forall v \in V, \quad C \leftarrow \emptyset, \quad F \leftarrow E.$
- 2. While  $F \neq \emptyset$
- 3. Let e = (u, v) be any edge in F.
- 4. Increase  $y_e$  until the constraint (3) becomes tight for u or v.
- 5. Add that corresponding vertex (say it is v) to C.
- 6.  $F \leftarrow F \setminus \delta(v)$ .

**Theorem 3** The above algorithm achieves an approximation ratio of 2 for the vertex cover problem.

Figure 3: Illustration of the primal-dual algorithm for the vertex cover problem. The cost of the vertices are indicated next to each vertex. Dotted edge denotes the edge currently under consideration, thick edges denote those already covered by the current vertex cover. The vertices in the cover are shown as solid circles.

**Proof:** First of all, it is clear that the set C returned by the algorithm is a vertex cover. Let y be the dual solution returned. Observe that by construction, this solution is dual feasible (we maintain dual feasibility throughout the execution). Furthermore, for any  $v \in C$ , we have that  $c_v = \sum_{e \in \delta(v)} y_e$ . Let us now compute the cost of the vertex cover returned by the algorithm.

$$\sum_{v \in C} c_v = \sum_{v \in C} (\sum_{e \in \delta(v)} y_e) = \sum_{e \in E} \alpha_e y_e \le 2 \sum_{e \in E} y_e$$

$$\le 2LP$$

$$\le 2OPT, \tag{4a}$$

where  $\alpha_e = 2$ , for edge e = (u, v) if both  $u, v \in C$ , 1 otherwise. The inequality (4a) follows from weak duality, and inequality (4b) follows from the fact that the primal LP is a relaxation of the vertex cover problem.

Figure 3 illustrates the execution of the primal-dual algorithm on a graph. For this instance, the algorithm returns a vertex cover of cost 9, whereas the optimal solution in this instance has

cost 7 (corresponding to the two vertices on the diagonal edge). The lower bound given by the dual solution has value 3 + 1 + 1 = 5.

A few final remarks:

- Dinur and Safra [2] have proved that it is NP-hard to approximate to the vertex cover with a factor better than 1.36.
- Currently, there is no algorithm for the vertex cover problem which achieves an approximation ratio better than 2. So the two (simple!) algorithms presented here are, in fact, the present best known approximation algorithms for this problem.
- Khot and Regev [3] have proved that it is UGC-hard to approximate vertex cover within a factor  $2 \varepsilon$ , for any  $\varepsilon > 0$ .

## References

- [1] Christofides, N. (1976). Worst-case analysis of a new heuristic for the travelling salesman problem, Report 388, Graduate School of Industrial Administration, CMU.
- [2] Dinur, I. and S. Safra (2002). The importance of being biased. In *Proceedings of the 34th ACM Symposium on Theory of Computing*, pp. 33-42.
- [3] Khot, S. and O. Regev (2008). Vertex cover might be hard to approximate to within  $2 \varepsilon$ . Journal of Computer and System Sciences, 74:335-349.
- [4] Papadimitriou, C.H. and S. Vempala (2000). On the approximability of the travelling salesman problem. In Proceedings of the 32nd ACM Symposium on Theory of Computing, pp. 126-133.
- [5] Papadimitriou, C.H. and M. Yannakakis (1993). The travelling salesman problem with distances one and two. *Mathematics of Operations Research*, 18:1-11.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

| 18.415/6.854 | Advanced | Algorithms |
|--------------|----------|------------|
|--------------|----------|------------|

November 17, 2008

# Lecture 17

Lecturer: Michel X. Goemans

# 1 Introduction

We continue talking about approximation algorithms.

Last time, we discussed the design and analysis of approximation algorithms, and saw that there were two approaches to the analysis of such algorithms: we can try comparing the solution obtained by our algorithm to the (unknown) optimal solution directly (as we did for Christofides's algorithm for TSP), or, when that is not possible, we can compare our solution to a *relaxation* of the original problem.

We can also use a relaxation to *design* algorithms, even without solving the relaxed problem: we saw a simple primal-dual algorithm that used the LP relaxation of the Vertex Cover problem.

In this lecture, we shall examine further the primal-dual approach and also the design of approximation algorithms through local search, and illustrate these on the facility location problem.

# 2 The facility location problem

### 2.1 Problem statement

We are given a set F of facilities, and a set D of clients. Our goal is to open some facilities and assign clients to them so that each client is served by exactly one facility. We are given, for each  $i \in F$ , the cost  $f_i$  of opening facility i and the cost  $c_{ij}$  of assigning client j to facility i for each  $j \in D$ .

If we open a certain subset  $F' \subseteq F$  of facilities, the cost incurred is  $\sum_{i \in F'} f_i$ . Subsequently, we will assign each client to the nearest facility, incurring a cost  $\min_{i \in F'} c_{ij}$  for client j. Thus our problem can be stated as the following optimization problem:

$$\min_{F' \subseteq F} \left( \sum_{i \in F'} f_i + \sum_{j \in D} (\min_{i \in F'} c_{ij}) \right).$$

This problem arises naturally in many settings, where the facilities might be schools, warehouses, servers, and so on. It is possible to imagine additional constraints such as capacities on the facilities; we shall deal with the simplest case and assume no other constraints. We shall also assume that the costs are all nonnegative, and that the  $c_{ij}$ s are in fact metric costs — that they come from a metric on  $F \cup D$  where the distance between  $i \in F$  and  $j \in D$  is  $c_{ij}$ .

### 2.2 Current status

This problem is known to be NP-hard. Hence we seek to design approximation algorithms. The best algorithm known is a 1.5-approximation algorithm, due to Byrka [1]. This is close to the best possible, in the sense that the following "inapproximability" result is true: if there is a 1.463-approximation algorithm, then  $NP \subseteq DTIME(n^{\log \log n})$  (see [2]).

Since our focus in this lecture is on the techniques, we will see simpler approximation algorithms that illustrate the approaches, each of which gives only a 3-approximation.

# 3 The primal-dual approach

We shall follow the general outline behind primal-dual approaches to many problems:

- 1. Formulate the problem as an integer program,
- 2. Relax it to a linear program,
- 3. Look at the dual of the linear program,
- 4. Devise an algorithm that finds an integral primal-feasible solution and a dual-feasible solution,
- 5. Show that the solutions are within a small factor of each other, and hence of the optimum.

### 3.1 IP formulation

Let the variable  $y_i$  denote whether the facility i is opened, i.e.,

$$y_i = \begin{cases} 1 & \text{if facility } i \text{ is opened,} \\ 0 & \text{otherwise} \end{cases}$$
 for each  $i \in F$ .

Similarly, let  $x_{ij}$  denote whether the client j is assigned to facility i, i.e.,

$$x_{ij} = \begin{cases} 1 & \text{if client } j \text{ is assigned to } i, \\ 0 & \text{otherwise} \end{cases}$$
 for each  $i \in F$  and  $j \in D$ .

So we must have

$$y_i \in \{0, 1\} \text{ for all } i \in F. \tag{1}$$

and

$$x_{ij} \in \{0, 1\} \text{ for all } i \in F, j \in D.$$

Further, we have the condition that each client must be assigned to exactly one facility:

$$\sum_{i \in F} x_{ij} = 1 \tag{3}$$

and the condition that clients can be assigned only to facilities that are actually open, i.e. that  $x_{ij} = 1 \implies y_i = 1$ . One way of writing this as a linear relation is:

$$y_i - x_{ij} \ge 0 \tag{4}$$

Finally, the objective function (cost) is

$$\sum_{i \in F} f_i y_i + \sum_{i \in F} \sum_{j \in D} c_{ij} x_{ij}. \tag{5}$$

The problem of minimizing (5) subject to conditions (1) (2) (3) and (4), is an integer programming problem.

#### 3.2LP relaxation

The conditions (1) and (2) are not linear constraints, but we can try to relax them to constraints that are linear. We write, for (2), the condition

$$0 \le x_{ij} \tag{6}$$

(we do not have to write  $x_{ij} \leq 1$ , as that is already forced by (3)), and for (1), we write the condition

$$0 \le y_i \tag{7}$$

(as the cost is an increasing function of  $y_i$ , the minimization will make sure that  $y_i \leq 1$ , if at all possible). Thus we have the following linear program:

$$\min \left( \sum_{i \in F} f_i y_i + \sum_{i \in F} \sum_{j \in D} c_{ij} x_{ij} \right)$$
 (8)

s.t. 
$$\sum_{i \in F} x_{ij} = 1 \qquad \forall j \in D \qquad (9)$$
$$y_i - x_{ij} \ge 0 \qquad \forall i \in F, \forall j \in D \qquad (10)$$
$$x_{ij} \ge 0 \qquad \forall i \in F, \forall j \in D \qquad (11)$$
$$y_i \ge 0 \qquad \forall i \in F \qquad (12)$$

$$y_i - x_{ij} \ge 0$$
  $\forall i \in F, \forall j \in D$  (10)

$$x_{ij} \ge 0 \qquad \forall i \in F, \forall j \in D \tag{11}$$

$$y_i > 0 \qquad \forall i \in F \tag{12}$$

We cannot expect every vertex of this LP to be 0-1; there can exist instances for which the LP optimum does not correspond to any convex combination of valid facility location integral solutions.

Thus the LP does not give a solution directly. One way of using the LP would be to solve it and then round the solution to a valid facility location; this needs some care but can be used to derive an approximation algorithm for the facility location problem. Another possibility is to pursue the primal-dual approach which is what we shall now do.

#### 3.3LP dual

Let us look at the dual of the LP. Introducing dual variables  $v_i$  for the constraints (9) and  $w_{ij}$  for the constraints (10), we get the dual LP:

$$\max \sum_{j \in D} v_i \tag{13}$$

s.t. 
$$\sum_{i \in D} w_{ij} \le f_i$$
  $\forall i \in F$  (14)

$$-w_{ij} + v_j \le c_{ij} \qquad \forall i \in F, \forall j \in D$$

$$(15)$$

$$w_{ij} > 0 \qquad \forall i \in F, \forall j \in D$$
 (16)

At the optimal solutions to the primal and dual, the complementary slackness condition says that:

$$y_i > 0 \implies \sum_{j \in D} w_{ij} = f_i \tag{17}$$

$$x_{ij} > 0 \implies v_j - w_{ij} = c_{ij} \tag{18}$$

$$y_i - x_{ij} > 0 \implies w_{ij} = 0. \tag{19}$$

If we could find a primal feasible solution and a dual feasible solution that satisfied the complementary slackness conditions, and furthermore the primal solution was integral, then we would have solved the problem. But as we have seen, this is not possible in general, because there might not be an integer solution corresponding to the LP optimum.

We interpret the complementary slackness conditions as follows. Client j pays a charge  $v_j \geq c_{ij}$ , if assigned to i (the condition (18)). The surpluses  $w_{ij}$  pay for the cost of opening the facility (the condition (17)). We use this interpretation to guide our primal-dual algorithm.

### 3.4 Primal-dual algorithm for the facility location problem

We will maintain  $v_j$ 's and  $w_{ij}$ 's that always constitute a dual-feasible solution. Initially, set each  $v_i = 0$  and each  $w_{ij} = 0$ . Start increasing all the  $v_j$ 's at rate 1. We watch out for 3 possible events:

- 1. For some  $i, j, v_j$  reaches  $c_{ij}$ , so that (18) holds, and (15) is in danger of being violated: In this case, we start increasing  $w_{ij}$  at rate 1 as well, so that  $v_j w_{ij} = c_{ij}$  will continue to hold.
- 2. For some i,  $\sum_{j \in D} w_{ij}$  reaches  $f_i$  "facility i is paid for": In this case, we freeze (stop increasing) all the  $w_{ij}$ 's. We also freeze all the  $v_j$ 's for which  $w_{ij}$  was being increased, namely  $\{j: v_j > c_{ij}\}$ . Finally, we also freeze those  $w_{i'j}$  for which a  $v_j$  has been frozen now, because we no longer need to increase them.
- 3. For some  $i, j, v_j$  reaches  $c_{ij}$ , when i is already paid for: In this case, we cannot increase  $w_{ij}$  now, so we instead freeze  $v_j$ , and also freeze all the  $w_{i'j}$ .

We repeat this process until every  $v_j$  is frozen. The procedure we have described is often referred to as a 'dual ascent' procedure, we we have only increased dual variables.

Suppose we stop with the values  $(\bar{v}, \bar{w})$ . We always remain dual-feasible, so  $\sum_{j \in D} \bar{v}_j$  when we stop is a lower bound on the optimal value of the LP. We now have to decide how to convert the obtained values into a facility location, i.e. which facilities to open. We will only open a subset of the paid-for facilities.

Say facility i is paid for at time  $t_i$ . When we terminate, create the graph  $G = (F \cup D, E)$  where  $E = \{(i, j), \bar{w}_{ij} > 0\}$ . Define cluster(i) as the set of all facilities that are neighbors of neighbors of i in this graph.

Process the paid-for facilities in nondecreasing order of  $t_i$ . First, consider the first paid-for facility, i.e. i for which  $t_i$  is minimum, and open it. We will not open any other facility in cluster(i). In general, open facility i' if it is not already in the cluster of a previously *opened* facility, i.e. iff  $i' \notin \bigcup_i \text{cluster}(i)$  where the union is over previously opened facilities i.

Having selected which facilities to open, we assign clients to facilities the natural way: assign each client to the nearest facility.

We now prove that this algorithm gives a 3-approximation algorithm.

### 3.5 Analysis of the algorithm

**Claim 1** Let O and A be the opening-cost and assigning-cost of the (primal) solution constructed by the algorithm. Then,

$$3O + A \le 3\sum_{i \in D} \bar{v}_i.$$

**Proof:** Let U be the set of facilities opened by the algorithm, and  $\sigma(j) \in U$  be the facility that the client j is assigned to. We need to show that

$$3\sum_{i\in U} f_i + \sum_{j\in D} c_{\sigma(j)j} \le 3\sum_{i\in D} \bar{v}_j.$$

For each client j, there are two possible scenarios:

Figure 1: Case (II). If i makes  $v_j$  stop increasing via the third event from Section 3.4, there is no edge between i and j in G. Otherwise,  $(i, j) \in G$ .

- (I) j has exactly one open facility, say  $i = \sigma(j)$ , in its neighborhood in G.
- (II) j has no open facility in its neighborhood in G.

First consider case (I). Since  $\bar{w}_{ij} > 0$  from the way we construct G, the algorithm freezes variables  $\bar{v}_j, \bar{w}_{ij}$  after tightening the equation  $c_{ij} = \bar{v}_j - \bar{w}_{ij}$ . Thus, we have  $c_{ij} + \bar{w}_{ij} = \bar{v}_j$ , and so

$$c_{ij} + 3\bar{w}_{ij} \le 3(c_{ij} + \bar{w}_{ij}) = 3\bar{v}_j. \tag{20}$$

If we take the summation of (20) over those clients in case (I), we obtain from  $\sum_{i} 3\bar{w}_{ij} = 3f_i$  that

$$\sum_{j \in D: \text{case (I)}} c_{\sigma(j)j} + 3 \sum_{i \in U} f_i \le 3 \sum_{j \in D: \text{case (I)}} \bar{v}_j.$$

Thus, the opening of all facilities is already accounted for.

Now consider case (II) where j contributes nothing for constructing facilities. Hence for completing the proof, it is enough to show that the assigning-cost for j is at most  $3\bar{v}_j$  i.e. there exists a facility  $i' \in U$  such that  $c_{i'j} \leq 3\bar{v}_j$ .

Let i be the facility that makes  $v_i$  stop to increase, for which it follows that

$$c_{ij} \le \bar{v}_j$$
 and  $t_i \le \bar{v}_j$ . (21)

In the case when  $i \in U$ , it follows obviously that  $c_{ij} \leq \bar{v}_j \leq 3\bar{v}_j$ . Hence assume  $i \notin U$ . Since i is not open (although i is fully paid for), there exists a facility  $i' \in U$  such that  $i \in \mathsf{cluster}(i')$ . Thus there exists a client j' which is connected to both i and i' in G. Since  $\bar{w}_{ij'} > 0$  and  $\bar{w}_{i'j'} > 0$ ,

$$c_{ij'} \le t_i \quad \text{and} \quad c_{i'j'} \le t_{i'}.$$
 (22)

From the triangle inequality, (21), (22) and  $t_{i'} \leq t_i \leq \bar{v}_j$  (since i was responsible for j freezing), we have

$$c_{i'j} \leq c_{i'j'} + c_{ij'} + c_{ij}$$

$$\leq t_{i'} + t_i + \bar{v}_j$$

$$\leq 2t_i + \bar{v}_j$$

$$\leq 3\bar{v}_j,$$

which completes the proof.

# 4 The local search based approach

Now we study a different type of approximation algorithm based on *local search*.

### 4.1 General paradigm

Suppose we want to minimize the objective function c(x) over the space S of feasible solutions. In the case of the facility problem, S is a subset of facilities and c(x) is the sum of the opening costs and the assigning costs. In a local search based algorithm, we have a neighborhood  $N: S \to 2^S$  which satisfies the following two conditions:

- $v \in N(v)$  for all  $v \in S$ ,
- there exists an efficient algorithm to decide whether  $c(v) = \min_{u \in N(v)} c(u)$  for a given v and, if not, find  $u \in N(v)$  such that c(u) < c(v).

Using this algorithm for searching the neighborhood, the algorithm travels in the space S iteratively finding a better solution in N(v) than the current solution  $v \in S$ . It terminates when the current solution v cannot be improved i.e. v is a locally optimal solution. In a local search based algorithm, one also needs an algorithm for finding an initial feasible solution.

We can raise some issues related to the design and analysis of local search algorithms:

 $Q_0$ : What neighborhood N should we choose?

- If |N(v)| is large, one can find a better local solution in each iteration but designing an algorithm to efficiently search the neighborhood might be more difficult.

 $Q_1$ : How good is a locally optimal solution which the algorithm provides?

- This decides the approximation ratio of the algorithm.

 $Q_2$ : How many iterations does the algorithm require before finding a local optimum?

- Using the local search algorithm is one way to find a local optimum; there might be some more direct way, and the complexity of finding a local optimum has been studied (see the discussion about the class PLS in next lecture).

Consider the Traveling Salesman problem. One possible neighborhood N arises from 2-exchange where  $u \in N(v)$  if the tour u can be obtained by removing two edges in v and replacing these with two different edges that reconnect the tour. Therefore,  $|N(v)| = \binom{n}{2}$ , hence it is enough to check only  $O(n^2)$  solutions to find a better solution in N(v). Other neighborhoods can also be defined, such as for example k-exchange in which k edges are replaced. In the problem set, a neighborhood of exponential size is considered.

### 4.2 Local search algorithm for the facility location problem

Now we explain a local search based approximation algorithm for the facility location problem. The set U of open facilities is enough for describing any solution in our solution space S since, after the open facilities are decided, the optimal assignment follows easily (and efficiently). The simplest neighborhood one can consider is to simply allow the addition of a new facility, the deletion of an open facility, or replacing one open facility by another. More formally, N(U) is designed as follows:  $U' \in N(U)$  if  $U' = U \cup \{i\}$ ,  $U' = U \setminus \{i'\}$ , or  $U' = U \cup \{i\} \setminus \{i'\}$  for some facilities i and i'. Note that  $|N(U)| = O(n^2)$  which settles the time-complexity issue for finding a better solution in N(U). The following claim settles  $Q_1$ . We will examine  $Q_2$  in the next lecture, albeit not for the facility location problem  $per\ se$ .

Claim 2 Consider a locally optimal solution v for the above neighborhood N. Then, its opening cost O and assigning cost A satisfy

$$A \le A^* + O^* \tag{23}$$

$$O \le O^* + 2A^*,\tag{24}$$

where  $O^*$  and  $A^*$  are the opening cost and the assigning cost of the optimal solution respectively.

Remark 1 Claim 2 quarantees an approximation ratio of 3 for this local-search algorithm since

$$A + O \le 3A^* + 2O^* \le 3(A^* + O^*) = 3OPT^*.$$

**Proof:** In this lecture, we will see only the proof of (23) due to time constraints. (The proof of (24) would take longer than the 5 minutes available at this point.) Let U and  $U^*$  be the sets of open facilities in locally and globally optimal solutions respectively. For a facility  $i \in U^* \setminus U$ , the local optimality of U implies

$$f_i + \sum_{j:\sigma^*(j)=i} \left( c_{\sigma^*(j)j} - c_{\sigma(j)j} \right) \ge 0,$$

where  $\sigma(j)$  and  $\sigma^*(j)$  are the open facilities which j is assigned to in U and in  $U^*$  respectively (since we could just reassign just the clients for which  $\sigma^(j)$  is i). By taking the summation over all  $i \in U^* \setminus U$ , it follows that

$$O^* + A^* - A \ge 0.$$

Now consider the time-complexity issue  $Q_2$ . There exist instances for which this algorithm will take an exponential number of steps. In fact, the negative result for this issue comes from the fact that the facility location problem (with this definition of the neighborhood) is PLS-complete [3], see next lecture for more details. Furthermore, it is unlikely that any algorithm (not necessarily based on this iterative local search process) can find a locally optimal solution in polynomial time in the worst case. However, if the algorithm walks to a better solution only when it improves the current solution significantly by  $\varepsilon$  factor, it can be guaranteed that the algorithm terminates in polytime with respect to n and  $\varepsilon$ . Furthermore, one can obtain the  $\varepsilon$ -version of Claim 4.2, which leads to  $(3 + \varepsilon')$ -approximation ratio of the algorithm.

# References

- [1] Jaroslaw Byrka. An optimal bifactor approximation algorithm for the metric uncapacitated facility location problem. *Proceedings of APPROX 2007*, 2007.
- [2] Sudipto Guha and Samir Khuller. Greedy strikes back: Improved facility location algorithms. In *Journal of Algorithms*, pages 649–657, 1998.
- [3] Y. Kochetov and D. Ivanenko. Computationally Difficult Instances for the Uncapacitated Facility Location Problem, volume 32. Springer US, 2005.

17-7

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### 18.415/6.854 Advanced Algorithms

November 19, 2008

## Approximaion Algorithms: MAXCUT

Lecturer: Michel X. Goemans

# 1 MAX-CUT problem

**MAX-CUT Problem:** Given a graph G=(V,E) and weights on the edges  $w:E\to R^+$ , find a cut  $(S:\bar{S}),S\subseteq V$  that maximizes  $w(S:\bar{S})=\sum_{e\in(S:\bar{S})}w(e)$ .

**MIN-CUT Problem:** find a cut  $(S : \bar{S})$  that minimizes  $w(S : \bar{S})$ .

There is a polynomial algorithm for the MIN-CUT problem: use the min s-t cut algorithm on each pair of vertices (or, better, for a fixed s), and take the smallest of them. However, the MAX-CUT problem is NP-hard, and we'll try several ways of designing approximation algorithms for it

# 2 Idea #1: Local Search

**Algorithm:** Start from any cut  $(S : \bar{S})$ . Define the neighborhood  $N(S : \bar{S})$  of the cut to be the MOVE neighborhood: all the cuts that result from moving one vertex from one side of the cut to the other side. Consider a locally maximum cut for this neighborhood.

**Lemma 1** If  $(S:\bar{S})$  is a local maximum for the MOVE neighborhood, then  $w(S:\bar{S}) \geq \frac{1}{2}w(E) \geq \frac{1}{2}OPT$ .

**Proof of lemma 1:** Look at a vertex  $i \in V$ . Let  $C_i$  be the set of all edges  $(i,j) \in E$  that are part of the cut  $(S:\bar{S})$  (that is if  $i \in S$  then  $j \in \bar{S}$  and vice versa). Let  $A_i$  be the set of all edges  $(i,j) \in E$  that are **not** part of the cut  $(S:\bar{S})$ . Since moving any single vertex i to the other side of the cut does not improve the weight of the cut, we know that:

$$w(C_i) > w(A_i)$$
.

Summing over all vertices i, we get:

$$\sum_{i \in V} w(C_i) \ge \sum_{i \in V} w(A_i),$$

or  $2w(S:\bar{S}) \geq 2w(E\setminus (S:\bar{S}))$ . Rearranging, we get:

$$4w(S:\bar{S}) > 2w(E)$$

or

$$w(S:\bar{S}) \ge \frac{1}{2}w(E) \ge \frac{1}{2}OPT.$$

#### Remarks:

(a) The bound of 1/2 cannot be improved for this MOVE neighborhood: Consider a k-vertex cycle, where k is a multiple of 4, as the graph G (with unit weights). The best cut will include

all edges. However, if we start from a cut in which the edges of the cycle alternate in and out of the cut, we have a locally optimum solution with only k/2 edges in the cut.

- (b) The local search algorithm based on the MOVE neighborhood for MAX-CUT takes exponentially many steps in the worst-case. This is true even for graphs that are 4-regular (each vertex has exactly 4 neighbors) (Haken and Luby [1]). For 3-regular graphs the algorithm is polynomial (Poljak [4]).
- (c) To capture the complexity of local search, Johnson, Papadimitriou and Yannakakis [3] have defined the class PLS (Polynomial Local Search). Members of this class are optimization problems of the form  $\max\{f(x):x\in S\}$  together with a neighborhood  $N:S\to 2^S$ . We say that  $v \in S$  is a local optimum if  $c(v) = \max\{c(x) : x \in N(v)\}$ . To be in PLS, we need to have polynomial-time algorithms for (i) finding a feasible solution, (ii) deciding if a solution is feasible and if so computing its cost, and (iii) deciding if a better solution in the neighborhood N(v) of a solution v exists and if so finding one. They introduce a notion of reduction, and this leads to PLS-complete problems for which any problem in PLS can be reduced to it. Their notion of reduction implies that if, for one PLS-complete problem, one has a polynomial-time algorithm for finding a local optimum then the same true for all PLS problems. In particular, MAX-CUT with the MOVE neighborhood is PLS-complete [5]. Furthermore, it follows from Johnson et al. [3] that the obvious local search algorithm is not an efficient way of finding a local optimum for a PLS-complete problem; indeed, for any PLS-complete problem, there exist instances for which the local search algorithm of repeatedly finding an improved solution takes exponential time. The result of Haken and Luby above is thus just a special case. Still, this does not preclude other ways of finding a local optimum.

## 3 Idea #2: Random Cut

**Algorithm:** There are  $2^{|V|}$  possible cuts. Sample a cut randomly using a uniform distribution over all possible cuts in the graph:  $\forall v \in V$ ,  $Pr(v \in S) = \frac{1}{2}$ , independently for all vertices  $v \in V$ .

**Lemma 2** This randomized algorithm gives a cut with expected weight that is  $\geq \frac{1}{2}OPT$ .

Proof of lemma 2:

$$\begin{split} E[w(S:\bar{S})] &= E[\sum_{e\in E} w(e)I(e\in (S:\bar{S}))] = \sum_{e\in E} w(e)\cdot Pr(e\in (S:\bar{S})) \\ &= \sum_{e\in E} w(e)\cdot \frac{1}{2} = \frac{1}{2}w(E). \end{split}$$

Using the method of *conditional expectations*, we can transform this randomized algorithm into a deterministic algorithm. The basic idea is to use the following identity for a random variable f and event A:

$$\begin{split} E[f] &= E[f|A]Pr(A) + E[f|\bar{A}]Pr(\bar{A}) = E[f|A]Pr(A) + E[f|\bar{A}](1 - Pr(A)) \\ &\leq \max\{E[f|A], E[f|\bar{A}]\}. \end{split}$$

In our setting, we consider the vertices in a specific order, say  $v_1, v_2, \dots$ , and suppose we have already decided/conditioned on the position (i.e. whether or not they are in S) of  $v_1, \dots, v_{i-1}$ . Now, condition on whether  $v_i \in S$ . Letting  $f = w(S : \bar{S})$ , we get:

$$E[f|\{v_1, \dots, v_{i-1}\} \cap S = C_{i-1}] < \max(E[f|\{v_1, \dots, v_{i-1}\} \cap S = C_{i-1}, v_i \in S], E[f|\{v_1, \dots, v_{i-1}\} \cap S = C_{i-1}, v_i \notin S]).$$

Lec18-2

Both terms in the max can be easily computed and we can decide to put  $v_i$  on the side of the cut which gives the maximum, i.e. we set  $C_i$  to be either  $C_{i-1}$  or  $C_{i-1} \cup \{v_i\}$  in such a way that:

$$E[f|\{v_1,\cdots,v_{i-1}\}\cap S=C_{i-1}\leq E[f|\{v_1,\cdots,v_i\}\cap S=C_i].$$

When we have processed all inequalities, we get a cut  $(C_n : \bar{C}_n)$  such that

$$\frac{1}{2}w(E) \le E[f] \le w(C_n : \bar{C}_n),$$

and this provides a deterministic 0.5-approximation algorithm.

Examining this derandomized version more closely, we notice that we will place  $v_i$  on the side of the cut that maximizes the total weight between  $v_i$  and the previous vertices  $\{v_1, v_2, \cdots, v_{i-1}\}$ . This is therefore a simple greedy algorithm.

#### Remarks:

(a) The performance guarantee of the randomized algorithm is no better than 0.5; just consider the complete graph on n vertices with unit weights. Also, the performance guarantee of the greedy algorithm is no better than 0.5 int he worst-case.

# 4 Idea #3: LP relaxation

Algorithm: Start from an integer-LP formulation of the problem:

$$\max \sum_{e \in E} w(e)x_e$$

$$s.t. \qquad x_e \in \{0,1\} \ \forall e \in E$$

$$\sum_{e \in F} x_e + \sum_{e \in C \setminus F} (1 - x_e) \le |C| - 1 \ \forall cycle \ C \subseteq E \ \forall F \subseteq C, \ |F| \ odd$$

$$\Leftrightarrow \sum_{e \in F} x_e - \sum_{e \in C \setminus F} x_e \le |F| - 1 \ \forall cycle \ C \subseteq E \ \forall F \subseteq C, \ |F| \ odd$$

Since we have a variable  $x_e$  for each edge (if  $x_e = 1$  than  $e \in (S : \bar{S})$ ), we need the second type of constraints to guarantee that S is a legal cut. The validity of these constraints comes from the fact that any cycle and any cut must intersect in an even number of edges. even number of edges that are in the cut.

Next, we relax this integer program into a LP:

$$\max \sum_{e \in E} w(e)x_e$$

$$s.t. \quad 0 \le x_e \le 1 \quad \forall e \in E$$

$$\sum_{e \in F} x_e - \sum_{e \in C \setminus F} x_e \le |F| - 1 \quad \forall cycle \ C \subseteq E \ \forall F \subseteq C, \ |F| \ odd.$$

This is a relaxation of the maximum cut problem, and thus provides an upper bound on the value of the optimum cut. We could try to solve this linear program and devise a scheme to "round" the possibly fractional solution to a cut.

#### Remarks:

- (a) This LP can be solved in a polynomial time. One possibility is to use the ellipsoid algorithm as the separation problem over these inequalities can be solved in polynomial time (this is not trivial). Another possibility is to view the feasible region of the above linear program as the projection of a polyhedral set  $Q \subseteq \mathbb{R}^{n^2}$  with  $O(n^3)$  number of constraints; again, this is not obvious.
- (b) If the graph G is planar, then all extreme points of this linear program are integral and correspond to cuts. We can therefore find the maximum cut in a planar graph in polynomial time (there is also a simpler algorithm working on the planar dual of the graph).
- (c) There exist instances for which  $\frac{OPT}{LP} \sim \frac{1}{2}$  (or  $\exists G = (V, E), \ w(e) = 1, OPT \leq n(\frac{1}{2} + \epsilon), \ LP \geq n(1 \epsilon)$ ), which means that any rounding algorithm we could come up with will not guarantee a factor better than  $\frac{1}{2}$ .

## 5 Idea #4: SDP relaxation

The idea is to use semidefinite programming to get a more useful relaxation of the maximum cut problem. This is due to Goemans and Williamson [2].

Instead of defining variables on the edges as we did in the previous section, let's use variables on the vertices to denote which side of the cut a given vertex is. This leads to the following quadratic integer formulation of the maximum cut problem:

$$\max \sum_{(i,j)\in E} w(i,j) \frac{1 - y_i y_j}{2}$$

$$s.t. \quad y_i \in \{1, -1\}^n \ \forall i \in V.$$

Here we have defined a variable  $y_i$  for each vertex  $i \in V$  such that  $y_i = 1$  if  $i \in S$  and  $y_i = -1$  otherwise. We know that an edge (i, j) is in the cut  $(S : \bar{S})$  iff  $y_i y_j = -1$ , and this explains the quadratic term in the objective function.

We can rewrite the objective function in a slightly more convenient way using the Laplacian of the graph. The Laplacian matrix L is defined as follows:

$$l_{ij} = \begin{cases} 0 & (i,j) \notin E \\ -w(i,j) & i \neq j, (i,j) \in E \\ \sum_{k:k \neq i} w(i,k) & i = j. \end{cases}$$

that is, the off-diagonal elements are the minus the weights, and the diagonal elements correspond to the sum of the weights incident to the corresponding vertex. Using the Laplacian matrix, we can rewrite equivalently the objective function in the following way:

$$y^{T}Ly = \sum_{i=1}^{n} \sum_{j=1}^{n} y_{i}y_{j}l_{ij} = \sum_{i=1}^{n} y_{i}^{2} \sum_{k \neq i} w(i,k) - \sum_{(i,j) \in E} y_{i}y_{j}w(i,j)$$
$$= 2w(E) - \sum_{(i,j) \in E} y_{i}y_{j}w(i,j) = 4\left(\sum_{(i,j) \in E} w(i,j)\frac{1 - y_{i}y_{j}}{2}\right),$$

and thus

$$\sum_{(i,j)\in E} w(i,j) \frac{1 - y_i y_j}{2} = \frac{1}{4} y^T L y.$$

Thus the maximum cut value is thus equal to

$$\max\{\frac{1}{4}y^TLY : y \in \{0,1\}^n\}.$$

If the optimization was over all  $y \in \mathbb{R}^n$  with  $||y||_2^2 = n$  then we would get that

$$\max\{\frac{1}{4}y^T L Y : y \in \mathbb{R}^n, ||y||^2 = n\} = \frac{n}{4}\lambda_{max}(L),$$

where  $\lambda_{max}(L)$  is the maximum eigenvalue of the matrix L. This shows that  $OPT \leq \frac{n}{4}\lambda_{max}(L)$ ; this is an eigenvalue bound introduced by Delorme and Poljak.

Using semidefinite programming, we will get a slightly better bound. Using the *Frobenius inner product*, we can again reformulate the objective function as:

$$\frac{1}{4}y^T L y = \frac{1}{4}L \bullet (yy^T),$$

or as

$$\frac{1}{4}L \bullet Y$$

if we define  $Y = yy^T$ . Observe that  $Y \succeq 0$ , Y has all 1's on its diagonal, and its rank is equal to 1. It is easy to see that the coverse is also true: if  $Y \succeq 0$ , rank(Y) = 1 and  $Y_{ii} = 1$  for all i then  $Y = yy^T$  where  $y \in \{-1, 1\}^n$ . Thus we can reformulate the problem as:

$$\begin{aligned} \max & \quad & \frac{1}{4}L \bullet Y \\ s.t. & \quad & rank(Y) = 1, \\ & \quad & \forall i \in V: \ Y_{ii} = 1, \\ & \quad & Y \succ 0. \end{aligned}$$

This is almost a semidefinite program except that the rank condition is not allowed. By removing the condition that rank(Y) = 1, we relax the problem to a semidefinite program, and we get the following SDP:

$$SDP = \max$$
  $\frac{1}{4}L \bullet Y$   $s.t.$   $\forall i \in V: Y_{ii} = 1,$   $Y \succ 0.$ 

Obviously, by removing the condition that rank(Y) = 1 we only increase the space on which we maximize, and therefore the value (simply denoted by SDP) to this semidefinite program is an upper bound on the solution to the maximum cut problem.

We can use the algorithms we described earlier in the class to solve this semidefinite program to an arbitrary precision. Either the ellipsoid algorithm, or the interior-point algorithms for conic programming. Remember that semidefinite programs were better behaved if they satisfied a regularity condition (e.g., they would satisfy strong duality). Our semidefinite programming relaxation of MAXCUT is particularly simple and indeed satisfies both the primal and dual regularity conditions:

(a) **Primal regularity conditions**  $\exists Y \succ 0 \text{ s.t. } Y_{ii} = 1 \ \forall i.$  This condition is obviously satisfied (consider Y = I).

(b) **Dual regularity condition:** First consider the dual problem -

$$\min \qquad \frac{1}{4} \sum_{i \in V} z_i$$

where  $z_i \in \mathbb{R}$  for all  $i \in V$ . The regulation condition is that there exist  $z_i$ 's such that  $\begin{pmatrix} z_1 & 0 & \dots & 0 \\ 0 & z_2 & \dots & 0 \\ \vdots & \vdots & \ddots & \vdots \\ 0 & 0 & z_i \end{pmatrix} - L \succ 0$ . This is for example satisfied if, for all  $i, z_i > \lambda_{max}(L)$ .

**Remark:** If we add the condition that  $z_1 = z_2 = ... = z_n$  to the dual then the smallest value  $z_i$  can take is equal to  $\lambda_{max}(L)$ , and we derive that:

$$OPT \le SDP \le \frac{n}{4} \lambda_{max}(L),$$

and therefore this SDP bound improves upon the eigenvalue bound. We will start the next lecture by proving the following theorem.

**Theorem 3 ([2])** For all  $w \ge 0$ , we have that  $\frac{OPT}{SDP} \ge 0.87856$ .

In order to prove this theorem, we will propose an algorithm which derives a cut from the solution to the semidefinite program. To describe this algorithm, we first need some preliminaries. From the Cholesky's decomposition, we know that:

$$Y \succeq 0 \iff \exists V \in R^{k \times n}, \ k = rank(Y) \leq n, \ s.t. \ Y = V^T V$$
  
$$\Leftrightarrow \exists v_1, ..., v_n \ s.t. \ Y_{ij} = v_i^T v_i, \ v_i \in \mathbb{R}^n.$$

Therefore, we can rewrite the SDP as a 'vector program':

$$\max \sum_{(i,j)\in E} w(i,j) \frac{1 - v_i^T v_j}{2}$$

$$s.t. \quad \forall i \in V: ||v_i|| = 1$$

$$\forall i \in V: v_i \in \mathbb{R}^n.$$

To be continued...

### References

- A. Haken and M. Luby, "Steepest descent can take exponential time for symmetric connection networks", Complex Systems, 1988.
- [2] M.X. Goemans and D.P. Williamson, Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming, J. ACM, 42, 1115–1145, 1995.
- [3] D.S. Johnson, C.H. Papadimitriou and M. Yannakakis, "How easy is local search", *Journal of Computer and System Sciences*, **37**, 79–100, 1988.

- [4] S. Poljak, "Integer Linear Programs and Local Search for Max-Cut", SIAM J. on Computing, 24, 1995, pp. 822-839.
- [5] A.A. Schäffer and M. Yannakakis, "Simple local search problems that are hard to solve", SIAM Journal on Computing,  ${\bf 20},\ 56-87,\ 1991.$

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### Lecture 19

Lecturer: Michel X. Goemans

### 1 Introduction

In this lecture, we revisit MAXCUT and describe a  $randomized \ \gamma \ (\approx .87856)$ -approximation algorithm. We also explore SPARSEST-CUT, an NP-hard problem for which no constant factor approximation is known. We begin to describe an  $O(\log k)$  approximation using multicommodity flows; here k is the number of commodities. To define the relationship between the optimal values of SPARSEST-CUT and multicommodity flow, we introduce metrics and finite metric spaces.

# 2 Revisiting MAXCUT

Recall the MAXCUT problem: given a graph G = (V, E) and weights  $w: E \to \mathbb{R}_+$  (we could assume that G is the complete graph and weights are 0 for the original non-edges), maximize  $w(S: \bar{S})$  (=  $\sum_{i \in \bar{S} \atop i \in \bar{S}} w_{ij}$ ) in  $S \subset V$ . MAXCUT can be formulated as the integer program

$$\max \sum_{(i,j)\in E} w_{ij} (1 - x_i x_j)/2$$

subject to

$$x_i \in \{\pm 1\}, \forall i.$$

The prior lecture described a 1/2-approximation algorithm and an upper bound on the solution to the above optimization, via reduction to a semidefinite program.

#### 2.1 SDP Relaxation of MAXCUT

In the SDP relaxation, we replaced the  $x_i$  with unit vectors in the sphere  $S^{n-1} := \{x \in \mathbb{R}^n : ||x|| = 1\}$ . Thus, the goal of the relaxed MAXCUT was to find

$$\max \sum_{(i,j) \in E} w_{ij} (1 - v_i^T v_j) / 2$$

subject to

$$v_i \in S^{n-1}, \forall i.$$

Though it is not immediately clear that this represents a semidefinite program, it can be reformulated as follows:

$$\max \sum_{(i,j)} w_{ij} (1 - Y_{ij})/2,$$

subject to

$$Y_{ii} = 1, \forall i$$

$$Y \succ 0$$
.

Figure 1: For the 5-cycle, the optimum vectors end up being in a lower-dimensional space (of dimension 2), see left figure. The angle between any two consecutive vectors is  $4\pi/5$  and total SDP value is  $5(1 - \cos(4\pi/5))/2 = 4.52 \cdots$ . Taking a random hyperplane through the origin gives the cut  $(S : \bar{S})$ , see the right figure.

Given a solution to the SDP in the form of unit vectors  $v_i$ , we would like to find a feasible S giving as large a cut as possible. The ideal is to have vertices i and j separated by the cut when  $(1 - v_i^T v_j)/2$  is large, i.e.,  $v_i$  and  $v_j$  are far apart on the sphere. Here is a way to do this. Choosing a hyperplane through the origin divides the vectors into two groups, and we let S be the intersection of one halfspace with the set of vectors. The sets of vectors on each side of the hyperplane correspond to S and S. As an example, we illustrate the vectors for a cycle of length 5 in Figure 1.

Which hyperplane should we choose? Well, the optimum vectors are definitely not unique; any rotation of them (orthonormal transformation) will also provide an optimum solution since the objective function depends only on the inner products  $(v_i^T v_j)$ . Therefore we should not have a preferred direction for the hyperplane.

# 3 MAXCUT $\gamma$ -Approximation Algorithm

This discussion provides the intuition behind the following randomized algorithm, due to Goemans and Williamson ([1]):

- 1. Choose a unit vector  $r \in S^{n-1}$  uniformly.
- 2. Let  $S = \{i \in V : r^T v_i > 0\}.$

**Remark 1** In the case n=2, it is easy to pick a uniform r, by taking  $\theta \in [0,2\pi)$  uniformly, whence  $r=(\cos\theta,\sin\theta)^T$ . For a general n, we should find  $r\in S^{n-1}$  by selecting each component independently from a Gaussian distribution, and then normalize to ||r||=1.

**Theorem 1** The Goemans-Williamson algorithm is a randomized  $\gamma$ -approximation algorithm for MAXCUT, where  $\gamma = \min_{-1 \le x \le 1} \frac{2 \cos^{-1} x}{\pi (1-x)} (\approx .87856)$ .

**Proof:** "OPT" and "SDP" will denote the optimal solution to the MAXCUT instance and its SDP relaxation. We show  $E[w(S:\bar{S})] \ge \gamma \cdot \text{SDP} \ge \gamma \cdot \text{OPT}$ .

By linearity of expectations, we have:

$$E[w(S:\bar{S})] = E[\sum_{(i,j)} w_{ij} \{1 \ if \ (i,j) \in (S:\bar{S}); \ 0 \ otherwise\}]$$
$$= \sum_{(i,j)} w_{ij} Pr[(i,j) \in (S:\bar{S})].$$

If we were in dimension 2 then  $v_i$  and  $v_j$  are separated by the line orthogonal to r if and only if this line falls between  $v_i$  and  $v_j$  and this occurs with a probability  $\angle(v_i, v_j)/\pi$  (where  $\angle(v_i, v_j)$  denotes the angle between  $v_i$  and  $v_j$ ). The same is also true for higher dimensions. Indeed, let p denote the projection of r onto the 2-dimensional space F spanned by  $v_i$  and  $v_j$ . We have

$$r^T v_i = p^T v_i$$
$$r^T v_j = p^T v_j$$

implying that  $v_i$  and  $v_j$  are separated for the partition defined by r if and only if they are separated for the partition defined by p. But p/||p|| is uniform over the unit circle in F. Therefore,

$$Pr[(i,j) \in (S:\bar{S})] = \angle(v_i,v_j)/\pi$$

and, using the fact that  $v_i$  and  $v_j$  are unit vectors (and thus  $v_i^T v_j = \cos \angle (v_i, v_j)$ ):

$$Pr[(i,j) \in (S:\bar{S})] = \cos^{-1}(v_i^T v_j)\pi.$$

So, we get a closed-form formula for the expected weight of the cut produced:

$$E[w(S:\bar{S})] = \sum_{(i,j)} w_{ij} \cos^{-1}(v_i^T v_j) / \pi.$$

On the other hand, we know that

SDP = 
$$\sum_{(i,j)} w_{ij} (1 - v_i^T v_j)/2$$
.

Since  $w_{ij}$  is non-negative,  $E[w(S:\bar{S})]/\text{SDP} \geq \text{the smallest ratio over all } (v_i, v_j)$ :

$$E[w(S:\bar{S})]/\text{SDP} \ge \min_{-1 \le x \le 1} (\cos^{-1}(x)/\pi)/[(1-x)/2]$$
  
=:  $\gamma (\approx 0.87856)$ .

Several remarks are in order.

**Remark 2** The analysis is tight in the sense that, for any  $\varepsilon > 0$ , there exist instances such that  $OPT/SDP \leq \gamma + \varepsilon$ .[2]

**Remark 3** It is possible to derandomize Goemans-Williamson (and achieve a performance guarantee of  $\gamma$ ); still, in practice, the fact that one can output many cuts is useful as one can then exploit the variance of the weight of the cut.

**Remark 4** No approximation algorithm achieving better than  $\gamma$  is currently known.

**Remark 5** Approximating MAXCUT within 16/17 ( $\approx .94117$ ) + $\varepsilon$  for any  $\varepsilon > 0$  is NP-hard[3]. Approximating MAXCUT within  $\gamma + \varepsilon$  for any  $\varepsilon > 0$  is UGC-hard; that is, an efficient algorithm doing such would imply the falsity of the Unique Games Conjecture.

**Remark 6** It can be shown that the SDP relaxation above always has an optimal solution in dimension r where  $\frac{r(r+1)}{2} \le n$  (i.e.  $r \le 2\sqrt{n}$ ).

### 4 SPARSEST-CUT and Multicommodity-Cut

We now consider the problem of identifying a sparse cut in a graph: one which is as small as possible, relative to the number of edges which could exist between the sets of vertices. The latter quantity is maximized by balancing the vertices across the partition. Hence, we seek  $S \subset V$  minimizing  $w(S:\bar{S})/|S\times\bar{S}|$ . A generalization of SPARSEST-CUT is the multicommodity cut problem, in which we have, in addition to a capacitated G=(V,E), some k commodities, each associated with a "demand"  $f_i$  and a source and sink  $s_i,t_i\in V$ . (The idea is that we want to ship  $f_i$  units of commodity i from  $s_i$  to  $t_i$ .) We seek the value of a cut  $(S:\bar{S})$  with minimum capacity relative to the demand across it, i.e.,

$$\min_{S:\bar{S}} \frac{u(S:\bar{S})}{\left[\sum_{i:(s_i,t_i)\in(S:\bar{S})} f_i\right]}.$$

We will write  $\beta$  for the objective in this expression, and denote its optimum by  $\beta^*$ .

We recover SPARSEST-CUT by taking u = w and creating a commodity of demand 1 for each pair of vertices. As another special case, when k = 1, we are minimizing  $u(S : \bar{S})$  over cuts separating s and t, so we have the min s-t cut problem (in an undirected graph).

#### 4.1 Concurrent multicommodity flow

Let us now discuss a problem which is in a sense dual to the multicommodity cut. In concurrent multicommodity flow, we are given G = (V, E) with k commodities and capacity constraints on each edge  $\in E$ , and seek the maximum  $\alpha$  such that we can send  $\alpha f_i$  units of flow across the graph from  $s_i$  to  $t_i$  for all i simultaneously, without violating the capacity constraints on each edge. Let  $\alpha^*$  denote the optimal value. It is easy to see how to do multicommodity flow by linear programming.

The multicommodity cut and flow problems are related by  $\alpha^* \leq \beta^*$ . Indeed, if we can send  $\alpha f_i$  from  $s_i$  to  $t_i$  for all i,  $u(S:\bar{S})$  must be at least  $\alpha f_i$  for each  $(s_i,t_i)$  in the cut, so

$$\beta = \frac{u(S : \bar{S})}{\left[\sum_{i:(s_i, t_i) \in (S : \bar{S})} f_i\right]} \ge \alpha$$

for all feasible  $\beta$  and  $\alpha$ . This is a "weak duality"-type condition.

If k=1, we have equality, by the max s-t flow min s-t cut theorem (one can show that the theorem for directed graphs implies it also for undirected graphs). It is non-obvious that we have  $\alpha^* = \beta^*$  for k=2 as well. In general, however, we do not have equality. In figure 2, we show an example of a graph with a relatively small number of commodities (4) for which  $\alpha^*$  is strictly less than  $\beta^*$ .

In this graph, all capacities have value = 1. For this graph,  $\beta^* = 1$ . Consider the multicommodity cut given by the dashed line. For this cut, and any similar cuts, the sum of the capacities across the cut is  $u(S:\bar{S})=3$  and the amount of demand that needs to go through it is  $\sum_{i:(s_i,t_i)\in(S:\bar{S})}f_i=3$  also. If we choose a cut for which the capacities sum to 2 instead, the sum of the demands will also be 2. Therefore,  $\beta^*=1$ .

What is  $\alpha^*$  though? There are k=4 commodities in this graph, and yet a maximum of 3 units of flow can be pushed across a cut at one time. Since  $s_2$  and  $t_2$  are on the same side of the cut, you might think that  $\alpha^*$  might be able to reach 1. However, since each  $s_i$  is at least two edges away from its  $t_i$  and there are 4 commodities, if  $\alpha^* = 1$  then the sum of the flow on all the edges of the graph would have to be (4)(2)(1) = 8. Yet there only 6 edges, each with capacity 1. This shows that  $\alpha^* \leq 3/4$ .

So what IS the relationship between  $\alpha^*$  and  $\beta^*$  in general?

#### Theorem 2

$$\frac{\beta^*}{\alpha^*} = O(\log k).$$

Figure 2: An Example Graph where  $\alpha^* < \beta^*$ .

**Remark 7** Computing  $\beta^*$  is NP-hard. However—as we will see in the upcoming lecture — we can get a  $O(\log k)$  approximation using the LP we have for  $\alpha^*$ , and a tighter  $O(\sqrt{\log k})$  approximation using an SDP.

To prove the above result, we introduce metric spaces.

# 5 Finite Metric Spaces

**Definition 1** Let X be an arbitrary set, and d a function  $X \times X \to \mathbb{R}$ . (X, d) is a metric space if the following properties hold for all  $x, y, z \in X$ :

- 1.  $d(x,y) \geq 0$  (Nonnegativity)
- 2. d(x,y) = d(y,x) (Reflexivity)
- 3.  $d(x,y) + d(y,z) \ge d(x,z)$  (Triangle Inequality)

For simplicity, we will deal only with finite metric spaces (i.e. |X| is finite).

**Definition 2** Let X, Y be sets with associated metrics d,  $\ell$ . For  $c \ge 1$ , we say that (X, d) embeds into  $(Y, \ell)$  with distortion c if there is a mapping  $\phi: X \to Y$  such that for any  $x, y \in X$ ,  $d(x, y) \le \ell(\phi(x), \phi(y)) \le cd(x, y)$ . If c = 1, the embedding is called isometric.

This distortion measure is useful when we can transform a problem defined on one metric into another metric that is easier to deal with. This is precisely what we will do in the context of multicommodity cuts and flows.

The most familiar metric spaces are n-dimensional Euclidean spaces, where  $d(x,y) := \|x-y\|_2 = \sqrt{\sum_i (x_i-y_i)^2}$ . Generalizing gives the family of  $\ell_p^n$  spaces, where we work over the set  $\mathbb{R}^n$  and  $d(x,y) := \|x-y\|_p = (\sum_i |x_i-y_i|^p)^{1/p}$ . One can show that in the limit as  $p \to \infty$ , this expression tends to  $\max_i |x_i-y_i|$ . This space is denoted  $\ell_\infty^n$ .

Suppose (X, d) is isometrically embeddable into  $\ell_1$  (that is,  $\ell_1^n$  for some n). Is d isometrically embeddable into  $\ell_2$  as well? Not necessarily. Here we claim that  $\ell_2$ -embeddable metrics are only a subset of  $\ell_1$ -embeddable metrics, which in turn are a subset of  $\ell_\infty$  metrics. In fact, we put forth the following lemma:

**Lemma 3** Any finite metric space (V,d) is isometrically embeddable in  $\ell_{\infty}^{|V|}$ .

**Proof:** For notational purposes, let  $V = \{1, 2, ..., n\}$ . The mapping  $\phi: V \to \mathbb{R}^{|V|}$  is given by

$$\phi(v) = (d(1, v), d(2, v), \dots, d(n, v)).$$

Using properties of metrics, we have

$$d(u,v) = |d(u,u) - d(u,v)|$$

$$\leq \max_{i \in V} |d(i,u) - d(i,v)|$$

$$= ||\phi(u) - \phi(v)||_{\infty}$$

$$= \ell_{\infty}(\phi(u), \phi(v)).$$

On the other hand, the triangle inequality gives

$$(\phi(u) - \phi(v))_i = d(i, u) - d(i, v) \le d(u, v)$$
  
$$(\phi(v) - \phi(u))_i = d(i, v) - d(i, u) \le d(u, v)$$

for all i, so  $\ell_{\infty}(\phi(u), \phi(v)) = \max_{i \in V} |(\phi(u) - \phi(v))_i| \le d(u, v)$ .

**Remark 8** The  $\ell_2$ -embeddable finite metrics are  $\ell_1$ -embeddable.

The proof for this will be revisited in the next lecture. For now we return to the Multicommodity-Cut problem, and how metrics can help us get an approximation algorithm for it.

# 6 Back to multicommodity cut

In the notation of metric spaces, we have the following. (" $M \leq M'$ " means "M is isometrically embeddable in M'")

Theorem 4

$$\alpha^* = \min_{\ell : (V,\ell) \le \ell_{\infty}} \frac{\sum_{e=(i,j) \in E} u(e)\ell(i,j)}{\sum_{i=1}^{k} f_{i}\ell(s_{i},t_{i})}$$
$$\beta^* = \min_{\ell : (V,\ell) \le \ell_{1}} \frac{\sum_{e=(i,j) \in E} u(e)\ell(i,j)}{\sum_{i=1}^{k} f_{i}\ell(s_{i},t_{i})}$$

(Note that the only difference between these two expressions is the class of metrics in which we permit  $(V,\ell)$  to reside. Thus, since  $\alpha^*$  minimizes over a larger space, we have  $\alpha^* \leq \beta^*$  immediately—as we expect.) In the following lecture, we show an algorithm to compute  $\beta^*$  approximately, making use of the above.

#### References

- [1] M.X. Goemans and D.P. Williamson, Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming, J. ACM, 42, 1115–1145, 1995.
- [2] U. Feige and G. Schechtman, On the optimality of the random hyperplane rounding technique for MAX CUT, Algorithms, 2000.
- [3] J. Håstad, Some optimal inapproximability results, J. ACM, 48, 798–869, 2001.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

November 26, 2008

Lecture 21: Convex Hull in  $\mathbb{R}^2$  and Small-d LP's

Lecturer: Michel X. Goemans

## 1 Introduction

The first two thirds of this lecture serve as an introduction to this class's coverage of computational geometry. The reader is referred to [1] for additional coverage. We'll consider several approaches for finding the convex hull of a set of points. The first three algorithms discussed pertain to points in  $\mathbb{R}^2$ . Then, and more extensively in later lectures, we'll generalize to consider the  $\mathbb{R}^n$  case.

In the final third of this lecture we will return to the previous topic of linear programming, this time considering programs relevant to computational geometry- dealing with a small fixed number of variables. In the general *n*-dimensional case, no strongly polynomial algorithm is known. For the case of a small fixed dimension, however, we will see a deterministic algorithm that runs in polynomial time without dependence on the size of the coefficients defining the problem. In the next lecture, we'll see a randomized version that runs in linear time.

## 2 Convex Hulls in 2-Dimensions

**Definition 1** A set of points, C, is **convex** if the line segment joining any pair of points of C lies entirely in C. The **convex hull** of a set of points, S, is the intersection of all convex sets containing S.

We wish to find the convex hull of a given set of n points  $S = p_1, p_2, ...p_n \in \mathbb{R}^2$ . Representing a general convex hull is a nontrivial problem, but in two dimensions it is simple enough to come up with a convention. For purposes of this lecture, the convex hull H of  $S \in \mathbb{R}^2$  will be expressed non-uniquely as a clockwise ordered list of the vertices defining the boundary of the hull, and we will refer to this list as the convex hull. For example, given the points:

the hull H would be an ordered list  $(p_4, p_1, p_5, p_7, p_6)$ . Alternatively, the list  $(p_1, p_5, p_7, p_6, p_4)$  would also be a correct output.

#### 2.1 The Gift Wrapping Algorithm

The idea of the gift-wrapping algorithm is as follows: if we can start from some point on the boundary of the desired hull H, we can consider wrapping a string around all points in the set. This string (or wrapping paper in three dimensions) will contact only points on the boundary of the hull, one-by-one in order. The algorithm therefore starts with a point known to be in the hull. We can take, for example, the lowest point in the set (smallest y-coordinate)- if there are more than one, then the leftmost of these. In the example, this is the point  $p_4$ . The algorithm then considers every edge  $(p_4, p_i)$  and calculates the angle between that edge and horizontal, and chooses the point corresponding to the edge with smallest angle. The motion of "sweeping around" continues by iterating this step, finding the edge forming with smallest angle with the previous previous edge in the list for each subsequent point.

Pict 2

#### Algorithm 1 Gift Wrapping Algorithm

```
i \leftarrow i_0 with p_{i_0} the lowest,leftmost point in the set S
H \leftarrow \{i_0\}
repeat
let j:(p_i,p_j) be the edge forming the smallest angle with previous convex hull edge i \leftarrow j
H \leftarrow \operatorname{prepend}(H,p_i)\nuntil i=i_0
return H
```

**Runtime Analysis.** The initial "find min" runs in O(n) for each vertex in the hull, say there are h of them, the algorithm must calculate the angle of the line, an operation requiring constant time, O(1) thus, in total, O(n) for each vertex in the hull and therefore, O(nh) for the entire algorithm. This running time bound is *output-sensitive*. There exist 2d convex hull algorithms running in time  $O(n \log h)$ .

#### 2.2 Divide and Conquer Algorithm

Given the convex hull A of the left half of a set of points, and B that of the right half, if one can easily compute the convex hull of the entire set, then this method can be used to recursively compute the convex hull of a set S with a divide-and-conquer approach. In the divide step we recursively partition our set using median search to divide sets into > and  $\le$  this median. The conquer step becomes trivial since the convex hull of a single point is just the point itself. Finally we recursively merge the hulls of left and right subsets. We now examine the MERGE procedure in detail.

Our MERGE(A B) merges (disjoint) left and right hulls by finding the lower and upper segments

Our MERGE(A,B) merges (disjoint) left and right hulls by finding the lower and upper segments which connect the hulls to form the total convex hull. All points no longer on the boundary are

removed from the merged hull. In each case the key is for the lower segment to be *lower tangent* to both A and B and the upper segment to be *upper tangent* both A and B.

**Definition 2** A line segment is **lower tangent** to a set, S, if it intersects S at one point and if the remainder of S is above the line L formed by extending the segment to infinity in both directions. Similarly, a segment is **upper tangent** to a set, S, if it intersects S at one point and if the remainder of S is below L.

The MERGE procedure (see Algorithm 2) finds these segments by beginning with the segment connecting the right-most point of A and the left-most point of B and then alternates between walking down B and A; it switches to walking down the other whenever the current segment becomes lower tangent to one of them. This continues until the segment is lower tangent to both A and B.

Claim 1 The algorithm terminates.

**Lemma 2** At any time during the execution of the algorithm, the segment  $(a_i, b_j)$  intersects neither the interior of A nor the interior of B.

**Proof:** Clearly this is true initially, when  $a_i$  is the right-most point of A and  $b_j$  is the left most point of B. So the lemma is true iff either form of moving (taking a step clockwise around one hull or counterclockwise around the other) preserves the property. This is the case because, if we intersect the interior of say B for the first time by moving along B, in fact, we must have been at a lower tangent of B. The proves the lemma.

To prove the claim that the algorithm terminates, notice that the lemma implies that the algorithm will never consider a point in A past the leftmost point. Likewise for B and the rightmost point. This completes the proof that the algorithm must terminate.

#### Algorithm 2 MERGE left and right convex hulls.

```
Given: the convex hulls A = (a_0, a_2, ... a_{m-1}) and B = (b_1, b_2, ... b_{n-1})
Find: The convex hull H of A \cup B
(i) Find the upper connecting segment
  a_i \leftarrow \text{the right-most point of } A
  b_i \leftarrow \text{the left-most point of } B
  while (a_i, b_j) is not a upper tangent of A and B do
     while (a_i, b_j) is not a upper tangent of B do
       j \leftarrow j + 1
     end while
     while (a_i, b_j) is not a upper tangent of A do
       i \leftarrow i-1
     end while
  end while{thus walking counterclockwise around A and clockwise around B}
  (u_A, u_B) \leftarrow (i, j)
(ii) Find lower connecting segment
  a_i \leftarrow \text{the right-most point of } A
  b_j \leftarrow \text{the left-most point of } B
  while (a_i, b_j) is not a lower tangent of A and B do
     while (a_i, b_j) is not a lower tangent of B do
       j \leftarrow j - 1
     end while
     while (a_i, b_i) is not a lower tangent of A do
       i \leftarrow i + 1
     end while
  end while \{thus, the algorithm walks clockwise around A and walks counterclockwise around B\}.
  (l_A, l_B) \leftarrow (i, j)
(iii) Merge hulls
  H \leftarrow (a_{u_A}, b_{u_b}, \dots, b_{l_b}, a_{l_a}, a_{u_A} - 1) {taking a indices mod m and b indices mod n}
  return H
```

**Runtime Analysis.** Since MERGE(A,B) must terminate after at most n steps, where n is the total number of points in both hulls, MERGE(A,B) has runtime O(n). Considering the recursion used in the divide step (merge sort requiring only O(n) time), T(n) = 2T(n/2) + O(n) thus, the entire procedure's runtime is  $O(n \log n)$ .

#### 2.3 Incremental Algorithm

We now consider an algorithm based on the idea of efficiently adjusting a known convex hull H of a set S to obtain the convex hull H' of  $S \cup \{p\}$  whenever we add a single point p to S.

One approach might be as follows: if the new point p lies inside H then ignore it; if it lies outside H, figure out how to add it to H to get H'. However, constructing an entire convex hull this way can easily take quadratic time since it takes O(n) to check the position of each new  $p_{i+1}$  relative to each boundary segment of the hull  $H_i$ .

This approach can be rescued in two different ways. One is to randomly order the points and one can then prove that the expected runtime of this randomized incremental algorithm is  $O(n \log n)$ . Or, and this is the approach we follow now, we can first sort the points by their x coordinate. Then at each iteration, we know that the point  $p_i$  will be added to the hull, since it is the right-most point of the set  $\{p_1, \ldots, p_i\}$ , and we just have to work outward from  $p_{i-1}$  in the hull  $H_{i-1}$  to identify the vertices forming the upper and lower tangents of  $p_i$  with  $H_{i-1}$ . Hence we use a procedure similar to the technique we saw in the MERGE step of the divide-and-conquer approach, testing edges first clockwise around  $H_{i-1}$  to find a lower tangent, and then counterclockwise to find an upper tangent.

Edges and vertices are removed when they are between the intersections of the two tangent lines. The test for finding a tangent edge is simple: consider extending the current edge connecting  $p_{n+1}$  with the hull of S to a full line. If all of S is above this line, the line is lower tangent. If all of S is below this line, the line is upper tangent. Thus, a simple test to decide whether or not to continue walking is to check if the next point which would be walked to is above or below the extended line of  $(p_{n+1}, p_i)$ . If looking for an upper tangent, one stops when the next point is found to be below the line. If looking for a lower tangent, one stops when the next point is found to be above the line.

**Definition 3** Points in the hull of S above the left most point of S are said to comprise the **upper** envelope of S. Points in the hull of S below the left most point of S are said to comprise the **lower** envelope of S

#### **Algorithm 3** MERGE(H,p) incremental merge step

```
(i) Find lower tangent segment of p<sub>n+1</sub> and H
p<sub>i</sub> ← the right-most point of H
while (p<sub>i</sub>, p<sub>n+1</sub>) is not a lower tangent to S do
Remove p<sub>i</sub> from S'
p<sub>i</sub> ← p<sub>i+1</sub>
end while
l<sub>H</sub> ← i
(ii) Similarly, find upper tangent segment (p<sub>n+1</sub>, p<sub>u<sub>H</sub></sub>) between p<sub>n+1</sub> and H.
(iii) Compute hull
H' ← (p<sub>u<sub>H</sub></sub>, p<sub>n+1</sub>, p<sub>l<sub>H</sub></sub>, ..., p<sub>u<sub>H</sub>-1</sub>) {taking indices mod n where appropriate}
return H'
```

Runtime Analysis. The initial sort of the points by their x coordinate takes  $O(n \log n)$  time. For each addition of a new point,  $p_{n+1}$ , the number of iterations performed equals the number of edges deleted from the hull of S in making the hull of S'. Therefore, since the total number of edges deleted is upper bounded by the total number of edges created and since at most two edges are created whenever we add a point, we derive that the entire algorithm performs O(n) iterations. Each iteration takes O(1) time, for a running time of O(n) over all iterations, and a total of  $O(n \log n)$  taking into account the initial sort.

#### 2.4 A Lower Bound on Two-Dimensional Comvex Hull Computations

**Theorem 3** Convex hull algorithms for n points in  $\mathbb{R}^2$  is as hard as sorting.

**Proof:** We reduce the problem of sorting n numbers  $x_1, x_2, ..., x_n \in \mathbb{R}$  to a convex hull computation. Consider the set of points  $S = ((x_1, x_1^2), (x_2, x_2^2), ..., (x_n, x_n^2))$  on a parabola in  $\mathbb{R}^2$ . Knowing the ordering in which these points appear on their convex hull allows to easily sort the original numbers  $x_1, \dots, x_n$  as the orderings are the same (up to a possible cylic shift).  $\square$  However, we have to be careful how we interpret that result. Indeed, the classical  $\Omega(n \log n)$  lower

However, we have to be careful how we interpret that result. Indeed, the classical  $\Omega(n \log n)$  lower bound for sorting applies in the *comparison* model, but in the comparison model, one cannot even compute the convex hull. See Sedgewick and Wayne [2] for a more detailed discussion. Yao [3] has shown that in the *quadratic decision tree model* in which one can test the sign of a quadratic polynomial, the number of operations required for computing the convex hull of n points in  $\mathbb{R}^2$  is  $\Omega(n \log n)$ .

## 3 Convex Hulls in Higher Dimensions

In higher dimensions, we can no longer represent convex hulls as simple ordered lists. The boundary of a d-dimensional convex hull is a collection of d-1-dimensional polytopes, which in turn are described by "faces" of dimension  $0, \ldots, d-2$ . The terminology for faces is the following:

| dim | name     |
|-----|----------|
| 0   | vertices |
| 1   | edges    |
| d-2 | ridges   |
| d-1 | facets   |

To describe such a hull, one typically constructs an *incidence graph*. The vertices of this graph may either correspond to all faces, or just to the ridges and facets. We connect a k-dimensional face F with a k-1-dimensional face F' if F contains F'.

What is the complexity of the output? In 2 dimensions, the number of faces is O(n). In 3 dimensions, Euler's formula says that h-e+f=2 where h is number of vertices, e is number of edges, and f is number of faces, and this implies that e, f = O(n). In 3 dimensions, the gift wrapping algorithm as well as an incremental algorithm run in  $O(n^2)$  time, while a more complex divide-and-conquer algorithm can be made to run in  $O(n \log n)$  time. For higher dimension D, one can show that the number of facets is  $O(n^{\lfloor d/2 \rfloor})$ , so this is definitely a lower bound on the time required to construct a convex hull. Not surprisingly, in general, convex hull algorithms are considerably more complicated in higher dimensions. In the next lecture, we'll see a simple randomized algorithm achieving the lower bound (for d > 3).

# 4 Linear Programming in fixed dimension

Consider a linear program:

$$\max c^T x$$
$$Ax < b,$$

where  $A \in \mathbb{R}^{n \times d}$ ,  $x \in \mathbb{R}^d$ , and the dimension d is fixed (not part of the input).

As said in earlier lectures, a strongly polynomial (i.e. not dependent on the size of the entries of the data) time algorithm for linear programming in the general case is not known. However, for fixed dimension, we'll show that such algorithm exists, and we will present a simple randomized algorithm whose running time will be linear in n (for fixed d). This was sketched in this lecture, but the derivation will be formalized in the next lecture.

# References

- [1] M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, "Computational Geometry", 3rd edition, Springer, 2008.
- [2] R. Sedgewick and K. Wayne, "Algorithms", 4th Edition.
- $[3]\,$  A. C.-C. Yao, "A Lower Bound to Finding Convex Hulls", J. ACM, 28, 780–787, 1981.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

### 18.415/6.854 Advanced Algorithms

December 1, 2008

### Lecture 22

Lecturer: Michel X. Goemans

In this lecture, we introduce Seidel's algorithm [3] to solve linear programs with n constraints in dimension d, when the dimension is small. The expected running time of Seidel's algorithm is O(d!n), i.e. it is strongly polynomial for fixed dimension d (strongly, since it does not depend on the size of the input coefficients). Then, we use Seidel's algorithm to develop a randomized convex-hull algorithm in an arbitrary dimension d which is the best possible when  $d \ge 4$ .

## 1 Linear Programming in Fixed Dimension

In this section, we fix the dimension d. We wish to find a strongly-polynomial time algorithm to solve linear programming.

### 1.1 Seidel's Algorithm

Let H be a set of n inequalities. Each inequality corresponds to a half-space h determined by a hyperplane. Let LP(H) be the linear program that minimizes  $c^Tx$  subject to the constraints:

$$x \in \bigcap_{h \in H} h, \quad x \in \mathbb{R}^d.$$

To make the description of the algorithm simpler, we make the following two assumptions:

- 1. Bounded: the feasible region is bounded, i.e. there exists M such that, for any feasible x,  $-M \le x_i \le M$  for all i = 1, 2, ..., d.
  - This assumption can be enforced by ficticiously imposing a large bounding box, and whenever one of the inequalities of this bounding box is tight at optimum, we know that the linear program is unbounded.
- 2. Non-degenerate: the intersection of any d+1 hyperplanes is empty. In 2-D, non-degeneracy means that there do not exist three lines meeting at the same point.
  - If H does not meet this assumption, we can use some standard tricks like perturbation to make it non-degenerate. This can be handled by doing so-called lexicographic perturbation.

These two assumptions imply that for any  $H' \subseteq H$ , LP(H') has a unique solution x(H'). Seidel's algorithm will actually apply to a more general class of problems than linear programming, but here we'll focus on linear programming. What is actually needed in the generalization is that the unique solution x(H') is defined by a basis:

**Definition 1** A subset  $B \subseteq H'$  is called a basis of the linear program LP(H') if x(B) = x(H') and B is minimal.

Seidel's algorithm solves the linear program H incrementally as follows. Chooes uniformly  $h \in H$ . Solve the linear program with h removed, and get a solution x. If the solution x satisfies h, then return x. If the solution x does not satisfy h, we impose the condition that h is satisfied at equality, and eliminate one variable. Then solve the linear program with d-1 variables and n-1 inequalities. The correctness of this algorithm was proved in the last lecture.

In Seidel's algorithm, we can stop the recursion when we have either n constraints in d = 1 variable (which takes O(n) time to solve), or 1 constraint in d variables (which takes O(d) time to optimize over our ficticious bounding box).

### 1.2 Analysis of Running Time

Let T(d,n) be the expected running time of Seidel's algorithm on an instance with n inequalities and d variables. To find a recursive relation for T(d,n), note that we first recursively solve an LP with n-1 inequalities and d variables, which takes time T(d,n-1). If the solution x satisfies the removed constraint h (which takes O(d) time to check), we are done and simply return the d coordinates of x. If x does not satisfy h, we first reduce the LP to only d-1 variables in O(dn) time (it takes O(d) time to eliminate one variable in each constraint) using the constraint h, and then solve the LP with n-1 inequalities and d-1 variables in T(d-1,n-1) time. The probability that x does not satisfy h is d/n, since the optimal solution is determined by exactly d inequalities and we have selected an inequality uniformly at random. This is the important step in the analysis and is known as backward analysis.

By the analysis above, we have

$$T(d,n) = T(d,n-1) + O(d) + \frac{d}{n} \left( O(dn) + T(d-1,n-1) \right)$$
$$= T(d,n-1) + \frac{d}{n} T(d-1,n-1) + O(d^2).$$

The base cases are T(1, n) = O(n) and T(d, 1) = O(d).

Using this recursive relation, we can prove by induction on d + n that

#### Claim 1

$$T(d,n) = O\left(\left(\sum_{1 \le i \le d} \frac{i^2}{i!}\right) d!n\right) = O(d!n).$$

**Proof:** The base case is satisfied. We need to check the induction step. Suppose that

$$T(d, n-1) = O\left(\left(\sum_{1 \le i \le d} \frac{i^2}{i!}\right) d!(n-1)\right),$$

$$T(d-1, n-1) = O\left(\left(\sum_{1 \le i \le d-1} \frac{i^2}{i!}\right) (d-1)!(n-1)\right).$$

Since

$$\sum_{1 \le i \le d} \frac{i^2}{i!} \cdot d!(n-1) + \frac{d}{n} \sum_{1 \le i \le d-1} \frac{i^2}{i!} \cdot (d-1)!(n-1) + d^2 \le \left(\sum_{1 \le i \le d} \frac{i^2}{i!}\right) d!n,$$

the claim also holds for T(d, n).

The second equality in the claim follows from the fact that  $\sum_{i=1}^{\infty} \frac{i^2}{i!}$  is finite.

Thus, we have shown a strongly polynomial time algorithm to solve linear programs in a fixed small dimension d.

## 1.3 Improvement (Matousek, Sharir, Welzl [2])

Although the expected running time of Seidel's algorithm is strongly-polynomial in n, it increases exponentially when d increases (more precisely, the dependence on d is  $2^{O(d \log d)}$ ). In this subsection, we briefly introduce an improvement to Seidel's algorithm which gives a subexponential bound in d.

We consider the linear program as follows. The LP algorithm LP(H,C) takes as input a candidate set C (that plays the role of a basis), and returns x as well as a basis B. Initially, we call LP(H,C) with  $C=\emptyset$ .

The algorithm proceeds as follows. If H = C, then return C. If  $H \neq C$ , choose h randomly among H - C. We recursively call  $LP(H - \{h\}, C)$  and get a basis B. If h is satisfied by the solution defined by B, then return B. Otherwise, we call LP(H, basis(B, h)), where basis(B, h) denotes an optimal basis for  $LP(B \mid \{h\})$ .

Claim 2 The expected running time is

$$O\left(e^{2\sqrt{d\log(n/\sqrt{d})}+O(\sqrt{d})+O(\log n)}\right).$$

When d is fixed, the running time is a polynomial of n. When n is fixed, the running time is  $O(e^{\sqrt{d}})$ , subexponential in d.

Use a trick due to Clarkson (through random sampling), one can show that linear programs with n inequalities in d dimensions can be solved in

$$O(d^2n + e^{\sqrt{d\log d}})$$

time. This is the best bound currently known that is independent on the size of entries. See Goldwasser [1] for a discussion.

## 2 Convex Hull

Given n points  $x_1, \ldots, x_n \in \mathbb{R}^d$ . Let P be the convex hull of  $x_1, \ldots, x_n$ . For d = 2 and d = 3, P can be found in  $O(n \log n)$  time. In the previous lecture, we showed several algorithms that solve 2-dimensional convex hull in  $O(n \log n)$  time.

Throughout this section, we assume that the points  $x_1, \ldots, x_n$  are in general position, meaning that any d+1 points do not lie on the same hyperplane. If that's not the case, a standard perturbation argument can be used.

#### 2.1 Outputs of Convex Hull Algorithms

In dimension 2, it is sufficient to output the vertices of the convex hull in counterclockwise order. In this subsection, we introduce what the output is for a general d.

**Definition 2** For any  $0 \le k < d$ , a k-face of a d-dimensional polytope P is a face of P with dimension k. A (d-1)-face is called a facet. A (d-2)-face is called a ridge. A 1-face is called an edge. A 0-face is called a vertex.

**Definition 3** A simplicial polytope is a polytope where every face is a simplex.

Since the points  $x_1, \ldots, x_n$  are in general position, the convex hull P is a simplicial polytope.

The convex hull algorithm outputs a facet graph  $\mathcal{F}(P)$ . The vertices of  $\mathcal{F}(P)$  are all facets of P. The edges of  $\mathcal{F}(P)$  correspond to the ridges of P, connecting two facets shared by the ridge (Figure 1).

For general d, one can show that the number of facets of P is  $O(n^{\lfloor d/2 \rfloor})$ . Since the convex hull algorithm needs to output all the facets of P, the running time of any such algorithm is at least  $\Omega(n^{\lfloor d/2 \rfloor})$ .

#### 2.2 Convex Hull Algorithms

Clarkson and Shor '89 developed a randomized algorithm to compute convex hull in  $O(n \log n + n^{\lfloor d/2 \rfloor})$  expected time. Chazelle '93 developed a deterministic algorithm in  $O(n \log n + n^{\lfloor d/2 \rfloor})$  time. These algorithms are optimal by the analysis in the previous subsection.

Figure 1: The figure on the left is part of a 3-dimensional simplicial polytope with four vertices labeled  $x_1, x_2, x_3, x_4$ . On the right is the corresponding facet graph, where the faces  $x_1x_2x_3$ ,  $x_2x_3x_4$ , and the edge  $x_2x_3$  are labeled.

We will illustrate Seidel's algorithm [3], which has running time  $O(n^2 + n^{\lfloor d/2 \rfloor})$ . For d = 2 and d = 3, Seidel's algorithm takes time  $O(n^2)$ , which is not optimal. But for larger d, Seidel's algorithm is optimal, and is considerably simpler.

We take a random permutation  $x_1, x_2, \ldots, x_n$  of the points. Let  $P_i$  be the convex hull of the points  $x_1, \ldots, x_i$ .

Initially  $P_{d+1} = \text{conv}(x_1, \dots, x_{d+1})$  is a d-dimensional simplex.  $\mathcal{F}(P_{d+1})$  is the complete graph on d+1 points. We incrementally compute  $P_{d+2}, \dots, P_n$ . To do this, we need the following definitions.

**Definition 4** A facet F of a polytope P is visible from a point  $x_i$  if the supporting hyperplane of F separates  $x_i$  from P. Otherwise, F is called obscured.

**Definition 5** A ridge of a polytope P is called visible from a point  $x_i$  if both facets it connects are visible, and obscured if both facets are obscured. A ridge is called a horizon ridge if one of the facets it connects is visible and the other is obscured.

To compute the convex hull  $P_i$  when adding a new point  $x_i$ , Seidel's algorithm performs the following four steps.

- Step 1 Find one visible facet F if one exists. If there is no visible facet, we are done. This step can be done using linear programming in O(d!i) time. Indeed we would like to find a hyperplane  $a^Tx \leq b$  (where the unknowns are  $a \in \mathbb{R}^d$  and b) such that  $a^Tx_i = b$  and  $a^Tx_i \leq b$  for  $j = 1, \dots, i-1$ . Any extreme solution will correspond to a new facet and to a horizon ridge. One of the two facets indicident to this horizon ridge is visible.
- Step 2 Find all visible facets. Determine all horizon ridges. Delete all visible facets and all visible ridges.

This can be done by depth-first-search (DFS), since the visible facets and invisible facets are seperated by horizon ridges. In terms of running time, we charge the deletion time of the facets to when the facets were created.

- Step 3 Construct all new facets. Each horizon ridge corresponds to a new facet containing the point  $x_i$  and the ridge (Figure 4).
- Step 4 Each new facet contains d ridges. Generate all these new ridges. Every new ridge R is a sequence of d-1 points  $a_1 < a_2 < \ldots < a_{d-1}$ . Then match corresponding ridges using radix sort to construct the facet graph.

Figure 2: In 3-D, ridges are just edges.

Figure 3: The visible ridges and the invisible ridges are seperated by horizon ridges.

Figure 4: In the figure on the top, the shaded regions are visible facets. In the figure on the bottom, visible facets are removed and new facets are added.

The expected running time of Seidel's algorithm to compute the convex hull is  $O(n^2 + n^{\lfloor d/2 \rfloor})$ . Indeed the running time is

$$O\left(\sum_{i=d+2}^{n} (i+N_i)\right),\,$$

where  $N_i$  is the number of facets created at step i. One has that

$$E[N_i] = E[\text{facets of } P_i \text{ containing } x_i] \le \frac{\binom{i-1}{d-1}}{\binom{i}{d}} O(i^{\lfloor d/2 \rfloor}) = \frac{d}{i} O(i^{\lfloor d/2 \rfloor}),$$

giving the required time bound.

# References

- [1] M. Goldwasser, "A survey of linear programming in randomized subexponential time", ACM SIGACT News, 26, 96–104, 1995.
- [2] J. Matousek, M. Sharir, and E. Welzl, "A subexponential bound for linear programming", *Algorithmica*, **16**, 498–516, 1996.
- [3] R. Seidel, "Small-dimensional linear programming and convex hulls made easy", *Discrete & Computational Geometry*, **6**, 423–434, 1991.

---

MIT OpenCourseWare http://ocw.mit.edu

6.854J / 18.415J Advanced Algorithms Fall 2008

For information about citing these materials or our Terms of Use, visit: http://ocw.mit.edu/terms.

Lecture 23

Lecturer: Michel X. Goemans

# 1 Voronoi Diagrams

### 1.1 Introduction

Suppose we are given a set P of points in the Euclidean plane, and we are interested in the problem of, given a point x, find the closest point of P to x. One approach to this problem is to divide the plane into regions associated with each  $p_i \in P$  for which x is closest to  $p_i$ . Finding these regions in two dimensions is the problem of constructing the Voronoi Diagram. One application of this structure is to compute the minumum spanning tree of a complete graph of n vertices in the Euclidean plane in time  $O(n \log n)$ .

## 1.2 Definitions

We will focus on the two-dimensional case. We are given a set

$$P = \{p_1, p_2, \dots, p_n\} \subseteq \mathbb{R}^2$$

and we want to partition the plane into regions which correspond to points which are closest to a specific point.

Figure 1: Voronoi Diagram (solid lines) for four points  $p_1$ ,  $p_2$ ,  $p_3$ ,  $p_4$ .

**Definition 1 (Voronoi Cell)** Given a set of points in  $\mathbb{R}^2$ ,  $P = \{p_1, p_2, \dots, p_n\} \subseteq \mathbb{R}^2$ , a Voronoi Cell  $V(p_i)$  is defined by:

$$V(p_i) = \{x : d(p_i, x) < d(p_i, x) \ \forall i \neq i \}.$$

Another way to define a Voronoi Cell is by defining  $h(p_i, p_j)$  to be the halfplane containing  $p_i$  defined by the bisector of  $p_i$  and  $p_j$ . A cell is then defined as:

$$V(p_i) = \bigcap_{j \neq i} h(p_i, p_j).$$

This implies that every cell is convex and is a (convex) polygonal region with at most n-1 sides.

**Definition 2 (Voronoi Diagram)** A Voronoi Diagram is a collection of Voronoi cells that covers  $\mathbb{R}^2$ .

### 1.3 Motivation

Why is a Voronoi Diagram useful? If the points represent firestations, the Voronoi cells represent the partition of the plane into regions which are closer to each firestation. More generally, given a point in a plane, it is useful to know the point from a set of points that is closest to it. Of course, this also requires a data structure to be able to answer the *point location problem* of, given x, finding the Voronoi cell that contains it. We will only learn how to construct the Voronoi diagram, not how to build a query datastructure for it.

Having such a diagram is useful for many problems. For example, a Voronoi diagram allows computation of the Euclidian minimum spanning tree on a set of points in  $O(n \log n)$  time, see the problem set.

# 1.4 Properties

The Voronoi cells are all disjoint and their closures cover the entire plane. The Voronoi diagram will consist of edges (possibly semi-infinite, extending to infinity) and vertices where 3 or more of these edges meet; these vertices will be equidistant to 3 or more points of P. One can characterize the vertices and the edges in the following way:

- **Lemma 1** 1. A point  $q \in \mathbb{R}^2$  is a vertex of a Voronoi Diagram  $\iff$  there exists an empty circle (i.e. its interior is empty) centered at q having at least 3 points of P on its boundary.
  - 2. Part of the bisector between  $p_i$  and  $p_j$  is an edge of the Voronoi diagram  $\iff$  there exists an empty circle centered at a point q having precisely  $p_i$  and  $p_j$  (and no other point) on its boundary.

We look now at how 'complex' a Voronoi diagram can be. We know that each cell is delimited by at most n-1 sides (edges), but in the lemma below, we show that collectively all cells do not have too many edges and vertices.

**Lemma 2** For a Voronoi diagram with n points, the following relations hold:

- The number of vertices of a Voronoi diagram is  $n_v \leq 2n 5$ .
- The number of edges in any Voronoi diagram is  $n_e \leq 3n 6$ .

Figure 2: To prove Lemmma 2 we add a point  $q_{\infty}$  to the Voronoi Diagram (solid lines), and connect all of the infinite edges to this point (shown in dotted lines).

**Proof:** We can view the Voronoi diagram as a planar graph, G, with some edges extending out to infinity. We add a point at infinity  $q_{\infty}$  representing 'infinity' and connect edges that extend to infinity to this point as shown in Figure 2. Note that the resulting graph G' is still planar.

The number of vertices in G' is  $n_v + 1$ ; the number of edges is  $n_e$ , and the number of faces is n. By Euler's formula, we have

$$n_v + 1 - n_e + n = 2.$$

Since we know that vertices will have at least 3 edges incident to them, we obtain, by summing the degrees over all vertices, that:

$$\sum_{\text{vertices } v} d(v) = 2n_e \ge 3(n_v + 1).$$

Combining this with Euler's formula, we get:

$$2(n_v + 1) + 2n \ge 4 + 3(n_v + 1)$$

or  $2n-5 \ge n_v$ . Using this in Euler's formula, we now get

$$n_e = n_v - 1 + n \le 3n - 6.$$

# 2 Computation of Voronoi Diagrams

### 2.1 Introduction

There are two primary algorithms we want to introduce. Both of these will be shown to compute the Voronoi diagram in time  $O(n \log n)$ . First, we can reduce the computation of the Voronoi diagram to that of a convex hull in  $\mathbb{R}^3$ , which is computable in time  $O(n \log n)$ ; this is our first algorithm. Secondly, we will review the sweep line algorithm of Fortune [1].

### 2.2 Convex Hull

Figure 3: Projection of a point onto a paraboloid in  $\mathbb{R}^3$ . To use the convex hull to compute the Voronoi diagram, this projection is done for all points in the set of points for which we want to compute the Voronoi diagram.

Suppose we have a set  $P \subseteq \mathbb{R}^2$  and we want to compute the corresponding Voronoi diagram. Let us consider the set  $P' = \{(x_i, y_i, x_i^2 + y_i^2) : (x_i, y_i) \in P\}$ . This projection onto a parabola is shown in Figure 3.

Consider the set of planes tangent to each point in P'. The intersection of the upper half spaces of these planes gives a polyhedral set Q whose projection back to  $\mathbb{R}^2$  gives the Voronoi diagram in the following sense: the projection of the facets (resp. edges, vertices) of Q gives the Vornoi cells (resp. edges, vertices) of the Voronoi diagram. This computation can be done in  $O(n \log n)$  time since this calculation is the geometric dual of the convex hull computation.

If, instead, we were to compute the convex hull of P' (rather than the halfs-paces tangent to the paraboloid at P') and project it back to  $\mathbb{R}^2$ , we would obtain a straight-line drawing on P (dual to the Voronoi diagram) known as the *Delaunay Triangulation*, see problem set.

### 2.3 Sweep Line Algorithm

The idea of a sweep line algorithm is to advance a line (in 2D) or a plane (in 3D) down through space, processing events as they occur. We will construct the Voronoi diagram as we sweep the line from top to bottom, and at any instance we will only have needed to consider points at or above the sweep line.

We cannot construct the entire diagram above the sweep line, but we can construct pieces of it. If we look at a single point above the line,  $p_i$ , for some points, they will assuredly be closer to it than to any points below the sweep line. This forms a parabola  $C(p_i)$  defined by the points equidistant from the point and the sweep line. We can find the parabola associated with each of the points. For any point that is above some parabola, we can correctly assign it to its Voronoi Cell.

Figure 4: A set of parabolae  $C(p_i)$  associated with four points  $p_i$ . Parabolae are denoted with thin lines, the beach line with a thick line, and the associated sweep line with a thick dashed line.

**Definition 3 (Beach line)** We define a Beach Line as the lower envelope of all parabolae  $C(p_i)$  for all points above the sweep line. A beach line is shown in Figure 4.

**Definition 4 (Breakpoint)** A breakpoint q is a point on the beach line that belongs to at least two parabolae.

Figure 5: Sample beach line illustrating multiple break points originating from the same parabola

The beach line is a series of segments of parabolae. A breakpoint q corresponding to the parabolas  $C(p_i)$  ad  $C(p_q)$  must be equidistant from both  $p_i$  and  $p_j$  since we know that  $d(q, p_i) = d(q, sweep) = d(q, p_j)$ . Furthermore, no other point of P is closer to q. Thus, by Lemma 1, q is part of an edge of the Voronoi diagram, and is part of the bisector between  $p_i, p_j$ . An example is shown in Figure 6.

We will keep track of which  $p_i$  the breakpoints are associated with in order. Note a beach line could have several segments from the same parabola, as illustrated in Figure 5.

#### 2.3.1 Events

As we sweep the line, we are not going to keep track of the precise location of the beach line (as it constantly changes) but we will just keep track of the points  $p_i$  corresponding to the parabola segments of the beach line from left to right. Several events can happen that modify this sequence of points  $p_i$ .

1. A 'Site Event' occurs when the sweep line goes through a new point  $p_l$ . This results in additition of an arbitrarily narrow parabola around  $p_l$  to the beach line. A sample site event is shown in Figure 7. If  $p_l$  intersects the parabola associated with  $p_j$ , we could write the change in the sequence of points as:

$$p_i p_j p_k \rightarrow p_i p_j p_l p_j p_k$$

Note we insert exactly one segment per site event, so there are n in total. Notice that each such addition increases the number of segments by 2, as shown above.

Figure 6: Illustration of points q on an edge of a Voronoi diagram as constructed by a moving sweep line.

We'll see that this is the only way of creating a new segment in the beach line, so this implies that the total number of segments in the beach line is at most 2n-1 (1 segment for the first site event, and 2 more for each subsequent site event).

2. A 'Circle Event' occurs when lowering the beach line causes a segment to disappear from the beach line. This boundary case is illustrated in Figure 8, which can be compared to Figure 6 to show the effect of a moving sweep line.

When a segment disappears, we have discovered a new vertex in the Voronoi diagram. Indeed, when a circle event occurs, we must have the three closest points equidistant to the vertex, and thus we have a vertex by Lemma 1.

The center of the circle is determined by  $p_1$ ,  $p_2$  and  $p_3$  (corresponding to 3 consecutive segments on the beach line), and the circle event will happen when the sweep line is tangent to the circle (below it). When a circle event happens, the beach line is modified in the following way:

$$p_1 p_2 p_3 \rightarrow p_1 p_3$$

Claim 3 The only way for the beach line to change is through a site event or a circle event. In other words, these are the only ways to create and remove segments.

We will not formally prove this – this is intuitive.

Figure 7: Site event. Parabolae shown with thin lines and the beach line shown as a thick line.

#### 2.3.2 Data Structures

In order to construct a diagram, we will describe three data structures:

### 1. Event queue:

Construct a priority queue containing events. The key of an event is its y-coordinate. For a site event the y-coordinate is the y-coordinate of the associated point. For a circle event, this is the position of the sweep line which is (lower) tangent to the circle.

We first insert the n site events into the priority queue, as we know the y coordinate of all the points. Consider moving the line down and processing events as they occur. Circle events are defined by looking at three consecutive segments of the beach line. Every time we introduce a new segment in the beach line, as happens in a site event, we potentially create two new circle events (potentially, since three consecutive segments create a circle event only if the 3 points are distinct). We may also need to delete some circle events.

Let us consider the addition shown in Figure 7. We will have removed the potential circle event  $p_i$   $p_j$   $p_k$  and added potential circle events  $p_i$   $p_j$   $p_l$  and  $p_j$   $p_l$   $p_k$ . Note that the deleted event can be thought of as a fake event because it was removed before it really happened and was processed. Still such a circle event was added to the event queue and then removed. There is at most one deleted (fake) circle event for each site event processed. Notice that the number of real circle events is equal to the number of vertices of the Voronoi diagram,  $n_v \leq 2n - 5$ .

Any circle event that is processed is real, and leads to a segment of the beach line disappearing. In terms of Figures 6 and 8, we would take  $p_1$   $p_2$   $p_3$  to  $p_1$   $p_3$ .

Figure 8: Circle event. Parabolae shown with thin lines, Voronoi diagram with thick lines, and the sweep line with a thick dashed line.

In general, we can write this as "Go from  $p_i$   $p_j$   $p_k$   $p_l$   $p_m$  to  $p_i$   $p_j$   $p_l$   $p_m$ ". We may need to delete up to two circle events corresponding to the lost segment and add two new events, corresponding to the new order. In this example, we are deleting circle events  $p_i$   $p_j$   $p_k$  and  $p_k$   $p_l$   $p_m$  and adding  $p_i$   $p_j$   $p_l$  and  $p_j$   $p_l$   $p_m$  (or a subset of them if some of the indices are equal). We are always adding and deleting a constant number of events (for each site event and real circle event), thus the total number of additions and deletions to the priority queue will be linear. Since we must process O(n) events corresponding to O(n) priority queue operations, the total runtime will be  $O(n \log n)$ .

#### 2. Beach line encoding:

We keep track of the points corresponding to the parabola segments constituting the beach line and the breakpoints  $p_i$   $p_j$  by creating a binary search tree in which points are leaves and internal nodes are breakpoints.

Note that this is an extension of the standard binary search tree because we have two different types of nodes (parabola segments and breakpoints). This prevents us from directly using a splay tree, since the splay action permutes the leaves and branches of the tree. One way to deal with this is to forget about parabola segments, and keep track of the breakpoints (as pairs of points), keyed from left to right.

When a site event occurs, we need to be able to locate the x value in the beach line. To use a binary search tree, we thus need to be able to perform binary comparisons to determine if the desired x value is to the left or right

of a breakpoint. Given a breakpoint as an ordered pair  $(p_i, p_j)$  and a sweep line, we can easily compute the x position of the breakpoint and decide if we must move to the right or to the left. In a circle event, we have three parabola segments and must remove the middle one. This is a delete operation. Thus there are a constant number of BST operations per circle or site event. Using a BST with amortized cost  $O(\log n)$  time per operation, maintaining the beach line is therefore  $O(n \log n)$  time.

### 3. Voronoi Diagram:

Let us replace each edge (shared by 2 cells) of the Voronoi diagram with two corresponding directed half-edges which are 'twin' to each other. Each half edge corresponds to one of the two cells, and each is oriented counterclockwise (with respect to its cell). For each half-edge, we define pointers:

- to its twin,
- to the next half-edge on the cell,
- to the previous half-edge on the cell.

From a given vertex we can follow the half-edges around a cell; by calling twin, we can move between cells and we can for example enumerate all half-edges incident to a vertex.

Let us consider how to modify this structure upon processing a site (Figure 7) and circle (Figure 8) events. In a site event, the two new breakpoints are equidistant from  $p_j$  and  $p_k$ , and are part of an edge of the Voronoi diagram. This will create two new half-edges. In a circle event we link the half edges that meet to construct the diagram. Thus there are a linear number of operations on this data structure as wll.

In summary, the first structure requires a linear number of operations each taking  $O(\log n)$  time. Similarly, for the second data structure, with a balanced BST. The last one requires constant time per event, for a linear number of events. Hence the total time to construct a Voronoi diagram is  $O(n \log n)$ .

We can show this is optimal because the Voronoi diagram of the set of points given by  $P = \{(x_i, \pm 1)\}$  solves the problem of sorting P, hence the diagram must take at least  $O(n \log n)$  time to sort.

Note we use  $\pm 1$  since we have assumed throughout this that we are not in the purely degenerate case in which all points are colinear; one can show that this is indeed the only case in which the Voronoi diagram has infinite lines and no vertices.

# References

[1] S Fortune. A sweepline algorithm for voronoi diagrams. In SCG '86: Proceedings of the second annual symposium on Computational geometry, pages 313–322, New York, NY, USA, 1986. ACM.
