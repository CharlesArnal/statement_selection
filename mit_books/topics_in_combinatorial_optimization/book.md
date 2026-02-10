| 18.997 Topics in Combinatorial Optimization | February 3rd, 2004  |
|---------------------------------------------|---------------------|
| Lecture 1                                   |                     |
| Lecturer: Michel X. Goemans                 | Scribe: Nick Harvey |

## 1 Nonbipartite Matching

Our first topic of study is matchings in graphs which are not necessarily bipartite. We begin with some relevant terminology and definitions. A matching is a set of edges that share no endvertices. A vertex v is covered by a matching if v is incident with an edge in the matching. A matching that covers every vertex is known as a perfect matching or a 1-factor (i.e., a spanning regular subgraph in which every vertex has degree 1). We will let  $\nu(G)$  denote the cardinality of a maximum matching in graph G. A vertex cover is a set C of vertices such that every edge is incident with at least one vertex in C. The minimum cardinality of a vertex cover is denoted  $\tau(G)$ . The following simple proposition relates matchings and vertex covers.

**Proposition 1** If M is a matching and C is a vertex cover then  $|M| \leq |C|$ .

**Proof:** For each edge in M, at least one of the endvertices must be in C, since C covers every edge. Since the edges in M do not share any endvertices, we must have  $|M| \leq |C|$ .

This proposition implies that  $\nu(G) = \max_M |M| \le \min_C |C| = \tau(G)$ , so  $\nu(G) \le \tau(G)$ . König showed that in fact equality holds if G is a bipartite graph with no isolated vertices. Unfortunately if G is not bipartite then we may have  $\nu(G) < \tau(G)$ . For example, if G is the cycle on three vertices then  $\nu(G) = 1$  but  $\tau(G) = 2$ . We will give another upper-bound for  $\nu(G)$  after introducing some more definitions.

If G = (V, E) is a graph and  $U \subseteq V$ , G - U denotes the subgraph of G obtained by deleting the vertices of U and all edges incident with them. Let o(G - U) denote the number of components of G - U that contain an odd number of vertices. Let M be a matching in G - U and consider a component of G - U with an odd number of vertices. There must be at least one unmatched vertex v in this component, since any matching necessarily covers an even number of vertices. Treating M as a matching in G, it is possible that we could increase the size of M by matching v with some vertex in U. However, we can add at most |U| edges to M in this manner, since the vertices in U will eventually all be matched. Thus any matching in G must have least o(G - U) - |U| unmatched vertices. This argument shows that the maximum size of a matching is upper-bounded by (|V| + |U| - o(G - U))/2, for any subset U. The following theorem strengthens this result.

Theorem 2 (Tutte-Berge Formula) Let G = (V, E) be a graph. Then

$$\nu(G) = \max_{M} |M| = \min_{U \subset V} (|V| + |U| - o(G - U))/2,$$

where the maximization is over all matchings M in G.

**Proof:** We will consider the case that G is connected. If G is not connected, the result follows by adding the formulas for the individual components. The proof proceeds by induction on the order of G. If G has at most one vertex then the result holds trivially. Otherwise, suppose that G has at least two vertices. We consider two cases.

Case 1: G contains a vertex v that is covered by all maximum matchings. The subgraph G-v cannot have a matching of size  $\nu(G)$ , otherwise that would give a maximum matching for G that leaves v unmatched. Thus  $\nu(G-v)=\nu(G)-1$ . By induction the result holds for the graph

G-v, so there exists a set  $U' \subset V-v$  that achieves equality in the Tutte-Berge Formula. Defining  $U=U'\cup\{v\}$ , we see that

$$\begin{split} \nu(G) &= \nu(G-v) + 1 \\ &= (|V-v| + |U'| - o(G-v-U'))/2 + 1 \\ &= ((|V|-1) + (|U|-1) - o(G-U))/2 + 1 \\ &= (|V| + |U| - o(G-U))/2 \end{split}$$

Case 2: For every vertex  $v \in G$ , there is a maximum matching that does not cover v. We will prove that each maximum matching leaves exactly one vertex uncovered. Suppose to the contrary, that is, each maximum matching leaves at least two vertices uncovered. We choose a maximum matching M and its two uncovered vertices u and v such that we minimize d(u,v), the distance between vertices u and v. If d(u,v)=1 then the edge uv can be added to M to obtain a larger matching, which is a contradiction.

Otherwise,  $d(u,v) \geq 2$  so we may fix an intermediate vertex t on some shortest u-v path. By the assumption of the present case, there is a maximum matching N that does not cover t. Furthermore, we may choose N such that its symmetric difference with M is minimal. If N does not cover u then (N,u,t) contradicts our choice of (M,u,v). Thus N covers u and, by symmetry, v as well. Since N and M both leave at least two vertices uncovered, there exists a second vertex  $x \neq t$  that is covered by M but not by N. Let xy be the edge in M that is incident with x. If y is also uncovered by N then N + xy is a larger matching than N, a contradiction. So let yz be the edge in N that is incident with y, and note that  $z \neq x$ . Then N + xy - yz is a maximum matching that does not cover t and has smaller symmetric difference with M than N does. This contradicts our choice of N, so each maximum matching must leave exactly one vertex uncovered. Then v(G) = (|V| - 1)/2. The Tutte-Berge Formula then follows by choosing  $U = \emptyset$ .

A natural question to ask next is: Given a graph G, what is a set  $U \subset V(G)$  giving equality in the Tutte-Berge Formula? Such a set is provided by the **Edmonds-Gallai Decomposition** of G. This decomposition partitions V(G) into three sets: D(G) is the set of all vertices v such that there is some maximum matching that leaves v uncovered, A(G) is the neighbour set of D(G), and C(G) is the set of all remaining vertices.

**Theorem 3** The set U = A(G) gives equality in the Tutte-Berge Formula. The set D(G) contains all vertices in odd components of G-U, and C(G) contains all vertices in even components of G-U.

Let G[D(G)] be the subgraph of G induced by D(G). It turns out that every connected component H of G[D(G)] is factor critical, meaning that H-v has a perfect matching for every  $v \in V(H)$ . Thus for any odd component in G[D(G)] we can actually choose any particular vertex to be left uncovered.

The Edmonds-Gallai Decomposition of a graph can be found as a byproduct of Edmonds' algorithm for finding a maximum matching. Before describing this algorithm, we need some more basic results. Let M be a matching in a graph G. An alternating path (relative to M) is a path P whose edges are alternately in M and not in M. An augmenting path for M is an alternating path with both endvertices uncovered by M. Let M' be the matching obtained by switching M-edges and non-M-edges along path P (i.e.,  $M' = M \triangle E(P)$ ). Then |M'| = |M| + 1, which explains why P is called an augmenting path.

**Theorem 4 (Berge)** M is a maximum matching if and only if G contains no M-augmenting path.

**Proof:** The "only if" direction is trivial, since any augmenting path can be used to increase the size of M. To prove the other direction, suppose that M is not maximum and let N be a maximum matching chosen with minimum symmetric difference with M. Consider the subgraph spanned by

 $M \cup N$ . Each vertex has degree at most 2, so the subgraph is a disjoint union of paths and cycles. There are no cycles or paths with equal number of edges from N and M, since  $N \triangle M$  is minimum. There are no paths with more N-edges than M-edges otherwise N would not be maximum. It follows that every component is an augmenting path for M.

Theorem 4 implies the following approach for finding a maximum matching: start with an empty matching and repeatedly find augmenting paths to increase its size. **Edmonds' Algorithm** uses this approach and gives a specific method for finding augmenting paths. Consider a graph G = (V, E) and a matching M in G. Let X be the set of uncovered vertices in G. To find an augmenting path for M, it will be helpful to define an auxiliary directed graph G' with vertex set V and arc set  $A = \{uv \mid \exists x \in V \text{ such that } ux \in E \text{ and } xv \in M\}$ . Observe that a directed path in G' corresponds to an (even length) alternating path in G. Furthermore, if there is an augmenting path for M then there is a directed path in G' starting at a vertex in X and ending at a neighbour of X. Unfortunately, the converse does not necessarily hold: G may contain a directed path in G' starting at a vertex in X and ending at a neighbour of X that does not correspond to an augmenting path. Such a path must necessarily have a prefix that is a flower, as shown in this figure.

The dotted arcs show a directed path in the auxiliary graph that starts at a vertex in X and ends at a neighbour of set X but does not correspond to an augmenting path. The graph contains flower, which consists of a stem and a blossom. The stem is simply an alternating path and the blossom is an odd-length cycle.

---

#### 18.997 Topics in Combinatorial Optimization

February 5, 2004

### Lecture 2

Lecturer: Michel X. Goemans Scribe: Robert Kleinberg

In this lecture, we will:

- Present Edmonds' algorithm for computing a maximum matching in a (not necessarily bipartite) graph G.
- Use the analysis of the algorithm to derive the Edmonds-Gallai Decomposition Theorem stated in the last lecture.

### 1 Recapitulation

Recall the following essential definitions and facts from the last lecture. A matching in an undirected graph G is a set of edges, no two of which share a common endpoint. Given a graph G and a matching M, a vertex is matched if it is the endpoint of an edge in M, unmatched otherwise; we will often designate the set of unmatched vertices by X. Given a graph G with matching M, an M-alternating path is a path whose edges are alternately in M and not in M. (Here we use path to mean a simple path, i.e. one with no repeated vertices. We'll refer to a non-simple path as a walk.) If both endpoints of an M-alternating path belong to the set X of unmatched vertices, it is called an M-augmenting path. Recall the following theorem from last time.

**Theorem 1** A matching M is of maximum size if and only if G contains no M-augmenting path.

Figure 1: An M-augmenting path

## 2 Flowers, Stems, and Blossoms

The following construction is useful for finding M-augmenting paths. Given a graph G = (V, E) with matching M; construct a directed graph  $\hat{G} = (V, A)$  with the same vertex set as G, and with edge set determined by the rule that  $(u, w) \in A$  if and only if there exists v with  $(u, v) \in E \setminus M$ ,  $(v, w) \in M$ . Observe that every M-augmenting path in G corresponds to a path in  $\hat{G}$  which begins at a vertex in X and ends at a neighbor of X. However, the converse is not true, because an M-alternating walk may begin at a vertex in X and end at a neighbor of X, without being an M-augmenting path, if it contains an odd cycle. Figure 2 illustrates an example of such a walk. This motivates the following definition.

**Definition 1** An M-flower is an M-alternating walk  $v_0, v_1, v_2, \ldots, v_t$  (numbered so that  $(v_{2k-1}, v_{2k}) \in M$ ,  $(v_{2k}, v_{2k+1}) \notin M$ ) satisfying:

1.  $v_0 \in X$ .

Figure 2: An M-flower

- 2.  $v_0, v_1, v_2, \dots, v_{t-1}$  are distinct.
- 3. t is odd.
- 4.  $v_t = v_i$ , i even.

The portion of the flower from  $v_0$  to  $v_i$  is called the stem, while the portion from  $v_i$  to  $v_t$  is called the blossom.

**Lemma 2** Let M be a matching in G, and let  $P = (v_0, v_1, \ldots, v_t)$  be a shortest alternating walk from X to X. Then either P is an M-augmenting path, or  $v_0, v_1, \ldots, v_j$  is an M-flower for some j < t.

**Proof:** If  $v_0, v_1, \ldots, v_t$  are all distinct, P is an M-augmenting path. Otherwise, assume  $v_i = v_j, i < j$ , and let j be as small as possible, so that  $v_0, v_1, \ldots, v_{j-1}$  are all distinct. We shall prove that  $v_0, v_1, \ldots, v_j$  is an M-flower. Properties 1 and 2 of a flower are automatic, by construction. It cannot be the case that j is even, since then  $(v_{j-1}, v_j) \in M$ , which gives a contradiction in both of the following cases.

- i = 0:  $(v_{i-1}, v_i) \in M$  contradicts  $v_0 \in X$ .
- 0 < i < j-1:  $(v_{j-1}, v_j) \in M$  contradicts the fact that M is a matching, since  $v_i$  is already matched to a vertex other than  $v_{j-1}$ .

This proves that j is odd. It remains to show that i is even. Assume, by contradiction, that i is odd. Then  $v_{j+1} = v_{i+1}$  (since both are equal to the other endpoint of the matching edge containing  $v_j = v_i$ ), and we may delete the cycle from P to obtain a shorter alternating walk from X to X. (See Figure 3.)

Given a flower  $F = (v_0, v_1, \dots, v_t)$  with blossom B, observe that for any vertex  $v_j \in B$  it is possible to modify M to a matching M' satisfying:

- 1. Every vertex of F belongs to an edge of M' except  $v_i$ .
- 2. M' agrees with M outside of F, i.e.  $M \triangle M' \subseteq F$ .
- 3. |M'| = |M|.

Figure 3: An alternating walk from X to X which can be shortened.

To do so, we take M' to consist of all the edges of the stem which do not belong to M, together with a matching in the blossom which covers every vertex except  $v_i$ .

Whenever a graph G with matching M contains a blossom B, we may simplify the graph by shrinking B, a process which we now define.

**Definition 2 (Shrinking a blossom)** Given a graph G = (V, E) with a matching M and a blossom B, the shrunk graph G/B with matching M/B is defined as follows:

- $V(G/B) = (V \setminus B) \cup \{b\}$
- $E(G/B) = E \setminus E[B]$
- $M/B = M \setminus E[B]$

where E[B] denotes the set of edges within B, and b is a new vertex disjoint from V.

Observe that M/B is a matching in G, because the definition of a blossom precludes the possibility that M contains more than one edge with one but not both endpoints in B. Observe also that G/B may contain parallel edges between vertices, if G contains a vertex which is joined to B by more than one edge.

The relation between matchings in G and matchings in G/B is summarized by the following theorem.

**Theorem 3** M is a maximum size matching in G if and only if M/B is a maximum size matching in G/B.

**Proof:** ( $\Longrightarrow$ ) Suppose N is a matching in G/B larger than M/B. Pulling N back to a set of edges in G, it is incident to at most one vertex of B. Expand this to a matching in  $N^+$  in G by adjoining  $\frac{1}{2}(|B|-1)$  edges to match every other vertex in B. Then  $|N^+|$  exceeds |M| by the same amount that |N| exceeds |M/B|.

( $\Leftarrow$ ) If M is not of maximum size, then change it to another matching M', of equal cardinality, in which B is an entire flower. (If S is the stem of the flower whose blossom is B, then we may take  $M' = M \triangle S$ .) Note that M'/B is of the same cardinality as M/B, and b is an unmatched vertex of M'/B. Since M' is not a maximum size matching in G, there exists an M'-augmenting path P. At least one of the endpoints of P is not in B. So number the vertices of P  $u_0, u_1, \ldots, u_t$  with  $u_0 \notin B$ , and let  $u_i$  be the first node on P which is in B. (If there is no such node, then  $u_i = u_t$ .) This sub-path  $u_0, u_1, \ldots, u_i$  is an (M'/B)-augmenting path in G/B.

```
M := \emptyset
X := \{\text{unmatched vertices}\}\
Form the directed graph \hat{G}.
while \hat{G} contains a directed path \hat{P} from X to N(X)
    Find such a path \hat{P} of minimum length.
    P := the alternating path in G corresponding to \tilde{P}
    if P is an M-augmenting path,
        modify M by augmenting along P.
    else
        P contains a blossom B.
        Recursively find a maximum size matching M' in G/B.
        if |M'| = |M/B| /* M is already a max matching. */
                            /* Done! */
            return M
                            /* M can be enlarged */
        else
            Unshrink M' as in the proof of Theorem 3,
             to obtain a matching in G of size > |M|.
end
```

Figure 4: Algorithm for computing a maximum matching

### 3 A polynomial-time maximum matching algorithm

The algorithm for computing a maximum matching is specified in Figure 4.

The correctness of the algorithm is established by Lemma 2 and Theorem 3. The running time may be analyzed as follows. We can compute X and  $\hat{G}$  in linear time, we can find  $\hat{P}$  in linear time (by breadth-first search), and we can shrink a blossom in linear time. We can only perform O(n) such shrinkings before terminating or increasing |M|. The number of times we increase |M| is O(n). Therefore the algorithm's running time is  $O(mn^2)$ . With a little more work, this can be improved to  $O(n^3)$ . (See Schrijver's book.) The fastest known algorithm, due to Micali and Vazirani, runs in time  $O(\sqrt{n} m)$ .

# 4 Combinatorial consequences of the algorithm

Our aim now is to use the analysis of the algorithm to derive the following two combinatorial theorems, both of which were asserted in the last lecture.

**Theorem 4 (Tutte-Berge Formula)** For a graph G and a set of vertices  $U \subseteq V(G)$ , let  $c_o(G \setminus U)$  denote the number of odd components of the graph  $G \setminus U$ , i.e. the number of components with an odd number of vertices. Then the cardinality of a maximum size matching,  $\nu(G)$ , satisfies:

$$\nu(G) = \min_{U \subseteq V} \frac{1}{2} [|V| + |U| - c_o(G \setminus U)]. \tag{1}$$

Theorem 5 (Edmonds-Gallai Decomposition) Given a graph G, let

```
D(G) := \{v : \exists \ a \ maximum \ size \ matching \ missing \ v\}

A(G) := N(D(G))

C(G) := V(G) \setminus (D(G) \cup A(G))
```

Figure 5: Edmonds-Gallai Decomposition

Then U = A(G) achieves the minimum on the right side of the Tutte-Berge formula, D(G) is the union of the odd components of  $G \setminus A(G)$ , and C(G) is the union of the even components of  $G \setminus A(G)$ . Moreover, every odd component of  $G \setminus A(G)$  is factor-critical. (A graph H is factor-critical if for every vertex v, there is a matching in H whose only unmatched vertex is v.)

To prove these theorems, consider a maximum size matching M in G, take an unmatched vertex  $x \in X$ , and consider all the vertices which can be reached by an alternating path from x. The first edge on such a path must lie outside of M, the second edge must lie in M, and so on, leading to a picture as in Figure 6.

Figure 6: Vertices reachable by alternating paths from x.

Motivated by this picture, we make the define the following three subsets of V(G):

Even :=  $\{v : \exists \text{ an alternating path of even length from } X \text{ to } v\}$ 

Odd :=  $\{v : \exists \text{ an alternating path from } X \text{ to } v\} \setminus \text{Even}$ 

Free :=  $\{v : \exists \text{ an alternating path from } X \text{ to } v\}$ 

We will sometimes refer to a vertex as being even, odd, or free, according to which of these sets it belongs to.

**Claim 6** If there is an edge from Even to v, then there is an alternating walk of odd length from X to v, and there is an alternating path from X to v.

**Proof:** If e = (u, v) is an edge between Even and v, and P is an alternating path of even length from X to u, then an alternating walk of odd length from X to v is constructed as follows. If  $e \in M$ , then we take P and delete the final edge, which is necessarily e. If  $e \notin M$ , then we append e to P. If this alternating walk is not a path, it can only be because v lies on P, in which case P contains a sub-path which is an alternating path from X to v.

Corollary 7 In G there is no edge between Even and Free.

Define the shrunk graph  $G_0$  to be the graph obtained at the innermost level of the recursion in the matching algorithm given above, on the final iteration of the **while** loop. Let  $M_0$  be the maximum size matching in  $G_0$  computed by the algorithm. Since  $G_0$  has no flowers, and  $M_0$  is a maximum matching, it follows that  $G_0$  has no alternating walk from X to X.

Claim 8 In  $G_0$ , there is no edge between two vertices in Even.

**Proof:** If such an edge e = (u, v) exists, then by Claim 6,  $G_0$  contains an alternating walk P of odd length from X to v. But v is even, so there is also an alternating path P' of even length from X to v. Concatenating P with the reverse of P', we obtain an alternating walk from X to X, contradicting the definition of  $G_0$ .

It is worth noting that Claim 8 doesn't necessarily hold in G. This is because all the vertices of a blossom are even. (The stem is an even-length alternating path from X to one vertex v of the blossom, and all other vertices of the blossom are reachable from v by an even-length alternating path which goes around the blossom either clockwise or counter-clockwise.)

Claim 9 Even =  $D(G) = \{v : \exists \ a \ maximum\text{-size matching missing } v\}.$ 

**Proof:** Certainly if v is even then there a maximum-size matching M' missing v. Such a matching is obtained by taking an even-length alternating path P from X to v and putting  $M' = M \triangle P$ . Conversely, if there exists a maximum-size matching M' missing v, then  $M \triangle M'$  is a union of even-length cycles and paths, and v is an endpoint of one of these paths, because it does not belong to an edge of M'. The other endpoint of this path P does not belong to an edge of M, i.e. it is an element of X. This confirms that P is an even-length alternating path from X to v.

**Claim 10** Odd = A(G) = N(D(G)).

**Proof:** If v is odd, then there is an alternating path of odd length from X to v. The vertex preceding v on this path must be even, which confirms that  $\mathsf{Odd} \subseteq N(\mathsf{Even}) = N(D(G))$ . The reverse inclusion follows from Claim 6, which ensures that every vertex adjacent to Even belongs to Even  $\cup$  Odd.

Claim 11 Free =  $C(G) = V(G) \setminus (D(G) \cup A(G))$ .

**Proof:** Immediate from the definition of Free, and from the preceding two claims which identify Even, Odd with D(G), A(G), respectively.

**Claim 12** In  $G_0$ , every free vertex is matched to another free vertex by M, and every odd vertex is matched to an even vertex by M.

**Proof:** Every vertex which is free or odd is incident to an edge of M, because no such vertex may belong to X. If e = (u, v) is an edge of M with u odd, and if P is an odd-length alternating path from  $x \in X$  to u, then  $P \cup \{e\}$  is an even-length alternating path from X to v. (It is not possible that  $v \in P$  because  $v \notin X$  and every vertex in  $P \setminus \{x\}$  is already matched to a vertex of P other than u.) This proves that every odd vertex is matched to an even vertex. That means a free vertex may not be matched to an odd vertex, but it also may not be matched to an even vertex (by Corollary 7), so every free vertex is matched to another free vertex.

Claim 13 Every component of  $G \setminus A(G)$  is a subset of either D(G) or C(G). The even-cardinality components are subsets of C(G), while the odd-cardinality components are subsets of D(G). Moreover, if M is a maximum-size matching in G, then every component H of D(G) satisfies one of the following:

- $|X \cap H| = 1$ , and  $M \cap \delta(H) = \emptyset$ . (The coboundary of a vertex set U, denoted by  $\delta(U)$ , is the set of edges with exactly one endpoint in U.)
- $X \cap H = \emptyset$ ,  $M \cap \delta(H)$  contains exactly one edge, and this edge joins H to A(G).

**Proof:** The proof is by induction on the number of blossoms which are shrunk during the execution of the maximum matching algorithm. If no blossoms are shrunk, then  $G = G_0$ , and the claim is a consequence of the following observations:

- 1. If u is an even vertex of  $G_0$ , then every neighbor of u is in  $Odd = A(G_0)$ . (By Corollary 7 and Claim 8.)
- 2. Therefore every vertex u in Even =  $D(G_0)$  is an isolated vertex of  $G_0 \setminus A(G_0)$ . Moreover, u either belongs to X, or is joined to  $A(G_0)$  by an edge of M.
- 3. For every component H of Free  $= C(G_0)$ , the edge set  $M \cap E[H]$  is a perfect matching in H. (By Claim 12.)

Now for the induction step, suppose B is a blossom in G and that the claim holds for G/B. Then B corresponds to a vertex  $b \in G/B$  which is an even vertex in some component  $H_b$  of D(G/B). (The stem of the flower containing B corresponds to an even-length alternating path from X to b in G/B.) When we inflate b to B, we claim that:

- 1. Except for b, all even vertices of G/B remain even. All vertices of B are also even in G.
- 2. All odd vertices of G/B remain odd.
- 3. All free vertices of G/B remain free.

If these are true, then we'll be done, because this says that inflating b to B doesn't change the set A(G), and it doesn't change the components of  $G \setminus A(G)$  except that a vertex of  $H_b$  inflates into an odd cycle. Note that this doesn't change the parity of  $|V(H_b)|$ . Also, inflating b to B doesn't change the number of unmatched vertices in  $H_b$ , nor does it change the number of matching edges in  $\delta(H)$ .

It remains to prove (1)-(3). For (1), let  $b^* \in B$  denote the vertex where the stem joins the blossom. If  $P = (v_0, v_1, \dots, v_t)$  is an even-length path in G/B with  $v_0 \in X$  and  $v_t \neq b$ , then one of the following cases applies.

- P avoids b. In this case, P is also a path in G, and there is nothing to prove.
- $b = v_s$ , s even. In this case, the sub-path  $(v_0, \ldots, v_s)$  lifts to a path  $P_0 = (v_0, \ldots, v_{s-1}, b^*)$  in G ending with the last edge of the stem. The next edge  $(v_s, v_{s+1})$  corresponds to an edge  $(w, v_{s+1})$  in G, with  $w \in B$ . Let  $P_1$  be an even-length alternating path in B from  $b^*$  to w. We can splice together  $P_0, P_1$ , and the path  $P_2 = (w, v_{s+1}, v_{s+2}, \ldots, v_t)$  to obtain an even-length alternating path in G from  $v_0$  to  $v_t$ .

•  $b = v_s$ , s odd. In this case, the sub-path  $(v_s, \ldots, v_t)$  lifts to a path  $P_2 = (b^*, v_{s+1}, v_{s+2}, \ldots, v_t)$  in G beginning with the last edge of the stem. The desired even-length path in G from  $v_0$  to  $v_t$  is constructed by a splicing process as before, but this time in reverse.

Finally, every vertex w in B is an even vertex of G, because we may obtain an even-length alternating path from X to w by taking the stem and appending an even-length path in B from  $b^*$  to w.

To prove (2) and (3), let  $A^*(G)$  denote the set of vertices in G which are odd vertices of G/B. (We wish to eventually prove that  $A^*(G) = A(G)$ , but for now we will not assume it.) From the induction hypothesis, we have the following characterization of components of  $G \setminus A^*(G)$ : each such component H satisfies

- 1. |V(H)| is even.  $X \cap H = \emptyset$ , and  $M \cap \delta(H) = \emptyset$ .
- 2. |V(H)| is odd.  $|X \cap H| = 1$ , and  $M \cap \delta(H) = \emptyset$ , or
- 3. |V(H)| is odd.  $X \cap H = \emptyset$ , and  $M \cap \delta H$  consists of a single edge joining H to  $A^*(G)$ .

Components of the first two types will be called inaccessible. Components of the third type will be called accessible, and the edge  $M \cap \delta(H)$  will be called the gateway to such a component. The terminology is justified by the following characterization of alternating paths in G which begin at a vertex  $x \in X$ : such a path P does not visit any inaccessible component except for the one containing x, and if P visits an accessible component H, then it reaches H by traversing the gateway edge. The proof is by contradiction: if not, let  $H_0$  be the first component of  $G \setminus A^*(G)$  not containing x which is reached by traversing an edge  $e = (v, w) \notin M$ . We must have  $u \in A^*(G)$  since there are no edges between distinct components of  $G \setminus A^*(G)$ . The edge preceding e in P is an edge  $e' = (u, v) \in M$ . Since  $u \in A^*(G)$ , e' is a gateway edge and v belongs to some other component  $H_1$  of  $G \setminus A^*(G)$ . P could not have reached  $H_1$  by traversing e' (since it is a simple path, and it exits  $H_1$  by traversing e'), so it must have reached  $H_1$  via a non-gateway edge, contradicting the fact that  $H_0$  was the first such component.

This characterization of alternating paths in G immediately proves (3), since components of  $G \setminus A^*(G)$  corresponding to free vertices of G/B satisfy (3) and are inaccessible. To see that it also proves (2), consider any  $v \in A^*(G)$ . In G/B there is an alternating path of odd length from X to v; this is also an alternating path in G, so all that remains is to show that G contains no alternating path of even length from X to v. Let e = (u, v) be the edge of M containing v. If P is an alternating path of even length from X to v, then e must be the last edge of P. But u belongs to an accessible component H, and e is its gateway edge. But this means the only way for P to reach H is to traverse e (because P starts in X, and  $X \cap H = \emptyset$ ), and this contradicts the fact that P is a simple path.

Claim 14  $|M| = \frac{1}{2} [|V| + |A(G)| - c_o(G \setminus A(G))].$ 

**Proof:** Every vertex in  $V \setminus X$  belongs to one and only one edge in M, so

$$|M| = \frac{1}{2} (|V| - |X|).$$
 (2)

Now, Claim 13, establishes that each odd component H of  $G \setminus A(G)$  satisfies one of the following two criteria:

- $|X \cap H| = 1$ ,  $M \cap \delta(H) = \emptyset$ .
- $X \cap H = \emptyset$ , and  $M \cap \delta(H)$  consists of a single edge joining H to A(G). (Moreover, every vertex in A(G) is an endpoint of exactly one such edge.)

Hence,

$$c_o(G) = |X| + |A(G)|.$$
 (3)

Combining (2) and (3) we obtain the desired formula.

This claim establishes that

$$\nu(G) \ge \min_{U \subseteq V} \frac{1}{2} \left[ |V| + |U| - c_o(G \setminus U) \right].$$

The reverse inequality is trivial, so we have proved the Tutte-Berge formula. Note that we have also established all of the claims in the Edmonds-Gallai Decomposition Theorem, except for the assertion that every component of D(G) is factor-critical. This part of the theorem will be addressed in the next lecture.

---

| 18.997 Topics in Combinatorial Optimization | February 10th, 2004  |
|---------------------------------------------|----------------------|
| Lecture 3                                   |                      |
| Lecturer: Michel X. Goemans                 | Scribe: Dan Stratila |

In this lecture we will cover:

- 1. Topics related to Edmonds-Gallai decompositions ([Sch03], Chapter 24).
- 2. Factor critical-graphs and ear-decompositions ([Sch03], Chapter 24).

Topics mentioned but covered during subsequent lectures are:

- 1. The matching polytope ([Sch03], Chapter 25).
- 2. Total Dual Integrality (TDI) and the Cunningham-Marsh formula ([Sch03], Chapter 25).

A detailed reference on matchings is the book *Matching Theory* by Lovasz and Plummer, [LP86].

## 1 Petersen's Theorem

Before stating Petersen's theorem, we recall that a graph is called *cubic* if each of its vertices has degree exactly 3, and *bridgeless* if it cannot be disconnected by deleting any one edge (in other words any pair of vertices has edge connectivity at least 2).

Figure 1: A bridgeless cubic graph and a perfect matching on it. Edges in the matching are bold.

**Theorem 1 (Petersen)** Any bridgeless cubic graph has a perfect matching.

**Proof:** We will show that for any  $V \subseteq U$ , we have  $c_o(G - U) \leq |U|$  (here  $c_o(G)$  is the number of odd components of the graph G). The theorem will then follow from the Tutte-Berge formula.

Consider an arbitrary  $U \subset V$ . Each odd component of G - U is left by an odd number of edges, since G is cubic. Since G is also bridgeless each component is left by at least 2 edges, hence by at least 3 edges. On the other hand, the set of edges leaving all odd components of G - U is a subset of the edges leaving U, and there are at most 3|U| edges

Figure 2: Illustration of the proof of Petersen's theorem. Edges inside U and  $C_i$ , as well as between  $C_4, C_5$  and U are omitted.

leaving U, since G is cubic. Among these 3|U| edges, there are at least 3 edges per each odd component, therefore there are at most |U| odd components. (See Figure 2.)

A bridgeless cubic graph and a perfect matching for it are shown in Figure 1.

Although any bridgeless cubic graph has a perfect matching, it is not true that any such graph can be decomposed into 3 perfect matchings. An example of this is the Petersen graph, depicted in Figure 3.

Figure 3: The Petersen graph.

## 1.1 Colorings and matchings

However, we can cover all edges of any bridgeless cubic graph with 4 matchings, as shown by the following theorem. (Note that a coloring is an assignment of colors to edges such

that edges sharing a vertex have different colors. Thus, a k-coloring is the same as covering all edges with k, not necessarily perfect, matchings.)

**Theorem 2 (Vizing, 1964)** For any graph, there is an edge coloring with at most  $\Delta + 1$  colors, where  $\Delta := \max_{v \in V} \deg(v)$  is the maximum degree of any vertex in G.

In fact, Holyer (1981) has shown that it is NP-complete to decide whether a given cubic graph is 3-colorable. It is also NP-complete to find the edge-coloring number of a k-regular graph, for each  $k \geq 3$  (Leven and Galil, 1983).

The following theorem is a particularly appealing result relating matchings and colorings.

**Theorem 3 (Tait, 1878)** Each planar cubic bridgeless can be decomposed into 3 matchings if and only if the 4-color conjecture holds.

Since the 4-color conjecture is now a theorem with a complicated proof, an easy proof of Tait's theorem is of interest.

Conjecture 1 (Fulkerson) For any bridgeless cubic graph there is exist 6 perfect matchings that cover each edge exactly twice.

More conjectures can be found in Chapter 28 of [Sch03], entirely devoted to edge-colorings.

## 2 Ear decompositions

Before proceeding to describe results about ear decompositions, we review a result on factor-critical graphs.

**Definition 1** A graph G is factor-critical if for any vertex  $v \in V$ , G - v has a perfect matching.

As before, let D(G) be the set of vertices missed by some maximum-size matching, let  $A(G) := N(D(G)) = \{v : \exists w \in U, \{v, w\} \in E\}$  be the set of all vertices neighboring vertices in D(G), and let  $C(G) := V \setminus (D(G) \cup A(G))$  contain all other vertices. Recall from Lecture 1 that U := A(G) attains the minimum in the Tutte-Berge formula, D(G) is the union of the odd components of G - U, and C(G) is the union of even components of G - U.

**Claim 4** Each odd connected component of G - A(G) is factor-critical.

**Proof:** We will give a proof that relies on Edmond's algorithm. First, recall from Lecture 2 that D(G) is the set of even vertices of the final forest, hence A(G) is the set of odd vertices. Since there are no edges between even vertices in the final forest, each odd component of G - A(G) is represented in the final graph by an even vertex.

So it suffices to show that any graph obtained by a series of blossom operations starting from a single vertex is factor-critical, and we do this by induction. Clearly, the original vertex is factor-critical (the first blossom, being an odd cycle is also factor-critical).

Now, assume that G/B, obtained from G by shrinking B, is factor-critical. If  $v \notin B$ , then G has a maximum matching that missing v, because G/B has one and it can be

completed by appropriately ading edges of B. If  $v \in B$ , then we can obtain a maximum matching in G that misses v by taking a maximum matching in G/B that misses B (such a matching exists since G/B is factor-critical), and then taking a maximum matching on B that misses v. Therefore G is factor-critical.

An ear decomposition  $G_0, G_1, \ldots, G_k = G$  of a graph G is a sequence of graphs with the first graph being simple (e.g. a vertex, edge, even cycle, or odd cycle), and each graph  $G_{i+1}$  obtained from  $G_i$  by adding an ear. Adding an ear is done as follows: take two vertices a and b of  $G_i$  and add a path  $P_i$  from a to b such that all vertices on the path except a and b are new vertices (present in  $G_{i+1}$  but not in  $G_i$ ). An ear with  $a \neq b$  is called proper (or open), and an ear with  $P_i$  having an odd (even) number of edges is called odd (even). (See Figure 4.) Several basic properties of graphs can be translated into the existence of an ear decomposition of a certain kind. Here are some examples.

Figure 4: An even proper ear added to  $G_i$ .

**Theorem 5 (Robbins, 1939 (implicit))** G is 2-connected if and only if G has a proper ear decomposition starting from a cycle.

**Proof:** Obviously, any graph that has a proper ear decomposition starting from a cycle is 2-connected.

Conversely, we assume G is 2-connected, and will show by induction how to construct it starting from a cycle. First, since G is 2-connected, it contains at least one cycle, which we can take as the initial cycle.

Now, suppose we have constructed a subgraph G' of G. If V(G') = V(G) and we are only missing edges, then we can add these edges as proper ears of length one. If  $V(G') \subset V(G)$ , then pick a vertex  $v \in V(G) \setminus V(G')$ . Since G is connected, there is a path P from some  $a \in V(G)$  to v; since G is 2-connected, there is a path Q distinct from P from V back to some vertex  $b \in V(G')$ ,  $b \neq a$ . Hence the paths P and Q form a proper ear from A to B containing at least one new vertex.

**Theorem 6** G is factor-critical if and only if G has an odd ear decomposition starting from an odd cycle.

**Proof:** If G has an odd ear decomposition, then it is factor critical, since blossoming yields a factor critical graph.

Conversely, suppose G is factor-critical. First, we establish the existence of an initial odd cycle. For any v, fix a near-perfect matching  $M_v$  that misses v. Then for an edge (u, v)

the existence of  $M_u$  and  $M_v$  implies there is an alternating even path from v to u. By adding (u, v) to it we obtain an odd cycle.

Fix a vertex v. We proceed by induction; let H be the vertex set already covered by the odd ear decomposition such that no edge in  $M_v$  crosses H. Since G is connected, there is an edge  $(a,b), a \in H, b \notin H, (a,b) \notin M_v$ . Moreover,  $M_b \triangle M_v$  contains an alternating path Q from b back to v. The first edge (w,u) to cross back into H on Q is not in  $M_v$ , by the construction of H. Therefore, we obtain an odd path from b to u, and can increase the size of H.

The two results can be combined. One can show that G is factor-critical and 2-connected if and only it has a proper ear decomposition starting from an odd cycle.

Here is another ear decomposition result. A bipartite ear decomposition starts from an even cycle, and adds an odd length path between vertices of different color. As a result, the graph stays bipartite. **Question:** G is  $\_\_$  if and only if it has a bipartite ear decomposition. What is  $\_\_$ ? (Answer at end of lecture.)

Here is a result on factor-critical graphs which can be used to characterize the facets of teh matching polytope.

**Theorem 7** Let G be a 2-connected factor-critical graph. Then the number of near-perfect matchings is at least |E(G)|.

**Proof:** We proceed by induction on the number of odd ears. Consider a graph G', and G obtained from G' by adding an odd ear  $P = (u_0, \ldots, u_k)$  of k edges. Then |V(G)| = |V(G')| + k - 1, |E(G)| = |E(G')| + k.

We can obtain |E(G')| near-perfect matchings by taking  $(u_1, u_2), \ldots, (u_{k-2}, u_{k-1})$  into the matching, and then generating |E(G')| near perfect matchings in G'. Moreover, we can obtain k-1 by matching all vertices on P except  $u_j, j=1,\ldots,k$ , and then taking a near-perfect matching on G' that misses either  $u_0$  (if j is odd) or  $u_k$  (if j is even). The final matching is obtained by taking the matching missing  $u_k$ , but not  $u_0$ , removing the edge matching  $u_k$  in G' and adding the edge matching  $u_k$  in P.

We note without further discussion that the number of affinely independent near-perfect matchings is equal to |E(G)|.

**Answer:** \_\_\_ is that every edge is in a perfect matching.

## References

- [LP86] L. Lovász and M. D. Plummer. Matching theory, volume 121 of North-Holland Mathematics Studies. North-Holland Publishing Co., Amsterdam, 1986. Annals of Discrete Mathematics, 29.
- [Sch03] Alexander Schrijver. Combinatorial optimization. Polyhedra and efficiency. Vol. A, volume 24 of Algorithms and Combinatorics. Springer-Verlag, Berlin, 2003. Paths, flows, matchings, Chapters 1–38.

---

| 18.997 | <b>Topics</b> | in | Combinatorial | O. | ptimization |
|--------|---------------|----|---------------|----|-------------|
|--------|---------------|----|---------------|----|-------------|

February 12, 2004

Lecture 4

Lecturer: Michel X. Goemans Scribe: Constantine Caramanis

This lecture covers: the Matching polytope, total dual integrality, and Hilbert bases.

## 1 The Matching Polytope and Total Dual Integrality

In this section we introduce the matching polytope as the convex hull of incidence vectors of matchings. Next, we give a linear description of the matching polytope, and prove that the linear description is correct by introducing the concept of Total Dual Integrality (TDI).

Given a graph G = (V, E), and a matching M on G, we can identify M with its incidence vector:

$$\chi^M \in \mathbb{R}^{|E|} \quad : \quad \chi^M_e = \left\{ \begin{array}{ll} 1 & e \in M \\ 0 & \text{otherwise} \end{array} \right.$$

We define the matching polytope  $\mathcal{P} = \mathcal{P}(G)$  to be the convex hull of these incidence vectors:

$$\mathcal{P}(G) = \operatorname{conv}\{\chi^M : M \text{ a matching of } G.\}$$

We wish to obtain a linear description of  $\mathcal{P} \subseteq \mathbb{R}^{|E|}$ . We must have  $x_e \geq 0$  for  $e \in E$ . Also, every vertex can have at most one adjacent edge in any matching, and thus

$$x(\delta(v)) \stackrel{\triangle}{=} \sum_{e \in \delta(v)} x_e \le 1.$$

Thus our first attempt at a linear description is:

$$P^{1} = \left\{ \begin{array}{ll} x_{e} \geq 0 & \forall e \in E \\ x(\delta(v)) \leq 1 & \forall v \in V \end{array} \right\}$$

Consider the triangle, with edges labelled {1, 2, 3}. In this case, the matching polytope is

$$\mathcal{P} = \text{conv}\{(0,0,0), (1,0,0), (0,1,0), (0,0,1)\}.$$

The point (1/2, 1/2, 1/2) is in  $P^1$ , i.e., it satisfies the constraints above, however it is not in the convex hull of the matching vectors. This example motivates the following family of constraints.

Observe that for any matching M, any odd cardinality subset U can have at most (|U|-1)/2 edges. Thus we have the additional constraints

$$x(E(U)) = \sum_{e \in E(U)} x_e \le \frac{|U| - 1}{2}, \qquad U \subseteq V, \ |U| \text{ odd,}$$

which we call the odd subgraph constraints. For the triangle, taking U to be the graph itself, we get the constraint  $x_1 + x_2 + x_3 \le 1$ . This constraint is violated by the point (1/2, 1/2, 1/2). As a second attempt at a linear description of the matching polytope we have:

$$P^{2} = \left\{ \begin{array}{ll} x_{e} \geq 0 & \forall e \in E \\ x(\delta(v)) \leq 1 & \forall v \in V \\ x(E(U)) \leq \frac{|U|-1}{2} & U \subseteq V, \ |U| \text{ odd} \end{array} \right\}$$

**Theorem 1 (Edmonds, 1965)** The linear description  $P^2$  is in fact the Matching polytope, i.e.,  $\mathcal{P} = P^2$ .

**Proof:** Edmonds gave an algorithmic proof: For any given weight vector, w, he argued that the optimization over  $P^2$  gives the same maximum weighted matching as the actual solution. The algorithm uses shrinking and expanding of blossoms. It is in Chapter 27 of Schrijver's book.  $\Box$  Rather than give Edmonds's algorithmic solution, we introduce the concept of Total Dual Integrality (TDI). This, in addition to Total Unimodularity, is further explored in Lecture 5.

Recall the primal and dual standard formulation of an LP.

$$(\text{Primal } (P)) \quad \left\{ \begin{array}{l} \max: \ c^{\top}x \\ \text{s.t.}: \quad Ax \leq b \end{array} \right\} \longleftrightarrow \left\{ \begin{array}{l} \min: \ b^{\top}y \\ \text{s.t.}: \quad A^{\top}y = c \end{array} \right\}$$

We define Total Dual Integrality as follows:

**Definition 1 (TDI)** A polyhedron defined by a system of inequalities  $\{x : Ax \leq b\}$  (with A and b rational) is Total Dual Integral (TDI) if for any integral cost vector c to the primal problem, if the associated dual

$$\begin{aligned} & min: & b^\top y \\ & s.t.: & A^\top y = c \\ & y \geq 0 \end{aligned}$$

has a finite optimal value, then it also has an integral solution  $y^*$ .

We now state the main theorem about TDI polytopes. We save the proof for the next lecture.

**Theorem 2 (Edmonds-Giles, 1978)** If the system  $\{Ax \leq b\}$  is TDI, and b is integral, then the polytope  $\{Ax \leq b\}$  is integral, i.e., all vertices are integral.

Total Dual Integrality is a property of the representation of the polyhedron. To illustrate this point, consider the two dimensional polytope

$$\mathcal{P} = \text{conv}\{(0,3), (2,2), (0,0), (3,0)\}$$

This polytope may have many different representations. For example,

$$\mathcal{P} = \left\{ \begin{array}{l} x_1 \ge 0, \ x_2 \ge 0 \\ x_1 + 2x_2 \le 6 \\ 2x_2 + x_1 \le 6 \end{array} \right\}$$

While the polytope is, evidently, integral, the system given is not TDI. For example, consider c = (1, 1). The dual to

is the linear program

min:  $6y_1 + 6y_2$ s.t.:  $y_1 + 2y_2 \ge 1$   $2y_1 + y_2 \ge 1$  $y_1, y_2 > 0$ 

The dual optimal value is finite, however there are no integral optimal points. The dual tries to express (1,1) as a positive linear combination of the vectors (1,2) and (2,1). This cannot be done as an integral linear combination. From this example, we see that in order for the dual to have an integral optimal solution, we must be able to express any integral vector in the dual cone  $\mathcal{C}$  (as in the figure below) as an integral combination of some set of vectors.

**Definition 2** Given a rational (i.e. of the form  $\{x : Ax \leq 0\}$  with A rational) cone C, the minimal set of vectors such that any integral point in C can be expressed as an integral nonnegative linear combination of vectors in the set, is called a Hilbert Basis for the cone.

For the cone defined by the vectors (1,2) and (2,1), a Hilbert basis is given by the set of vectors  $H = \{(1,2),(2,1),(1,1)\}$ . We can get the additional vector (1,1) by adding the redundant constraint  $x_1 + x_2 \le 4$  in the primal. Therefore, the linear system

$$\left\{
\begin{array}{l}
x_1, x_2 \ge 0 \\
x_1 + 2x_2 \le 6 \\
2x_1 + x_2 \le 6 \\
x_1 + x_2 \le 4
\end{array}
\right\}$$

is TDI.

**Remark**: Any rational cone has a finite Hilbert basis. This does not necessarily hold for all irrational cones.

**Theorem 3** For P a rational polyhedron, there exists a TDI system  $\{Ax \leq b\}$  such that  $P = \{x : Ax \leq b\}$ . Furthermore, the polytope P is integral if and only if we can take b to be integral.

The primal form of the statement says that if P is a rational polyhedron such that  $\max\{c^{\top}x:x\in P\}$  is integral for every integral vector c, then the polyhedron is integral.

Suppose that for every rational supporting hyperplane (i.e., for every  $\alpha, \beta$  such that  $\alpha^{\top} x \leq \beta$  for every  $x \in P$ , and  $\{\alpha^{\top} x = \beta\} \cap P \neq \emptyset$ ) there exists an integer point on the hyperplane. Then, the polytope is integral.

This gives us an analog of Farkas's lemma: The system Ax = b has no integral solution if and only if  $A^{\top}y$  integral and  $b^{\top}y$  non-integral has a solution.

---

| 18.997 Topics in Combinatorial Optimization | February 24th, 2004 |
|---------------------------------------------|---------------------|
| Lecture 5                                   |                     |
| Lecturer: Michel X. Goemans                 | Scribe: Ben Recht   |

In this lecture, we investigate the relationship between total dual integrality and integrality of polytopes. We then use a theorem on total dual integrality to provide a new proof of the Tutte-Berge formula.

## 1 Total Dual Integrality

Consider the linear program defined as

$$\begin{array}{ll}
\max & c^{\top} x \\
\text{s.t.} & Ax < b
\end{array} \tag{1}$$

where A and b are rational and the associate dual program

$$\begin{array}{ll}
\min & y^{\top} b \\
\text{s.t.} & A^{\top} y = c \\
& y \ge 0
\end{array} \tag{2}$$

**Definition 1** The system of inequalities by  $Ax \leq b$  is Total Dual Integral or TDI if for all integral vectors c the dual program has an integral solution whenever the optimal value is finite.

The main result for today is

**Theorem 1** If  $Ax \leq b$  is TDI and b is integral then  $P = \{x : Ax \leq b\}$  is integral

**Proof:** We proceed by contradiction. Consider a vertex  $x^*$  of P such that  $x_j^* \notin \mathbb{Z}$ . We can construct an integral c such that  $x^*$  is the optimal solution corresponding to c by picking a rational c in the optimal cone of  $x^*$  and scaling. Consider  $\hat{c} = c + \frac{1}{q}e_j$  where q is an integer. Since the cone is full dimensional,  $\hat{c}$  will still be in the optimality cone of  $x^*$  for q sufficiently large. Now it follows that  $q\hat{c} = qc + e_j$  and thus  $(q\hat{c})^{\top}x^* - (qc)^{\top}x^* = x_j^* \notin \mathbb{Z}$ . This means that either  $(q\hat{c})^{\top}x^*$  or  $(qc)^{\top}x^*$  are not integral which contradicts the assumption of total dual integrality.

Note that the converse doesn't generally hold. We can have  $Ax \leq b$  integral with b an integral vector, but the system is not TDI.

### 1.1 Total Unimodularity

As an aside, we can consider an alternate condition which guarantees integrality.

**Definition 2** A matrix A is totally unimodular (TUM) if for any square submatrix A', det  $A' \in \{-1,0,1\}$ .

The following propositions hold for TUM matrices.

**Proposition 2** If A is totally unimodular then for all integral vectors b,  $Ax \leq b$  is integral.

This differs from Total Dual Integrality where the integrality was dependent on both A and b.

**Proposition 3** If A is totally unimodular,  $Ax \leq b$  is total dual integral for any integral vector b.

For the case of non-bipartite matching, A is not totally unimodular. Indeed, for the three cycle with edges  $e_1 = (1, 2)$ ,  $e_2 = (2, 3)$ ,  $e_3 = (1, 3)$ , the matrix of  $x(\delta(v)) \le 1$  is given by

$$A = \begin{bmatrix} 1 & 0 & 1 \\ 1 & 1 & 0 \\ 0 & 1 & 1 \end{bmatrix} \tag{3}$$

and  $\det A = 2$ .

Often we can find subsystems of inequalities which define specific solutions of interest and are totally unimodular. Such a technique is employed in Lovász's proof of the Lucchesi-Younger theorem on dicuts.

### 1.2 An alternate proof of Theorem 1

We begin by proving a theorem of Kronecker.

Theorem 4 (Kronecker Approximation Theorem (1884) ) Ax = b has an integral solution if and only if  $y^{\top}b$  is an integer whenever  $y^{\top}A$  is an integral vector.

**Proof:** To prove the forward implication, take an integral solution  $x^*$ . Then  $y^\top A x^* = y^\top b$  and if  $y^\top A$  is integral then  $y^\top b$  must be an integer.

To prove the converse, first note that there must be some solution to the system of equations; otherwise there would be a solution to  $y^{\top}A = 0$  with  $y^{\top}b \neq 0$  and by scaling y, we can get  $y^{\top}b \notin \mathbb{Z}$ . For the remainder, we will consider only a full row rank part of A.

We proceed by introducing operations on the matrix A which preserve integrality. Let the jth column of A be denoted by  $a_j$ . First note that exchanging two columns of A preserves both the existence of an integral solution of Ax = b and the property that  $y^{\top}b \in \mathbb{Z}$  whenever  $y^{\top}A \in \mathbb{Z}$ . Second, note that we can add any integral multiple of one column to another column and still preserve the assumptions. Indeed, for  $\lambda \in \mathbb{Z}$ , if Ax = b, construct the matrix A' with columns identical to those of A but with  $a'_i = a_i + \lambda a_j$ . Let x' be a vector with  $x'_k = x_k$  except for  $x'_j = x_j - \lambda x_i$ . Then it is clear that A'x' = b and x' is integral (whenever x is). Conversely if A'x' = b, we can define x by  $x_k = x'_k$  except for  $x_j = x'_j + \lambda x'_i$  and x is integral and satisfies Ax = b. The preservation of the second assumption is proved similarly.

Using these elementary operations, we can transform A into the form

$$A' = \left[ \begin{array}{cc} B & 0 \end{array} \right] \tag{4}$$

with B lower triangular as follows. For the first row, we can pair any two nonzero entries and compute their gcd using Euclid's algorithm

$$\gcd(x,y) = \begin{cases} \gcd(x-y,y) & \text{if } x \ge y\\ \gcd(y,x) & \text{if } x < y \end{cases}$$
 (5)

since these operations are elementary, we can perform them on the columns and reduce the first row to one nonzero entry. We can then put this column as column 1 and proceed to the next row leaving column 1 fixed. Proceeding in this manner results in the desired form for A'.

Now observe that B is nonsingular because we have assumed that A has full row rank.  $B^{-1}A' = \begin{bmatrix} I & 0 \end{bmatrix}$  and hence  $B^{-1}b$  must be integral (since every row of  $B^{-1}$  is a possible candidate for  $y^{\top}$ ). Since

$$A' \left[ \begin{array}{c} B^{-1}b \\ 0 \end{array} \right] = b \tag{6}$$

we have found an integral solution to the system A'x = b and this completes the proof.

**Corollary 5**  $P = \{x : Ax \leq b\}$  is integral if and only if each supporting hyperplane contains and integral vector.

**Proof:** The forward implication is immediate because every supporting hyperplane contains a vertex of P. For the converse, suppose  $x^*$  is a non-integral vertex of P.  $x^*$  is a unique solution of a subsystem  $\hat{A}x = \hat{b}$  and by the Kronecker approximation theorem, there exists a vector y such that  $y^{\top}b$  is non-integral and  $y^{\top}\hat{A}$  is integral. By adding an integral constant to the components of y, we can assume that y is nonnegative. Let  $c = \hat{A}^{\top}y$  and  $\alpha = y^{\top}b$ . Then  $c^{\top}x = \alpha$  is a supporting hyperplane (teh fact that  $c^{\top}x \leq \alpha$  is valie follows from the nonnegativity of y) and  $c^{\top}x$  is non-integral for all integral x which is a contradiction.

This results in a new proof for Theorem 1.

**Proof of Theorem 1:** If  $Ax \leq b$  is TDI and b is integral, pick an integral c such that  $c_i$  and  $c_j$  are relatively prime for  $i \neq j$ . By linear programming duality,  $\max c^{\top} x$  such that  $Ax \leq b$  will be an integer  $\alpha$  and  $c^{\top} x = \alpha$  will be a supporting hyperplane.

Since the entries of c are relatively prime, we can find an integral vector x contained in the supporting hyperplane. (Indeed, it can be shown easily by induction on n that if the gcd of the entries of c is g then there is an integral solution to  $c^{\top}x = g$ .) Therefore, we conclude that  $Ax \leq b$  is integral.

# 2 Back to matchings

Given a graph G and a matching M define a vector  $\chi^M \in \mathbb{R}^{|E|}$  as

$$\chi_e^M = \begin{cases} 1 & e \in M \\ 0 & \text{otherwise} \end{cases} \tag{7}$$

The  $Matching\ Polytope$  is the convex hull of all such incidence vectors.

Consider the polytope P defined by the inequalities.

$$x(\delta(v)) \le 1 \quad \forall v \in V$$

$$x(E(U)) \le \left\lfloor \frac{|U|}{2} \right\rfloor \quad \forall U \in \mathcal{P}_{odd}$$

$$x > 0$$
(8)

where  $\mathcal{P}_{odd}$  denotes the odd cardinality subsets.

Edmonds proved in 1965 that P was indeed the matching polytope. Cunningham and Marsh in 1978 proved Edmonds result by showing that P was TDI. Indeed this immediately implies that P is the matching polytope because all vertices of P would be integers, and any valid integer solution of P is a matching.

Explicitly we have

**Theorem 6 (Cunningham-Marsh)** For all  $w \in \mathbb{Z}^{|E|}$ , there exist integral vectors y and z such that the maximum weight of any matching is equal to

$$\min \sum_{v \in V} y_v + \sum_{S \in \mathcal{P}_{odd}} \left\lfloor \frac{S}{2} \right\rfloor z_s$$
$$\sum_{v \in V} y_v \chi^{\delta(v)} + \sum_{S \in \mathcal{P}_{odd}} z_s \chi^{E(S)} \ge w$$
$$y > 0, \quad z > 0$$

The proof of this theorem is in Schrijver's book. There are actually two proofs in the book, one that assumes the knowledge of the matching polytope, the other that's self-contained.

We will now show that the Cunningham-Marsh theorem implies the Tutte-Berge formula in the cardinality case ( $w_e = 1$  for all e).

#### Theorem 7 (Tutte-Berge)

$$\nu(G) = \min_{U \subseteq V} \frac{1}{2} (|U| + |V| + o(G - U))$$

**Proof:** Recall from lecture 1 that "\le " was immediate.

For any solution of the Cunningham-Marsh dual problem, it is clear that  $y_v$  and  $z_S$  are at most 1 as  $w_e = 1$  for all edges. Furthermore, for all  $v \in V$  either  $y_v = 1$  or  $z_S = 1$  for some odd set S containing v.

Suppose  $z_S$  and  $z_T$  are such that  $S \cap T \neq \emptyset$ . If  $S \cup T$  is an odd set, we can set  $z_S = z_T = 0$  and  $z_{S \cup T} = 1$  because

$$\left\lfloor \frac{|S|}{2} \right\rfloor + \left\lfloor \frac{|T|}{2} \right\rfloor = \frac{|S| + |T|}{2} - 1 \ge \frac{|S \cup T| + 1}{2} - 1 = \left\lfloor \frac{|S \cup T|}{2} \right\rfloor \tag{9}$$

and this assignment would reduce the cost function. If  $S \cup T$  is an even set, take  $j \in S \cup T$  and set  $z_{S \cup T - \{j\}} = 1$  and  $y_j = 1$ . This will also never increase the cost function. Therefore, we conclude that for an optimal solution, the sets  $\{S \in \mathcal{P}_{odd} : z_S = 1\}$  are not overlapping.

Let  $U = \{v \in V : y_v = 1\}$  and  $W = \{S \in \mathcal{P}_{odd} : z_S = 1\}$ . If  $v \in U$  and  $v \in S$  with  $S \in W$ , then we can remove v and an additional vertex u from S and let  $y_u = 1$  and this gives another feasible solution without increasing the cost function. Thus we can assume that U and all the sets S in W are disjoint. This implies that there cannot be any edges between the sets with  $z_S = 1$ , which means that |W| = o(G - U). Therefore we have shown

$$\nu(G) = \sum_{v \in V} y_v + \sum_{S \in \mathcal{P}_{odd}} \left\lfloor \frac{S}{2} \right\rfloor z_S$$

$$= |U| + \frac{|V| - |U|}{2} - \frac{1}{2}|W|$$

$$= \frac{1}{2} (|V| + |U| - o(G - U))$$
(10)

---

#### 18.997 Topics in Combinatorial Optimization

February 26th, 2004

Lecture 6

Lecturer: Michel X. Goemans Scribe: Joungkeun Lim

Last time, we saw that the matching polytope was defined by:

$$x(\delta(v)) \le 1 \quad \forall v \in V$$
  
$$x(E(S)) \le \left\lfloor \frac{|S|}{2} \right\rfloor, \text{ for } |S| \text{ odd}$$
  
$$x \ge 0.$$

One may wonder whether we need all *blossom* inequalities  $x(E(S)) \leq \lfloor \frac{|S|}{2} \rfloor$ . In other words, which of these inequalities define facets of the polytope and are essential in the description.

**Theorem 1**  $x(E(S)) \leq \lfloor \frac{|S|}{2} \rfloor$  is necessary in the description of the matching polytope iff G[S] is factor-critical and 2-connected.

The proof is in the book, Ch.25-5. The fact that they are necessary uses the Theorem mentioned in lecture 3 that the number of affinely independent near-perfect matchings in a 2-connected factor-critical graph is equal to |E|.

## 1 Partially Ordered Sets (posets) — Ch.14

**Definition 1** S is poset with relation  $\leq$  when,

- $s \leq s$
- s < t and  $t < s \Rightarrow s = t$
- $s \le t$  and  $t \le v \Rightarrow s \le v$  (transitive)

for  $s, t, v \in S$ .

s < t means  $s \le t$  and  $s \ne t$ . The poset S induces a digraph (S,A) such that A is the set of edges (s,t) if s < t.

**Definition 2** An antichain A is a subset of S such that  $\forall s \neq t \in A, t \nleq s$  and  $s \nleq t$ . A chain C is a subset of S such that  $\forall s \neq t \in C, s \leq t$  or  $t \leq s$ .

We define the maximum s of a chain C as the element of C such that  $t \leq s$  for all  $t \in C$ . The maximum element exists and is unique in any chain of a poset.

We can easily see that  $|A \cap C| \leq 1$  for any antichain A and any chain C.

**Theorem 2**  $\max_{C} |C| = minimum number of antichains <math>A'_{i}s$  which partition S.

**Theorem 3** (Dilworth's theorem)  $\max_A |A| = minimum \ number \ of \ chains \ C'_i s \ which \ partition \ S.$ 

In both theorems 2 and 3, " $\leq$ " part is clear by  $|A \cap C| \leq 1$ . For both theorems, it would be enough to prove the existence of the appropriate number of chains or antichains *covering* S rather than partitioning it.

**Proof:** (proof of theorem 2 " $\geq$ " part) Define height(s) as the number of elements in the longest chain whose maximum is s. Then the maximum of all heights equals to  $\max_{C} |C|$ . Let  $A_i = \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n} |C_i| + \sum_{i=1}^{n$ 

Figure 1: A maximum antichain A and the subgraph  $A^{\uparrow}$  and  $A^{\downarrow}$ .

 $\{s|height(s)=i\}$ , then  $A_i$  is an antichain.  $A_1,A_2,\cdots,A_M$  is a set of antichains which partitions S where  $M=\max_{C}|C|$ .

**Proof:** (proof of theorem 3 "\geq" part) Take a maximum size antichain A and  $|A| = \alpha$ . Let  $A^{\uparrow} = \{s | \exists t \in A, \ t \leq s\}$  and  $A^{\downarrow} = \{s | \exists t \in A, \ s \leq t\}$ .

We consider two cases.

- Case 1: there is no antichain A of maximum size such that  $A \neq A^{\uparrow}$  and  $A \neq A^{\downarrow}$ . In this case, the only antichains of maximum size are either the set of maximal elements or the set of minimal elements. Choose a minimal element s and a maximal element t satisfying  $s \leq t$  (this is always possible otherwise we could find a larger antichain). Think of  $S \setminus \{s, t\}$ . Then the maximum size of an antichain decreases because, otherwise, there would exist an antichain A such that  $A \neq A^{\uparrow}$  and  $A \neq A^{\downarrow}$ . So the maximum size of an antichain decreases by 1 and it is  $\alpha 1$ . By induction,  $S \setminus \{s, t\}$  can be partitioned by  $\alpha 1$  chains. Adding the chain  $\{s, t\}$ , S can be partitioned by  $\alpha$  chains.
- Case 2: there is an antichain A of maximum size such that  $A \neq A^{\uparrow}$  and  $A \neq A^{\downarrow}$ . A is a maximum antichain in both  $A^{\uparrow}$ ,  $A^{\downarrow}$ . By induction on the size of the poset, there exists  $\alpha$  chains in each set  $A^{\uparrow}$ ,  $A^{\downarrow}$  which partition the poset. Now we merge every two chains, one from each set, which intersect. That will give  $\alpha$  chains which partition the original set.

#### 2 Bipartite Matching

Dilworth's theorem is actually equivalent to König's theorem for bipartite graphs. Let us start by stating König's theorem and showing it follows from our discussion on non-bipartite matching.

Let  $\nu(G)$  be the size of a maximum matching in G and  $\tau(G)$  be the size of a minimum vertex cover in G.

**Theorem 4** (König's theorem)  $\nu(G) = \tau(G)$  in a bipartite graph G.

We'll prove this using the Edmonds-Gallai structure since we have already proved it, but this is an overkill. König's theorem can be proved quite simply.

**Proof:** The following sets are defined in the Edmonds-Gallai structure.

6-2

- D(G) = vertices missed by some matching.
- A(G) = N(D(G)) =the neighborhood of D(G) and
- $C(G) = V(G) \setminus D(G) \setminus A(G)$ .

We already know that each component of G[D(G)] is factor-critical and that each component of G[C(G)] has a perfect maching. So we can find a vertex cover which has the same size as the maximum matching as follows.

- 1. Take all of A(G).
- 2. Each component of C(G) is bipartite and contains a perfect matching, so we can take one side of the bipartition within C(G) in the vertex cover. Here we have selected half of the vertices of C(G).
- 3. From each component of D(G), delete one of the vertices which is adjacent to a vertex of A(G). Then each component of D(G) turns to be of even size and we can take half of the elements to put within the vertex cover.

Combining all the vertices we got from 1, 2, 3, we obtain a vertex cover of G of size:

$$|A(G)| + \frac{|C(G)|}{2} + \frac{|D(G)| - o(G \setminus A(G))}{2} = \frac{1}{2}[|V| + |A(G)| - o(G \setminus A(G))],$$

where  $o(G \setminus A(G))$  is the number of odd components of  $G \setminus A(G)$ . Therefore we found a vertex cover which has the same size as a maximum matching.

Now we will show a different proof of Dilworth's theorem using König's theorem.

**Proof:** (Dilworth's theorem) For a poset S, define a bipartite graph H with 2n vertices by creating two vertices  $a_i$ ,  $b_i$  for each  $i \in S$ , and the edge set E(H) is such that  $(a_s, b_t) \in E(H) \Leftrightarrow s < t$ .

Figure 2: The bipartite graph H.

We claim that a matching M in the graph H corresponds to a partitioning of S by n - |M| chains. Indeed, just consider the arcs the poset that correspond to the edges in the matching. Every vertex i of S can have at most one incoming arc (if  $b_i$  is matched) and one outgoing arc (if  $a_i$  is matched). This means that it corresponds to a partitioning of S by chains. The number of chains is equal to the number of vertices with no incoming edge and this is equal to the number of unmatched vertices in B, i.e. n - |M|.

Now consider a minimum vertex cover F of H. Let  $\hat{A} = \{s \in S | a_s \notin F \text{ and } b_s \notin F\}$ . The fact that F is a vertex cover implies that  $\hat{A}$  is an antichain. Furthermore, we have that  $|\hat{A}| \geq n - |F| = n - |M|$ , which is the number of chains we have obtained in the first part that partitions S. Therefore we proved the  $\geq$  part of Theorem 3.

### 3 Weighted posets

We can generalize Theorems 2 and 3 to weighted posets. Let  $w: S \to Z_+$ , be a weight function defined on the elements of S.

**Theorem 5**  $\max_C w(C) (= \sum_{s \in C} w_s)$  where the maximum is taken over the chains C is equal to the minimum number of antichains which cover each s w(s) times,  $\forall s \in S$ .

**Theorem 6**  $\max_A w(A) (= \sum_{s \in A} w_s)$  where the maximum is taken over the antichains A is equal to the minimum number of chains which cover each s w(s) times,  $\forall s \in S$ .

Both theorems have to be stated in terms of covering S instead of partitioning S.

**Proof:** (Proof of Theorem 5) Replace a vertex s by a chain of w(s) copies of s,  $\forall s \in S$ . If  $s \leq t$  in the original poset, we have that  $s^{(i)} \leq t^{(j)}$  when  $s^{(i)}$  (resp.  $t^{(j)}$ ) is any copy of s (resp. t). See Figure 3. Let the resulting poset denoted by S'. Then apply Dilworth's theorem to S'. A maximum cardinality chain in S' corresponds to a chain in S of maximum weight. Also a minimum covering of S' by antichains corresponds to a covering of S by antichains which cover s w(s) times.

Figure 3: Making w(s) chain copies of s.

**Proof:** (Proof of Theorem 6) Replace a vertex s by an antichain of w(s) copies of s,  $\forall s \in S$ . By applying Dilworth's theorem to the resulting poset will give the proof by similar reasoning to the previous proof. See Figure 4.

Figure 4: Making w(s) incomparable copies of s.

# 4 Chain Polytope

Theorem 5 is equivalent to the fact that the following system is TDI:

$$\begin{array}{l} Max \sum w_s x_s \\ \text{s.t.} \ x(A) \leq 1 \ , \, \forall \ \text{antichain A} \\ x_s \geq 0, \, s \in S. \end{array}$$

The dual is:

$$\begin{aligned} & Min \sum_{A} y_{A} \\ & \text{s.t. } \sum_{(A:s \in A)} y_{A} \geq w_{s} \\ & y_{A} \geq 0. \end{aligned}$$

From Theorem 5, we derive that both the primal and the dual have an integer optimal solution whenever  $w_s$  is integral for all s. This means that the system is TDI.

The following antichain polytope is TDI for the same reason.

$$\begin{array}{l} Max \sum w_s z_s \\ \text{s.t. } z(C) \leq 1 \text{ , } \forall \text{ antichain C} \\ z_s \geq 0, \, s \in S. \end{array}$$

---

| 18.997 Topics in Combinatorial Optimization | March 2, 2004       |
|---------------------------------------------|---------------------|
| Lecture 7                                   |                     |
| Lecturer: Michel X. Goemans                 | Scribe: Jan Vondrák |

## 1 Gallai's Conjecture

In this lecture, we will be concerned with graph coverings by a collection of paths or cycles. The goal will be to cover all the vertices by a small number of either paths or cycles, and this number will be bounded by the independence number  $\alpha(G)$ . ( $\alpha(G)$  is the maximum size of an independent, or stable, set, i.e. a set of vertices inducing no edges.) For a directed graph D,  $\alpha(D)$  refers to the corresponding undirected graph. Let's start with the following statement, proved by Gallai and Milgram in 1960.

**Theorem 1** (Gallai-Milgram) In every directed graph D, the vertices can be partitioned into  $\alpha(D)$  vertex-disjoint directed paths.

Observe that we may able to partition V with fewer directed paths, as it is the case for example for a directed cycle (one path suffices but  $\alpha(D) = \lfloor n/2 \rfloor$ ).

Consequently, Gallai suggested a related conjecture, which has been recently proved by Bessy and Thomassé.

**Theorem 2** (Bessy-Thomassé) In every strongly connected digraph D, the vertices can be covered by at most  $\alpha(D)$  directed cycles.

In contrast to the Gallai-Milgram theorem, the directed cycles cannot be always chosen to be vertex-disjoint, and this explains the "covering" instead of "partitioning" in teh statement. Below is an example of a directed graph D which has  $\alpha(D)=3$ , and it can be covered by 2 cycles, but there are no two disjoint cycles in D.

Before we proceed to the proofs, let's note a few connections to other theorems.

- Gallai-Milgram implies Dilworth's theorem. For any poset, there is a digraph naturally associated with it, where (i,j) is an arc if i < j. Paths correspond to chains and stable sets to antichains which implies that the poset can be partitioned into  $\alpha(D)$  chains where  $\alpha(D)$  is the maximum size of an antichain.
- Bessy-Thomassé implies that every digraph can be covered by at most  $\alpha(D)$  directed paths. (Add a new vertex connected to everything in both directions, which makes the graph strongly connected. Then find a cycle covering and turn the cycles into paths, removing the new vertex if necessary.) However, this is weaker than Gallai-Milgram, because the paths are not necessarily disjoint (so this is a cover and not a partition).

• For a tournament, Gallai-Milgram implies the existence of a hamiltonian path. For a strongly connected tournament, Bessy-Thomassé implies the existence of a hamiltonian cycle. These are theorems previously proved by Rédei (1934) and Camion (1960).

Now we turn to the proof of Gallai-Milgram. The theorem is proved by repeated application of the following lemma (starting with a trivial partitioning into n (singleton) paths).

**Lemma 3** Let  $\pi$  be a partitioning of the vertices of D into directed paths  $P_1, P_2, \dots P_l$ ,  $l > \alpha(D)$ . Let  $S(\pi)$  denotes the starting vertices, and  $F(\pi)$  the ending vertices of  $P_1, \dots P_l$ . Then there is a partitioning  $\pi'$  into l-1 directed paths such that  $S(\pi') \subset S(\pi)$  and  $F(\pi') \subset F(\pi)$ .

**Proof:** We proceed by induction on the size of D. Since  $|F(\pi)| > \alpha(D)$ , there must be an arc (v, u) with  $u, v \in F(\pi)$ . Consider the paths  $P_u, P_v$  whose endpoints are u and v, respectively.

- 1. If  $P_u$  has length 0, we can just remove it and extend  $P_v$  by the arc (v, u), which yields a covering  $\pi'$  of l-1 paths.
- 2. If  $P_u$  has length at least 1, let w be the vertex on  $P_u$  preceding u. We remove vertex u and apply the inductive hypothesis on the remaining digraph  $\hat{D}$ . The partition  $\pi$  can be also restricted to a partition  $\hat{\pi}$  by removing u from  $P_u$ . Note that now  $v, w \in F(\hat{\pi})$ , since v remains in  $\hat{D}$  and w was the last vertex on  $P_u$  before u. Since  $\alpha(\hat{D}) \leq \alpha(D)$ , by induction there is a partitioning of  $\hat{D}$  into l-1 paths  $\hat{\pi}'$ , such that  $F(\hat{\pi}')$  contains all the vertices of  $F(\hat{\pi})$  except one. If  $w \in F(\hat{\pi}')$ , then we extend the path ending at w by (w, u). Otherwise  $v \in F(\hat{\pi}')$ , and we extend the path ending at v by (v, u). Either way, we obtain a partitioning  $\pi'$  where  $F(\pi') \subset F(\pi)$ .

In the rest of the lecture, we prepare the ground for the proof of Bessy-Thomassé.

**Definition 1** For a directed graph D = (V, A), consider enumerations of the vertex set, such as  $(v_1, v_2, \dots v_n)$ . We define a cyclic ordering as an equivalence class of enumerations with respect to the following equivalence relations:

- $(v_1, v_2, \dots v_{n-1}, v_n) \sim (v_2, v_3, \dots, v_n, v_1)$
- $(v_1, v_2, \dots v_n) \sim (v_2, v_1, \dots v_n)$  if  $(v_1, v_2) \notin A$  and  $(v_2, v_1) \notin A$ .

For an enumeration, we call an arc  $(v_i, v_j)$  forward if i < j, and backward if i > j. Also, we can visualize all arcs as going clockwise around the circle, and then backward arcs are those which cross the boundary between  $v_n$  and  $v_1$ .

For a cyclic ordering  $\mathcal{O}$  and a directed cycle C, let  $i_{\mathcal{O}}(C)$  denote the number of backward arcs in C. Note that  $i_{\mathcal{O}}(C)$  depends on the cyclic ordering, but not on a specific enumeration within the equivalence class;  $i_{\mathcal{O}}(C)$  can be also viewed as the number of times the cycle loops around the circle.

We call a cyclic ordering valid, if every arc is contained in a directed cycle of index  $i_{\mathcal{O}}(C) = 1$ . S is a cyclic stable set with respect to  $\mathcal{O}$ , if it is a stable set which is consecutive in some enumeration of  $\mathcal{O}$ .

**Theorem 4** For every strongly connected directed graph, there exists a valid cyclic ordering.

**Proof:** Let  $\mathcal{O}$  be a cyclic ordering, minimizing the sum of indices over all directed cycles,  $\sum_{C} i_{\mathcal{O}}(C)$ . Suppose that  $\mathcal{O}$  is not valid, i.e. some arc is not in any directed cycle of index 1. Consider such an arc  $(v_j, v_i)$  and an enumeration such that  $(v_j, v_i)$  is a backward arc and j - i is as small as possible. Since there is no cycle of index 1 containing  $(v_j, v_i)$ , there is no forward path from  $v_i$  to  $v_j$ . First assume that j - i > 1. One implication of this is that  $(v_{k+1}, v_k)$  is never an arc. Let k be the maximum smaller than j, such that  $v_k$  can be reached by a forward path from  $v_i$ .

- 1. k = i: there is no arc between  $v_i$  and  $v_{i+1}$ , so we can swap  $v_i$  with  $v_{i+1}$ , which moves  $v_i$  closer to  $v_j$  (contradiction).
- 2.  $k \neq i$ : there are no arcs from  $v_k$  to  $v_l$ ,  $k < l \leq j$ . Also, there are no arcs from  $v_l$  to  $v_k$  for the same indices l; otherwise the existence of this arc would contradict the minimality of j i. Therefore we can swap  $v_k$  with  $v_{k+1}$ , then with  $v_{k+2}$ , until we swap  $v_k$  with  $v_j$ , which creates an enumeration where  $v_i$  and  $v_j$  are closer to each other (contradiction).

Thus we can assume that j-i=1. In this case, we switch  $v_i$  and  $v_j$ , which creates a different cyclic ordering. Every directed cycle which contains  $(v_j, v_i)$  decreases its index by 1. No other cycle is affected. Therefore we find a cyclic ordering  $\mathcal{O}'$  with a smaller value of  $\sum_C i_{\mathcal{O}'}(C)$ , which is a contradiction.

A corollary is Camion's theorem for strongly connected tournaments.

**Corollary 5** For a strongly connected tournament, there is a cyclic ordering  $(v_1, v_2, \dots v_n)$  such that all the edges  $(v_i, v_{i+1})$  are oriented clockwise, i.e. there is a hamiltonian cycle.

---

| 18.997 | Topics | in | Combinatorial | O      | ptimization  |
|--------|--------|----|---------------|--------|--------------|
| 10.00. | TOPICS |    | Committee     | $\sim$ | PULLLEGUIOII |

March 4, 2004

### Lecture 8

Lecturer: Michel X. Goemans Scribe: Constantine Caramanis

This lecture covers the proof of the Bessy-Thomassé Theorem, formerly known as the Gallai Conjecture. Also, we discuss the cyclic stable set polytope, and show that it is totally dual integral (TDI) (see lecture 5 for more on TDI systems of inequalities).

## 1 Recap and Definitions

In this section we provide a brief recap of some definitions we saw in the previous lecture. Also we answer a question that remained unanswered in the previous lecture regarding the polynomiality of finding a valid ordering given any strongly connected directed graph.

For a strongly connected digraph D = (V, A), with |V| = n, we make the following definitions.

- 1. Given an enumeration of the vertices,  $\{v_1, \ldots, v_n\}$ , an arc  $(v_i, v_j) \in A$  is called backward if i > j and forward if i < j.
- 2. An ordering  $\mathcal{O}$ , is an equivalence class of enumerations of a graph. The equivalence class is defined by the equivalence relations
  - (a)  $v_1, v_2, \ldots, v_n \sim v_2, v_3, \ldots, v_n, v_1,$
  - (b)  $v_1, v_2, \dots, v_n \sim v_2, v_1, v_3, \dots, v_n$ , if there is no arc between  $v_1$  and  $v_2$ , i.e.,  $(v_1, v_2), (v_2, v_1) \notin A$ .
- 3. Given an ordering  $\mathcal{O}$ , the *index* with respect to  $\mathcal{O}$  of a directed cycle C, denoted  $i_{\mathcal{O}}(C)$ , is the number of backward arcs in C. Recall from the last lecture that the index is well defined, since the index is invariant under the equivalence operations defined above.
- 4. We say that an ordering  $\mathcal{O}$  is valid if for any arc  $(u,v) \in A$ , there exists a cycle C containing that arc, with index 1:  $i_{\mathcal{O}}(C) = 1$ . We showed in the last lecture that there always exists a valid ordering.
- 5. A cyclic stable set S with respect to a valid ordering  $\mathcal{O}$ , is such that S is a stable set on the underlying undirected graph, and also there exists some enumeration  $\{v_1, \ldots, v_n\}$  of the ordering such that  $S = \{v_1, \ldots, v_k\}$ , where k = |S|.

Last time we proved that any strongly connected digraph has a valid ordering. In fact, given any such graph, a valid ordering can be found in time polynomial in the size of the graph. Recall that the proof of the existence theorem showed that the minimizer of

$$\min_{\mathcal{O}} \sum_{\text{directed cycles } C} i_{\mathcal{O}}(C),$$

must be a valid ordering. Given any ordering  $\mathcal{O}$ , we showed in the proof that in a polynomial number of steps (essentially, by repeated "local swaps"), if  $\mathcal{O}$  is not valid, we can obtain a new ordering  $\mathcal{O}_1$ , reducing the number of arcs for which there are no cycles of index 1 containing them. Therefore we can find a valid ordering in polynomial time.

### 2 The Bessy-Thomassé Theorem

Recall the statement of the theorem.

**Theorem 1** Given a strongly connected digraph D = (V, A), and a valid ordering  $\mathcal{O}$ , if  $\alpha_{\mathcal{O}}$  denotes the size of the largest cardinality cyclic stable set, then

$$\alpha_{\mathcal{O}} = \min \sum_{\{C_1, \dots, C_p\}} i_{\mathcal{O}}(C_i),$$

where the cycles  $\{C_1, \ldots, C_p\}$  cover the vertex set V.

The inequality

$$\alpha_{\mathcal{O}} \leq \min \sum_{\{C_1, \dots, C_p\}} i_{\mathcal{O}}(C_i),$$

is straightforward (as each vertex of a cycle stable set must be contained in (at least) one directed cycle and the corresponding entering arc must be backward), so we consider only the proof of the reverse inequality.

Before we prove this theorem, we make some remarks. It is important to note that the cyclic stability number,  $\alpha_{\mathcal{O}}$ , depends on the ordering  $\mathcal{O}$  chosen. To illustrate this, recall our digraph on five vertices from last lecture. In Figure 2, we exhibit two different orderings where the cyclic stability number is different.

Figure 1: In figure (a) above, the cyclic stability number equals 2, where as in (b), the cyclic stability number equals 1.

Computing the stability number of a general graph is known to be NP-hard. One of the corollaries of the Bessy-Thomassé Theorem is that the cyclic stability number can be computed efficiently. This follows because we can compute the quantity  $\min \sum_{\{C_1,\dots,C_p\}} i_{\mathcal{O}}(C_i)$  in the right hand side of the theorem above, efficiently. We can do this by formulating a network flow problem that computes the minimization. To do this, fix an enumeration of the ordering. Attach a cost of 0 to every forward arc in the digraph under the given enumeration, and a cost of 1 to every backward arc. Next, split each vertex v into a pair  $\{v_{\text{out}}, v_{\text{in}}\}$  with a directed edge  $(v_{\text{out}}, v_{\text{in}})$  with flow capacity bounded from below by 1. Then for every arc (u, v) in the original graph, draw an arc  $(u_{\text{out}}, v_{\text{in}})$  in the network flow graph. Finding a minimum cost flow in this network can be done efficiently, and it amounts to finding a set of cycles  $\{C_1,\dots,C_p\}$  that cover V, and minimize  $\sum_{\{C_1,\dots,C_p\}} i_{\mathcal{O}}(C_i)$ .

A key step in the proof of the Bessy-Thomassé Theorem is a lemma that provides a sufficient condition for a subset S of vertices to be a cyclic stable set.

**Lemma 2** Given a valid ordering  $\mathcal{O}$ , fix an enumeration,  $\{v_1, \ldots, v_n\}$ . Let  $S \subseteq V$  be a subset of the vertices. If there are no forward paths between any two vertices of S, then S is a cyclic stable set.

**Proof:** Suppose, to the contrary, that S has no forward arcs, but S is not a cyclic stable. Let  $v_i$  be the first element of the enumeration in S. If we rotate the enumeration so that  $v_i$  becomes  $v_1$ , no forward paths are either created or destroyed in S, so we may assume, without loss of generality, that  $v_1 \in S$ . If S is a cyclic stable set with respect to  $\mathcal{O}$ , then there exists some enumeration of  $\mathcal{O}$  for which the elements of S are the first k = |S| elements of the enumeration. Equivalently, there exists a sequence of local steps, or swaps we can make according to the equivalence relations defining an ordering, to move from the current enumeration to one of the correct form. If S is not a cyclic stable set, as we assume, then this is not possible. Consider the enumeration which brings S "as close as possible" to having all its elements at the beginning of the enumeration, as illustrated in Figure 2. By this we mean that as many elements of S as possible are listed first in the enumeration, and furthermore, the first element of S not part of the initial string of elements of S (which we call  $S_{<}$ ) is as close to  $S_{<}$  as possible. We denote by  $S_{<}$  the elements of S that are at the beginning of

Figure 2: The figure exhibits the enumeration with respect to which as many elements of S as possible are the first elements of the enumeration. Since S is assumed not to be a cyclic stable set, there must be some element w sandwiched by elements of S.

the enumeration, by  $S_{>}$  the remaining elements of S, and by W the elements after the last element of  $S_{<}$  and before the first element of  $S_{>}$ , as illustrated in Figure 2. Since there are no forward paths joining any two elements of S, for any  $w \in W$  there cannot be a forward path from  $S_{<}$  to w, and a forward path from w to an element of  $S_{>}$ . Consider the first  $w \in W$  where there is no forward path from  $S_{<}$  to w (if there is such a vertex). Because w is assumed to be the first such vertex, there can be no forward path from any vertex v coming before w in the enumeration. If there were such a vertex v, then if there were a forward path from  $S_{<}$  to v, we would also have a forward path from  $S_{<}$  to w. If there were no forward path from  $S_{<}$  to v, it would contradict our assumption that w is the first vertex in W that has no forward path from  $S_{<}$ . In particular, then, there are no arcs from any vertex before w in the enumeration, to w. However, there also can be no arc from w to any vertex before it in the enumeration. This follows because  $\mathcal{O}$  was assumed to be a valid ordering. If there were such an arc, say (w, v) for v earlier in the enumeration, because we assume there are no forward arcs from any vertex coming before w, to w, and that w is the first such vertex, then any cycle C containing the arc (w,v) must have  $i_{\mathcal{O}}(C) \geq 2$ , a contradiction to the validity of the ordering  $\mathcal{O}$ . Therefore there are no arcs between w and any vertex previous to w in the enumeration. But then using the equivalence relations, we can swap w with each element before it, including then each element of  $S_{<}$ . But this contradicts our assumption that the first element of  $S \setminus S_{<}$  was as close as possible to  $S_{<}$ . Therefore there are no elements in W that have no forward paths from S. In particular, this implies that there are no forward paths from any  $w \in W$  to  $S_{>}$ . Then, let  $v_j \in S$  be the first vertex in  $S_{>}$ . By assumption, unless W is empty,  $v_{j-1} \in W$ , and there is no forward path from  $v_{j-1}$  to  $S_{>}$ , and in particular,  $(v_{j-1}, v_j) \notin A$ . But then, since  $\mathcal{O}$  is a valid ordering,  $(v_j, v_{j-1}) \notin A$ . In this case, we can swap the two vertices, contradicting our assumption that our enumeration put S "as close as possible" to having its elements at the beginning of the enumeration. Therefore W must be empty, and S is indeed a cyclic stable set.

We now move to the proof of the Bessy-Thomassé Theorem.

#### **Proof:**

The Main Idea: We want to show that the size of the maximum cyclic stable set equals the minimum total index of a family of cycles covering V. Essentially the proof relies on mapping our digraph D to a poset T. At this point, we appeal to Dilworth's Theorem (lecture 6). Recall that the strong version of Dilworth's Theorem tells us that the size of the largest antichain in the poset equals the minimum number of chains needed to partition the elements of the poset. We show that our maximum size cyclic stable set S in D, corresponds naturally to an antichain in the poset T. Thus the size of the largest antichain in T is at least the size of S, i.e.,  $\alpha_{\mathcal{O}}$ . Then we use Lemma 2 to show that any antichain in T corresponds to a cyclic stable set in D. Thus we have that the size of the largest antichain in T is exactly  $\alpha_{\mathcal{O}}$ .

Dilworth's Theorem now links the number of chains partitioning T to  $\alpha_{\mathcal{O}}$ . The final part of the proof recovers a covering family of cycles from the chains in T.

The Proof: For the given ordering  $\mathcal{O}$ , let  $S = \{v_1, \ldots, v_k\}$  denote the maximum size cyclic stable set, with corresponding enumeration of  $V = \{v_1, \ldots, v_k, \ldots, v_n\}$ . We note that since S is, in particular, a stable set, we can permute its elements as we wish within the given ordering.

We form an acyclic digraph D' = (V', A') from D as follows. Let  $V' = \{v_1, \ldots, v_n, v'_1, \ldots, v'_k\}$  (we duplicate the elements of S) so that |V'| = n + k. Next, if  $(v, w) \in A$  is a forward arc, then  $(v, w) \in A'$ . If  $(w, v_i) \in A$  is a backward arc into a vertex of S (i.e., if  $v_i \in S$ ) then  $(w, v'_i) \in A'$ . Note that by our choice of enumeration, any arcs into  $v_i$ ,  $i \leq k$ , must be backward. Therefore the digraph D' is acyclic. It is illustrated in Figure 2.

Figure 3: This figure illustrates the directed acyclic graph D' we obtain from splitting the vertices in S and drawing arcs as explained above.

In order to use Dilworth's Theorem, we need to have a poset T. We obtain a poset T from the acyclic digraph D' by considering the transitive closure of D'. Since the sets  $\{v_1, \ldots, v_k\}$  and

 $\{v_1', \ldots, v_k'\}$  have no incoming and outgoing arcs, respectively, they are both antichains in T. This is also evident from Figure 2. We show that they are in fact maximum size antichains. Consider any antichain I. As the ordering is valid, for any vertex, there exists a directed cycle of index 1 going through it. This translates into a chain in the poset going from  $v_i$  to  $v_i'$  for any  $1 \le i \le k$ . This means that an antichain I cannot contain both  $v_i$  and  $v_i'$ . Let  $I_D$  be the elements of the original digraph D corresponding to I.

By renumbering the elements of S (recall that we can permute the elements of S within the given ordering) we can assume that  $v'_1, \ldots, v'_l \in I$ , and  $v'_{l+1}, \ldots, v'_k \notin I$ . Now rotate the enumeration to obtain  $\{\tilde{v}_1, \ldots, \tilde{v}_n\}$  so that  $\tilde{v}_1 = v_{l+1}$ . Since I is an antichain, and since the digraph vertices  $\{v_1, \ldots, v_l\}$  corresponding to the poset elements  $\{v'_1, \ldots, v'_l\}$  at the "top" of the poset T have been rotated to be the last elements of the enumeration, there are no forward paths between any two elements of  $I_D$ . Therefore, by Lemma 2,  $I_D$  is a cyclic stable set. Therefore  $I_D$ , and consequently I, can have size at most equal to the size of S, that is,  $\alpha_O$ . We have thus shown that the size of the largest antichain in T is equal to the cyclic stability number  $\alpha_O$  of D.

Now consider the minimal partitioning set of chains in the poset T, call these  $P_1, \ldots, P_k$  (where  $k = |S| = \alpha_{\mathcal{O}}$ ). Each chain  $P_i$  is a chain from  $v_i$  to  $v'_{\sigma(i)}$ , for some permutation  $\sigma$  of  $\{1, \ldots, k\}$ . By a slight abuse of notation, we also use  $P_i$  to refer to the directed path in D from  $v_i$  to  $v_{\sigma(i)}$  (or cycle if  $\sigma(i) = i$ ). We note that by construction of T, there is exactly one backward arc in each path  $P_i$ , namely, the last arc to  $v_{\sigma(i)}$ . These paths cover the vertex set V. Now, the cycles in the permutation  $\sigma$  correspond to cycles in D. For example, if (12) is a cycle in  $\sigma$ , i.e., if  $\sigma(1)=2$  and  $\sigma(2)=1$ , then joining the paths  $P_1$  and  $P_2$  we have a cycle from  $v_1$  to  $v_1$ . We note that these cycles may in fact intersect. Since the cycles merely need to cover the vertex set V, distinct cycles can intersect. We need to take care that the same cycle does not intersect itself. If  $\sigma$  happens to be the identity permutation,  $\sigma(i) = i$ , then each path is a cycle and cannot intersect itself, and hence the proof is complete. If this is not the case, then a cycle in D obtained by joining together the paths  $P_i$  that correspond to a cycle of  $\sigma$  may in fact intersect itself. Suppose that i and j are in the same cycle of  $\sigma$  and the paths  $P_i$  and  $P_j$  intersect, in say v. We can then replace the paths  $P_i$  and  $P_j$  by two other paths  $P'_i$  and  $P'_j$  (obtained by switching from one to the other at v) which together cover the same vertices and which corresponds to a new permutation  $\sigma'$  with  $\sigma'(i) = \sigma(j)$  and  $\sigma'(j) = \sigma(i)$ . Now the number of cycles in the permutation has increased by one, and we can repeat this process until no cycle in D (corresponding to each cycle of teh permutation  $\sigma$ ) intersects itself.

Since the cycle splitting procedure does not change the total index of the cycles, we know that the total index equals the minimal number of chains required to partition T. But by above, this is exactly the size of the maximum cyclic stable set, and therefore

$$\alpha_{\mathcal{O}} = \min \sum_{\{C_1, \dots, C_p\}} i_{\mathcal{O}}(C_i),$$

which is what we wanted to prove.

# 3 Cyclic Stable Set Polytope

In this section, we follow some recent (unpublished) work of A. Sebö, and define the cyclic stable set polytope of a strongly connected graph D, with a given valid ordering  $\mathcal{O}$ . Define the polytope  $\mathcal{P}$  as follows.

$$\mathcal{P} \stackrel{\triangle}{=} \left\{ x \left| \begin{array}{ll} x(C) \le i_{\mathcal{O}}(C), & \forall \text{ directed cycles } C \\ x_v \ge 0, & \forall v \in V \end{array} \right. \right\}.$$

We show in this section that the polytope  $\mathcal{P}$  is totally dual integral (TDI) (see lecture 5 for more on TDI system of inequalities).

Given a cyclic stable set S (cyclic stable with respect to the given ordering), let  $x^S$  denote its incidence vector, i.e.,  $x_v^S = 1$  if  $v \in S$ , and 0 otherwise. Then in fact  $x^S \in \mathcal{P}$ . Indeed, consider any

directed cycle C. Since S is cyclic stable, C always enters S via a backward arc, and therefore the number of backward arcs of C is at least the cardinality of its intersection with S:

(# backward arcs in 
$$C$$
) =  $i_{\mathcal{O}}(C) \ge |C \cap S|$ ,

or, equivalently,  $x^S(C) \leq i_{\mathcal{O}}(C)$ .

Since we have shown that the incidence vector of every cyclic stable set belongs to  $\mathcal{P}$ , we have:

$$\alpha_{\mathcal{O}} \leq \max: \sum_{v \in V} x_v$$
  
s.t.:  $x(C) \leq i_{\mathcal{O}}(C), \quad \forall C$   
 $x_v \geq 0, \quad \forall v \in V$ 

By linear programming duality, and then by observing that the optimum value of a minimization can only increase if we add constraints, we have

$$\begin{array}{lll} \alpha_{\mathcal{O}} & \leq & \max: & \sum_{v \in V} x_v \\ & \text{s.t.}: & x(C) \leq i_{\mathcal{O}}(C), & \forall C \\ & x_v \geq 0, & \forall v \in V \end{array}$$

$$= & \min: & \sum_{C} i_{\mathcal{O}}(C) y_C \\ & \text{s.t.}: & \sum_{C: v \in C} y_C \geq 1, & \forall v \in V \\ & y_C \geq 0, & \forall C \end{array}$$

$$\leq & \min: & \sum_{C: v \in C} i_{\mathcal{O}}(C) y_C \\ & \text{s.t.}: & \sum_{C: v \in C} y_C \geq 1, & \forall v \in V \\ & y_C \geq 0, & \forall C \\ & y_C \in \{0, 1\}. \end{array}$$

But this last quantity is exactly the minimum total index of a cycle cover of V, and thus by the Bessy-Thomassé Theorem, the final quantity equals  $\alpha_{\mathcal{O}}$ . Therefore equality must hold throughout.

Recall that in order to prove that the description of  $\mathcal{P}$  is TDI, we must show that for all integral objective functions w ( $w_v \in \mathbb{Z}$ ), the dual linear program

min: 
$$\sum_{C} i_{\mathcal{O}}(C) y_{C}$$
  
s.t.:  $\sum_{C: v \in C} y_{C} \ge 1$ ,  $\forall v \in V$   
 $y_{C} \ge 0$ ,  $\forall C$ 

has an integral solution whenever its value is finite. We note that we have just proved this statement for the special case  $w_v = 1$ . We note also that if we have  $w_v \leq 0$ , we can replace this  $w_v$  by 0 without affecting the feasible region of the dual linear program. Therefore, we can assume that we have  $w_v \in \mathbb{Z}_+$ .

We now construct a strongly connected digraph D' = (V', A'), with valid ordering  $\mathcal{O}'$  as follows. Let V' consist of  $w_v$  copies of each  $x_v$ ,  $\{x_{v,1}, \ldots, x_{v,w_v}\}$  (recall that  $w_v$  is a positive integer). If  $(v,u) \in A$ , then  $(x_{v,i}, x_{u,j}) \in A'$  for every  $i \leq w_v$  and  $j \leq w_u$ . From our reasoning above, we know that the linear program associated to the digraph D' (now we have  $w_v = 1$  for every  $v \in V'$ ) produces an integral solution that corresponds to a maximum size cyclic stable set in D'. Note that if  $x_{v,i}$  is in the stable set S' for D', then we can also take  $x_{v,j}$  to be in S' for any  $j \leq w_v$ . Therefore any maximum size cyclic stable set S' in D' naturally corresponds to a cyclic stable set S' in S' in S' naturally corresponds to a cyclic stable set S' of all copies of the vertices in S, is a cyclic stable set in S', with  $|S'| = w'x^S$ . Therefore given any vector S' with S' is a cyclic stable set in S' the linear program with objective function S' has an integral optimal solution. Therefore S' is totally dual integral, as we wished to show.

---

# 18.997 Topics in Combinatorial Optimization

9 March 2004

# Matroids

Lecturer: Michel X. Goemans Scribe: Bridget Eileen Tenner

For reference, see Chapter 39 of Schrijver's book.

**Definition 1** A matroid  $M = (S, \mathcal{I})$  is a finite ground set S together with a collection of sets  $\mathcal{I} \subseteq 2^S$ , known as the independent sets, satisfying the following axioms:

- 1. If  $I \in \mathcal{I}$  and  $J \subseteq I$  then  $J \in \mathcal{I}$ .
- 2. If  $I, J \in \mathcal{I}$  and |J| > |I|, then there exists an element  $z \in J \setminus I$  such that  $I + z \in \mathcal{I}$ , where + indicates union.

If  $I \subseteq S$  is not an element of  $\mathcal{I}$ , I is called a *dependent set*. An element  $I \in \mathcal{I}$  is a *basis* if it is a maximal (inclusion-wise) independent set. A *circuit* C of M is a minimal dependent set. A set  $I \in \mathcal{I}$  is a *spanning set* if I contains a basis.

## Example 1 Linear matroids.

Let A be an m-by-n matrix. Let  $S = \{1, ..., n\}$  be the index set of the columns of A.  $I \subseteq S$  is independent if the columns indexed by I are linearly independent.

It is straightforward to check that the axioms for a matroid hold in this example.

**Observation 1** All bases of a matroid have the same cardinality by the second axiom.

For  $T \subseteq S$ , let the rank of T be  $r_M(T) = r(T) = \max\{|I| : I \subseteq T \text{ and } I \in \mathcal{I}\}$ . Note that this is a generalization of the linear algebra definition of rank. Letting the set T equal S, we find that  $r_M(S) = |B|$ , the size of a basis of the matroid.

If F is a field, a matroid is said to be *representable* over F if the matrix A and linear independence are taken over F.

#### Example 2 Uniform matroids.

For any ground set S and a specific k, let  $I \in \mathcal{I}$  if  $|I| \leq k$ . Denote this matroid  $U_{|S|}^k$ .

The matroid  $U_4^2$  is a linear matroid: consider four vectors in the plane such that no two are multiples of each other. Then let each column of a 2-by-4 matrix A correspond to one of these vectors.

Can the matroid  $U_4^2$  be represented over another field? Let us consider this question for GF(2). That is, can we find a matrix A in which all entries are 0 or 1, no column is the zero vector, no two columns sum to the zero vector, but any three columns sum to the zero vector?

Before answering this question, observe the following: for any linear matroid, we can assume that the rank of the matrix A is m, since otherwise we could remove the redundant rows. By elementary operations, we can further assume that A has the form

$$\begin{bmatrix} I_m & B \end{bmatrix}$$

where B is an m-by-(n-m) matrix.

Returning to the question of  $U_4^2$  being representable over GF(2), if there was such a representation, then it would have the form

$$\begin{bmatrix} 1 & 0 & * & * \\ 0 & 1 & * & * \end{bmatrix}$$

where each \* is either 0 or 1. However, each of the columns must be distinct, and none can be  $(0,0)^T$  so there is no such representation. Thus the matroid  $U_4^2$  is uniform and linear, but is not representable over GF(2).

**Definition 2** A binary matroid is a linear matroid that can be represented over GF(2). A matroid is regular if it is representable over any field F.

## Example 3 Graphic matroids.

For an undirected graph G = (V, E), let the ground set S be the set E of edges of the graph. The matroid M(G), sometimes called the cycle matroid of G, is defined as  $M(G) = (E, \mathcal{I})$  where  $\mathcal{I} = \{F \subseteq E : F \text{ is acyclic}\}.$ 

It is straightforward to check that the axioms of a matroid hold in this example. In a graphic matroid, we can make the following observations:

- The bases are the spanning trees of G.
- The circuits are the circuits of the graph G.
- The spanning sets are the connected sets of G.
- The rank function is defined as  $r_{M(G)}(F) = |V| \kappa(V, F)$  where  $\kappa(H)$  is the number of connected components of a graph H.

Graphic matroids are linear. This can be seen by looking at the vertex/edge incidence matrix with a +1 and a -1 in each edge column (the order of these is unimportant). In fact, this representation works over any field F: let the +1 be the multiplicative identity in F and let the -1 be the additive inverse of this +1. Thus graphic matroids are regular.

The matroids defined so far can be classified in the following manner:

 $\{\text{graphic matroids}\}\subseteq \{\text{regular matroids}\}\subseteq \{\text{binary matroids}\}\subseteq \{\text{linear matroids}\}.$ 

# Example 4 Matching matroids.

Start with a graph G = (V, E). Let S = V, the set of vertices. A set  $I \subseteq S$  is independent if I can be covered by a matching. Note, if G has a perfect matching, every subset of the vertices can be covered.

The first axiom of a matroid is easy to check for matching matroids. Given the hypotheses of the second axiom, let  $M_J$  and  $M_I$  be the corresponding matchings of the independent sets J and I, respectively. If  $M_I$  covers one element in  $J \setminus I$ , the axiom obviously holds. So suppose this is not the case. Consider  $M_I \Delta M_J$ . Every vertex in  $J \setminus I$  has an alternating path that starts from that vertex. Some of these paths may end in  $I \setminus J$ , but they cannot all end there, since  $|J \setminus I| > |I \setminus J|$ . Thus at least one vertex in  $J \setminus I$  has a path that ends somewhere else. And that endpoint cannot be in  $J \cap I$  since these vertices have degree 0 or 2 in  $M_I \Delta M_J$ . Thus we have an alternating path P from  $J \setminus I$  to a vertex not in I. Now  $M_I \Delta P$  is a matching that covers I and one more vertex in  $J \setminus I$ .

**Example 5** Let G = (V, A) be a digraph. Suppose  $S \subseteq V$ . Assume there is a distinguished vertex  $s \in V$ . Let  $I \subseteq S$  be independent if there exist arc-disjoint paths from s to v for all  $v \in I$ .

As in the previous examples, the first axiom of matroids is clear for this example. The second axiom is essentially network flows: reverse the paths from s to the elements of the set J. These could share some of the arcs of the paths from s to the elements of the set I. When viewed as a whole, there are more sources (vertices of  $J \setminus I$ ) than sinks (vertices of  $I \setminus J$ ). Decompose this into paths and cycles. This yields at least one path from  $v \in J \setminus I$  to s.

This example can be generalized in the following manner. The ground set S is still a subset of V, but now instead of having a distinguished vertex s, there is a distinguished set  $U \subseteq V$ . A set  $I \subseteq S$  is independent if there exist *vertex*-disjoint paths from a subset  $T \subseteq U$ , |T| = |I|, to I. Such matroids are known as gammoids, and were developed by Perfect in 1968.

Consider a matroid  $M=(S,\mathcal{I})$ . The dual matroid is  $M^*=(S,\mathcal{I}^*)$  where  $\mathcal{I}^*=\{I\subseteq S:S\setminus I\text{ is a spanning set for }M\}$ . That is, the complement of a basis of M, as well as all subsets of this, is independent in  $M^*$ . The bases of  $M^*$  are the complements of the bases of M. It is straightforward to check that this is a matroid.

Suppose we take the cycle matroid of a planar graph G that is sufficiently connected to guarantee a unique embedding (three-connectivity does this). Define the dual graph in the standard way. Take a spanning tree of G and consider the edges not selected by this. Look at the corresponding edges in the dual graph. This gives a spanning tree in the dual graph. So the dual of this matroid is also graphic, and in this particular situation the dual matroid corresponds to the dual graph of the original graph. Tutte has shown that the dual of the cycle matroid of a graph G is also a graphic matroid if and only if G is planar.

Several properties of dual matroids are worth mentioning here. First, let us understand  $(M^*)^*$ . This is certainly a matroid, and the bases of this matroid are the bases of M. Thus  $(M^*)^* = M$ . Also, recall that to a matroid M we associate a rank function  $r_M$ . What is the rank function  $r_{M^*}$  associated to the dual  $M^*$ ? Let U be an independent set in  $M^*$ . Then, given that any basis B of M has size  $r_M(S)$  and that  $B \setminus U = B \cap (S \setminus U)$  is a largest independent set in  $S \setminus U$ ,

$$r_{M^*}(U) = \max_{\text{basis } B \text{ of } M} |U \setminus B|$$

$$= |U| - \min_{\text{basis } B \text{ of } M} |U \cap B|$$

$$= |U| - \left(r_M(S) - \max_{\text{basis } B \text{ of } M} |B \setminus U|\right)$$

$$= |U| - r_M(S) + r_M(S \setminus U).$$

There are additional operations (besides taking the dual) that can be performed on a matroid. For example if  $Z \subseteq S$ , we have the deletion  $M \setminus Z$  and the contraction M/Z.

Deletion:  $M \setminus Z = (S \setminus Z, \{I \subseteq S \setminus Z : I \text{ independent in } M\})$ . For example, take a graphic matroid and delete some of its edges. Look at acyclic subsets of the remaining edges. The rank function for this matroid is  $r_{M \setminus Z}(U) = r_M(U)$  for  $U \subseteq S \setminus Z$ .

Contraction:  $M/Z = (M^* \setminus Z)^*$ . From the formulas for the rank after taking the dual or after deleting elements, we get that

$$r_{M/Z}(U) = r_{(M^* \setminus Z)^*}(U) = |U| - r_{M^* \setminus Z}(S \setminus Z) + r_{M^* \setminus Z}(S \setminus Z \setminus U)$$

$$= |U| - r_{M^*}(S \setminus Z) + r_{M^*}(S \setminus Z \setminus U)$$

$$= |U| - (|S \setminus Z| - r_M(S) + r_M(Z)) + (|S \setminus Z \setminus U| - r_M(S) + r_M(Z \cup U))$$

$$= r_M(Z \cup U) - r_M(Z).$$

This can be interpreted as follows. Take any  $X \subseteq Z$  such that  $|X| = r_M(Z)$ , i.e. X is a maximal independent set in Z. Now, U will be independent in M/Z if  $r_M(Z \cup U) = |U| + r_M(Z) = |U| + |X| = |U \cup X|$  which means that  $U \cup X$  is independent in M. In other words, another (equivalent) definition for the contraction is

$$M/Z = (S \setminus Z, \{I \subseteq S \setminus Z : I \cup X \in \mathcal{I}\}).$$

By playing with the rank function, one can check that, for any disjoint sets Y and Z,  $(M/Z)/Y = M/(Y \cup Z) = (M/Y)/Z$ . And similarly for deletions. Moreover,  $(M/Z) \setminus X = (M \setminus X)/Z$ .

If M is representable over F, then  $M^*$  is also representable over F. This can be seen by taking the standard representation  $A = [I_m \ B]$  for M. This corresponds to a representation A' for  $M^*$  where  $A' = [B^T \ I_{n-m}]$ .

Also,  $M \setminus Z$  and M/Z can be represented over F if M can. The class of matroids representable over F is thus closed under taking minors.

Consider non-binary matroids. Look at the minor minimal non-binary matroids. There is only one, and this is  $U_4^2$ . Any other non-binary matroid has  $U_4^2$  as a minor. A major open problem, posed by Rota, is: for GF(q), do you need only a finite number of

A major open problem, posed by Rota, is: for GF(q), do you need only a finite number of obstructions for non-GF(q)-representable matroids? The GF(2) case was done by Tutte in 1958, and the GF(3) and GF(4) cases have been done since then. However, the general case is still open.

---

### 18.997 Topics in Combinatorial Optimization

March 11, 2004

Lecture 10

Lecturer: Michel X. Goemans Scribe: Nicole Immorlica

Matroid theory was first formalized in 1935 by Whitney [5] who introduced the notion as an attempt to study the properties of vector spaces in an abstract manner. Since then, matroids have proven to have numerous applications in a wide variety of fields including combinatorics and graph theory.

Today we will briefly survey matroid representation and then discuss some problems in matroid optimization and the corresponding applications. The tools we develop will help us answer the following puzzle:

**Puzzle:** A game is played on a graph G(V, E) and has two players, George and Ari. Ari's moves consist of "fixing" edges  $e \in E$ . George's moves consist of deleting any unfixed edge. The game ends when every edge has been either fixed or deleted. Ari wins if the graph at the end of the game is connected (i.e. if the fixed edges form a spanning tree). Otherwise George wins. Supposing George moves first, characterize the graphs in which George has a winning strategy.

## 1 Graphic Matroids

Let us begin with some comments regarding graphic matroids that arose during a discussion after class last time. Recall the *graphic matroid* of graph G is  $M(G) = (E, \mathcal{I} = \{F \subseteq E : F \text{ is acyclic}\})$ . For which graphs G and G does G and G does G and G does G and G does does during a figure 1 (a) and Figure 1 (b) respectively, G and G does during a figure 1 (b) respectively, G does during a figure 1 (c) respectively.

Figure 1: Switching operation preserves matroid representation.

We can think of H as being obtained from G by taking a vertex cut of size two and switching the roles of each vertex in one of the subgraphs. In fact, for 2-connected graphs, this operation always preserves the matroid representation.

**Theorem 1** If G and H are 2-connected, then M(G) = M(H) if and only if H can be obtained from G via a sequence of switching operations.

For higher connectivity, no opertaions exist that lead to the same matroid.

**Theorem 2** If G and H are 3-connected, then M(G) = M(H) if and only if G = H.

In general, graph (vertex) connectivity can be equated to a corresponding notion of matroid connectivity. In particular, it can be shown that a graphic matroid corresponding to a k-connected graph is k-connected and vice versa. However, we will not define matroid connectivity here.

Let us make one final observation concerning graphic matroids. Recall that last time we saw if a graph G is planar (we assumed sufficiently connected, so that it is uniquely embeddable, but this is not necessary), then  $M^*(G) = M(G^*)$  where the \* operation indicates taking the dual of the corresponding object. It can be shown that planar graphs are unique in this sense.

**Theorem 3 (Tutte)** The dual matroid of a graphic matroid M(G) corresponding to graph G is itself a graphic matroid if and only if G is planar.

## 2 Matroid Representation

We would like to characterize matroids representable over a finite field. As a first step, note a matroid and its dual are representable over the same fields.

**Theorem 4** If M is representable over F, then so is  $M^*$ .

**Proof:** Suppose the bases of M have size m. Then, by assumption, M can be represented by an  $m \times n$  matrix  $A = [I^{m \times m} | B^{m \times (n-m)}]$ . The columns of this matrix are indexed by the elements of the ground set. Let Z be a basis of M and rearrange the rows and columns of A such that  $Z = X_2 \cup Y_1$  where  $X_2$  and  $Y_1$  are as pictured (Figure 2(a)).

Figure 2: Representation of M and  $M^*$ .

Consider the matrix  $A^* = [B^T | I^{(n-m)\times(n-m)}]$  (Figure 2(b)). Since Z was a basis, B restricted to the  $X_1$  rows and  $Y_1$  columns has full rank. Thus the  $X_1$  columns in  $A^*$  also have full rank, and so  $Z^* = X_1 \cup Y_2$  is an independent set of vectors. By a similar argument, it is a maximal independent set and so is a basis. As  $Z^* = S \setminus Z$ ,  $Z^*$  is a basis of  $M^*$ . Since this is true for every basis Z of M,  $A^*$  is a representation of the dual matroid  $M^*$  of M.

In 1971, after characterizations of GF(2)- and GF(3)-representable matroids, Gian-Carlo Rota conjectured that the matroids representable over any finite field can be characterized by a finite list of excluded minors (just as, for example, planar graphs can be characterized as those graphs excluding  $K_{3,3}$  and  $K_5$  as minors). A minor of a matroid M is a matroid which can be obtained from M by contractions (defined last time) and deletions of elements of the ground set.

Binary matroids, or matroids representable over GF(2), were characterized by their excluded minors by Tutte in 1958 [4]. They are precisely the matroids which exclude  $U_4^2$  as a minor. (Observe

that the list of excluded minors should be closed under taking the dual, and indeed  $U_4^2$ 's dual is  $U_4^2$  itself.)

**Theorem 5** A matroid is binary if and only if it excludes  $U_4^2$  as a minor.

Tutte further characterized regular matroids, or matroids representable over any field.

**Definition 1** The Fano matroid is the matroid with ground set  $S = \{A, B, C, D, E, F, G\}$  whose bases are all subsets of S of size 3 except  $\{A, D, B\}$ ,  $\{B, E, C\}$ ,  $\{A, F, C\}$ ,  $\{A, G, E\}$ ,  $\{D, G, C\}$ ,  $\{B, G, F\}$ , and  $\{D, E, F\}$ .

Figure 3: Fano matroids

Note Fano matroids (and hence their duals, see Theorem 4), are representable over GF(2) by, for example,  $A = (0, 1, 0)^T$ ,  $B = (1, 0, 0)^T$ ,  $C = (0, 0, 1)^T$ ,  $D = (1, 1, 0)^T$ ,  $E = (1, 0, 1)^T$ ,  $F = (0, 1, 1)^T$ , and  $G = (1, 1, 1)^T$ . In fact, these two matroids are the minimal binary non-regular matroids.

**Theorem 6** A binary matroid is regular if and only if it excludes the Fano matroid  $F_7$  and its dual  $F_7^*$  as minors.

The ternary matroids, or matroids representable over GF(3) were characterized in the early 1970s in an unpublished work of Reid, later published by Bixby [1] and Seymour [3].

**Theorem 7** The ternary matroids are the matroids which exclude  $U_5^2$ ,  $U_5^{2*} = U_5^3$ ,  $F_7$ , and  $F_7^*$  as minors.

In 2000, Geelen, Gerards and Kapoor characterized matroids representable over GF(4) [2] by specifying seven excluded minors, a work for which they won the 2003 Fulkerson Prize.

The current state-of-the-art is represented in Figure 4.

**Remark:** Linear matroids are matroids that are representable over *some* field. Not all linear matroids are representable over the rationals. The Fano matroid is an example of a binary matroid that is not representable over the rationals:

If  $F_7$  is representable over the rationals, then it is representable over the reals. Since the basis has cardinality 3, it is representable over  $\Re^3$ . Assume such a representation. Since D, E, and F are dependent, they must define a plane that passes through the origin, say the xy-plane. Consider, say, D and E. Each of A, B, C, and G together with D and E form an independent set. Therefore, A, B, C, and G do not lie on the xy-plane. Thus we can project them onto the z=1 plane (i.e.

Figure 4: Classes of matroids.

scale them so that they lie in the z=1 plane). This new representation, say A', B', C', and G', preserves the independence relations and thus is also a representation of  $F_7$ . Now notice that  $\operatorname{span}(A,G)\cap\operatorname{span}(C,B)=\operatorname{span}(E)$ . As E lies in the xy-plane,  $\operatorname{span}(A,G)\cap(z=1)=\overline{A'G'}$  and  $\operatorname{span}(C,B)\cap(z=1)=\overline{B'C'}$  form two parallel lines. Similarly,  $\operatorname{span}(A,B)\cap(z=1)=\overline{A'B'}$  and  $\operatorname{span}(C,G)\cap(z=1)=\overline{C'G'}$  form two parallel lines. Thus A'B'C'G' is a parallelogram, and so its diagonals,  $\overline{B'G'}$  and  $\overline{A'C'}$  must intersect. However, this contradicts the fact that  $\operatorname{span}(A,C)\cap\operatorname{span}(B,G)=\operatorname{span}(F)$ .

# 3 Matroid Optimization

To show the power of matroids and just as a sample of things to come, we begin with a definition of the union of matroids. This definition will prove useful in answering questions like  $does\ G$  contain  $k\ disjoint\ spanning\ trees?$ 

**Definition 2** The matroid union  $\vee_{i=1}^k M_i$  of matroids  $M_1 = (S_1, \mathcal{I}_1), \ldots, M_k = (S_k, \mathcal{I}_k)$  is the matroid  $M = (\bigcup_{i=1}^k S_i, \mathcal{I})$  where  $\mathcal{I} = \{\bigcup_{i=1}^k I_i : I_i \in \mathcal{I}_i\}.$ 

We will show that M is a matroid; this is not completely obvious. Furthermore, one can characterize the size of a maximal independent subset in the union of matroids as follows.

**Lemma 8** Let  $M = \bigvee_{i=1}^k M_i$  for matroids  $M_i = (S_i, \mathcal{I}_i)$ . Then for any  $U \subseteq S$ ,  $r_M(U) = \min_{T \subseteq U} (|U - T| + \sum_{i=1}^k r_{M_i}(T \cap S_i)$  where  $r_M(U)$  is the rank of set U in matroid M.

We will see applications of this next time. Today we will discuss a simpler optimization problem, that of finding a maximum weight independent set in a matroid. Specifically, let  $M = (S, \mathcal{I})$  be a

matroid with an integral weight function w(s) for each  $s \in S$ . We would like to find an  $I \in \mathcal{I}$  of maximum weight.

Consider the greedy algorithm. First order the elements of S so that  $w(s_i) \geq w(s_{i+1})$ . Initialize I to the empty set. At step i, if  $\{s_i\} \cup I \in \mathcal{I}$ , set  $I \leftarrow \{s_i\} \cup I$ . We will prove that this algorithm is optimal with the aid of the following polytope due to Edmonds:

#### Matroid Polytope

$$x_s \ge 0 \qquad \forall s \in S$$
  
 $x(U) \le r(U) \qquad \forall U \subseteq S$ 

Note that the second inequality implies  $x_s \leq 1$  as the rank of a single vertex is at most one. We will show that this polytope is integral and that the vertices are the indicator vectors of independent sets of the matroid. Certainly all independent sets of the matroid satisfy that  $x(U) \leq r(U)$ .

**Theorem 9** The greedy algorithm finds a maximum weight independent set.

**Theorem 10** The matroid polytope of Edmonds is integral.

**Proof:** (of Theorems 9 and 10) Consider the linear program

$$\max \sum_{s \in S} w(s) x_s$$
s.t. 
$$\sum_{s \in U} x_s \le r(U) \qquad \forall U \subseteq S$$

$$x_s \ge 0 \qquad \forall s \in S$$

and its dual

$$\min \sum_{U \subseteq S} r(U)y_U$$
s.t. 
$$\sum_{U \ni s} y_U \ge w(s) \qquad \forall s \in S$$

$$y_U \ge 0 \qquad \forall U \subseteq S.$$

Consider adding the constraint that the  $y_U$  are integral to the dual. Let the optimal value of this extended dual be  $O_D$ , the optimal value of the primal be  $O_D$ , the optimal value of the dual be  $O_D$ , and the weight of the maximum independent set be  $W_I$ . We will construct feasible  $y_U$  for the extended dual such that the value of the program  $O_D'$  will equal the weight w(I) of the set I returned by the greedy algorithm. This will prove several facts. As  $w(I) \leq W_I \leq O_D = O_D \leq O_D'$ , this shows that the greedy algorithm is optimal, thus proving Theorem 9. Furthermore, this shows that the dual is integral for an arbitrary integral weight function, and thus the system is TDI. Together with the fact that the rank function is integral, this proves that the matroid polytope is integral, thus proving Theorem 10.

Let's prove that  $O_D' = w(I)$ . Label the elements of S in order of decreasing weight as the greedy algorithm does. Let  $U_i = \{s_1, \ldots, s_i\}$  and set  $y_{U_n} = w(s_n)$ ,  $y_{U_i} = w(s_i) - w(s_{i+1})$  for  $1 \le i \le n$ . For all other sets U, set  $y_U = 0$ . Note  $y_U \ge 0$  and  $y_U$  are integral by construction. The first constraint of the dual is also satisfied as, for all i,  $\sum_{U \ni s_i} y_U = \sum_{j \ge i} y_{U_j} = w(s_n) + \sum_{j=i}^{n-1} w(s_j) - w(s_{j+1}) = w(s_i)$ . Now consider the objective. Notice  $r(U_1) = 1$  if  $s_1 \in I$  and 0 otherwise. Similarly,  $r(U_i) - r(U_{i-1}) = 1$  if  $s_i \in I$  and 0 otherwise. Therefore,

$$O_D' = \sum_{U} r(U) y_U$$

$$= \sum_{i=1}^{n-1} r(U_i)(w(s_i) - w(s_{i+1})) + r(U_n)w(s_n)$$

$$= w(s_1)r(U_1) + \sum_{i=2}^{n} w(s_i)(r(U_i) - r(U_{i-1}))$$

$$= w(I).$$

## References

[1] R. Bixby. On reid's characterization of ternary matroids. J. Combin. Theory Ser. B, 26:174–204, 1979.

- [2] J. F. Geelen, A. M. H. Gerards, and A. Kapoor. The excluded minors for gf(4)-representable matroids. *Journal of Combinatorial Theory Series B*, 79, 2000.
- [3] P. Seymour. Matroid representation over gf(3). J. Coubin. Theory Ser. B, 26:159–173, 1979.
- [4] W. T. Tutte. A homotopy theorem for matroids, i, ii. Trans. Amer. Math Soc., 88:144–174, 1958.
- [5] H. Whitney. On the abstract properties of linear dependence. Amer. J. Math., 57:509–533, 1935.

---

#### 18.997 Topics in Combinatorial Optimization

16 March 2004

# Lecture 11

Lecturer: Michel X. Goemans Scribe: Fumei Lam

Let  $\mathcal{M}_1 = (S, \mathcal{I}_1), \mathcal{M}_2 = (S, \mathcal{I}_2)$  be two matroids on common ground set S with rank functions  $r_1$  and  $r_2$ . Many combinatorial optimization problems can be reformulated as the problem of finding the maximum size common independent set  $I \in \mathcal{I}_1 \cap \mathcal{I}_2$ . This problem was studied by Edmonds and Lawler, who proved the following min-max matroid intersection characterization.

### Theorem 1

$$\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| = \min_{U \in S} \left( r_1(U) + r_2(S \setminus U) \right).$$

As with many min-max characterizations, proving one of the inequalities is straightforward. For any  $U \subseteq S$  and  $I \in \mathcal{I}_1 \cap \mathcal{I}_2$ , we have

$$|I| = |I \cap U| + |I \cap (S \setminus U)|$$
  
 
$$\leq r_1(U) + r_2(S \setminus U),$$

since  $I \cap U$  is an independent set in  $\mathcal{I}_1$  and  $I \cap (S \setminus U)$  is an independent set in  $\mathcal{I}_2$ . Therefore,  $\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| \le \min_{U \in S} (r_1(U) + r_2(S \setminus U)).$ 

The following important examples illustrate some of the applications of the matroid intersection theorem.

## Examples

1. For a bipartite graph G = (V, E) with color classes  $V = V_1 \cup V_2$ , consider  $\mathcal{M}_1 = (E, \mathcal{I}_1)$  and  $\mathcal{M}_2 = (E, \mathcal{I}_2)$  where  $\mathcal{I}_i = \{F : \forall v \in V_i, \deg_F(v) \leq 1\}$  for i = 1, 2. Note that  $\mathcal{M}_1$  and  $\mathcal{M}_2$ are (partition) matroids, while  $\mathcal{I}_1 \cap \mathcal{I}_2$ , the set of bipartite matchings of G, does not define a matroid on E. Also, note that the rank  $r_i(F)$  of F in  $M_i$  is the number of vertices in  $V_i$ covered by edges in F. Then by Theorem 1, the size of a maximum matching in G is

$$\nu(G) = \min_{U \in E} (r_1(U) + r_2(E \setminus U))$$

$$= \tau(G)$$
(2)

$$= \tau(G) \tag{2}$$

where  $\tau(G)$  is the size of a minimum vertex cover of G. Thus, the matroid intersection theorem generalizes Kőnig's matching theorem.

2. As a corollary to Theorem 1, we have the following min-max relationship for the minimum common spanning set in two matroids.

$$\min_{F \text{ spanning in } M_1 \text{ and } M_2} |F| = \min_{B_i \text{ basis in } \mathcal{M}_i} |B_1 \cup B_2|$$

$$= \min_{B_i \text{ basis in } \mathcal{M}_i} |B_1| + |B_2| - |B_1 \cap B_2|$$

$$= r_1(S) + r_2(S) - \min_{U \subseteq S} [r_1(U) + r_2(S \setminus U)].$$

Applying this corollary to the matroids in example 1, it follows that the minimum edge cover in G is equal to the maximum of  $|V|-r_1(F)-r_2(E\setminus F)$  over all  $F\subseteq E$ . Since this is exactly the maximum size of a stable set in G, the corollary is a generalization of the Kőnig-Rado theorem.

3. Consider a graph G with a k-coloring on the edges, i.e., edge set E is partitioned into color classes  $E_1 \cup E_2 \cup \ldots \cup E_k$ . The question of whether or not there exists a rainbow spanning tree (i.e. a spanning tree with edges of different colors) can be restated as a matroid intersection problem on  $\mathcal{M}_1 = (E, \mathcal{I}_1)$  and  $\mathcal{M}_2 = (E, \mathcal{I}_2)$  with

$$\mathcal{I}_1 = \{F \subseteq E : F \text{ is acyclic}\}\$$
  
 $\mathcal{I}_2 = \{F \subseteq E : |F \cap E_i| \le 1 \ \forall i\}$ 

Since  $\mathcal{I}_1 \cap \mathcal{I}_2$  is the set of rainbow forests, there is a rainbow spanning tree of G if and only if

$$\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| = |V| - 1.$$

By Theorem 1, this is equivalent to the condition

$$\min_{U \subset E} (r_1(U) + r_2(E \setminus U)) = |V| - 1.$$

Since  $r_1(U) = |V| - c(U)$  (where c(U) denotes the number of connected components of (V, U)), it follows that there is a rainbow spanning tree of G if and only if the number of colors in  $E \setminus U$  is at least c(U) - 1 for any subset  $U \subseteq E$ . In other words, a rainbow spanning tree exists if and only if removing the edges of any t colors leaves a graph with at most t + 1 components.

- 4. Given a digraph G = (V, A), a branching D is a subset of arcs such that
  - (a) D has no directed cycles
  - (b) For every vertex  $v, \deg_{in}(v) \leq 1$  in D.

Branchings are the common independent sets of matroids  $\mathcal{M}_1 = (E, \mathcal{I}_1), \mathcal{M}_2 = (E, \mathcal{I}_2)$ , where

$$\mathcal{I}_1 = \{F \subseteq E : F \text{ is acyclic in the underlying undirected graph } G\}$$
  
 $\mathcal{I}_2 = \{F \subseteq E : \deg_{\text{in}}(v) \le 1 \ \forall v \in V\}$ 

Note that  $\mathcal{M}_1$  is a graphic matroid on G and  $\mathcal{M}_2$  is a partition matroid. Therefore, the problem of finding a maximum branching of a digraph can be solved by the matroid intersection algorithm.

In order to prove Theorem 1, we need the following lemmas. Recall that a circuit is a minimal dependent set.

**Lemma 2** Let  $M = (S, \mathcal{I})$  be a matroid. If  $I \in \mathcal{I}, I + x \notin \mathcal{I}$ , then I + x contains a unique minimal circuit.

**Lemma 3** (Basis exchange) Suppose  $B_1$  and  $B_2$  are two bases of a matroid  $\mathcal{M}$ . For any  $x \in B_1 \setminus B_2$ , there exists  $y \in B_2 \setminus B_1$  such that

$$B_1 - x + y \in \mathcal{I}$$
 and  $B_2 - y + x \in \mathcal{I}$ 

Given an independent set I in a matroid  $\mathcal{M} = (S, \mathcal{I})$ , we define a digraph with vertex set S and arc set  $A_M(I) = \{(x, y) : x \in I, y \in S \setminus I, I - x + y \in \mathcal{I}\}$ . We often drop the M subscript when referring to A. This digraph plays a crucial role in several matroid optimization algorithms including matroid intersection.

**Lemma 4** Let  $I, J \in \mathcal{I}$  with |I| = |J|. Then A(I) contains a matching on  $I\Delta J = (I \setminus J) \cup (J \setminus I)$ .

**Proof:** We can assume I, J are bases in  $\mathcal{I}$  (otherwise, consider the truncated matroid whose independent sets are those in  $\mathcal{I}$  of size less than or equal to |I|). We proceed by induction on  $|I \setminus J|$ . For any  $x \in I \setminus J$ , there exists  $y \in J \setminus I$  such that  $J' = J - y + x \in \mathcal{I}$ . Then  $I \setminus J' = (I \setminus J) - x$  and  $J' \setminus I = (J \setminus I) - y$ . If  $|I \setminus J| = 1$ , then we are done; otherwise by induction on  $|I \setminus J|$ , A(I) contains a matching on  $I \Delta J'$ , which we extend to a matching of  $I \Delta J$  by adding edge (x, y).

Unfortunately, the converse of this theorem is not true, as shown by the following counterexample. Let  $\mathcal{M}$  be the graphic matroid on the following graph G.

For  $I = \{e_1, e_2, e_3\}, J = \{f_1, f_2, e_3\}, A(I)$  contains a matching  $(e_1, f_1), (e_2, f_2)$  of  $I\Delta J$  and  $I \in \mathcal{I}$ , but  $J \notin \mathcal{I}$ .

However, by a slight strengthening of the condition, we can prove the following.

**Lemma 5** Given matroid  $\mathcal{M} = (S, \mathcal{I}), I \in \mathcal{I}$ , and  $J \subseteq S$  with |I| = |J|, if A(I) contains a unique matching on  $I\Delta J$ , then  $J \in \mathcal{I}$ .

Note that in the example above, A(I) also contains the matching  $(e_1, f_2), (e_2, f_1)$  on  $I\Delta J$ , so the stronger condition fails.

**Proof:** Let N denote the unique perfect matching on  $I\Delta J$  and consider the digraph in which we reverse the orientation of the arcs in N. By the uniqueness of the perfect matching, there are no directed cycles in the resulting graph, so there is a topological ordering of the vertices. This ordering induces a labeling on vertices in  $N = \{(y_1, z_1), (y_2, z_2), \dots (y_t, z_t)\}$  such that there are no arcs  $(y_i, z_j)$  for i < j.

If  $J \notin \mathcal{I}$ , then it contains a circuit C. Let i be the smallest index such that  $z_i \in C$ . Since there are no arcs from  $y_i$  to  $z_j$  with j > i,  $I - y_i + z_j \notin \mathcal{I}$ , implying  $z_j \in \operatorname{span}(I - y_i)$ . Since this is true for all j > i,  $C - z_i \subseteq \operatorname{span}(I - y_i)$ . But since C is a circuit,  $z_i \in \operatorname{span}(C - z_i) \subseteq \operatorname{span}(I - y_i)$ . Then  $I - y_i + z_i \notin \mathcal{I}$  and by definition of A(I),  $(y_i, z_i) \notin A(I)$  (since  $I - y_i + z_i \notin \mathcal{I}$ ), a contradiction to the existence of perfect matching N. Therefore  $J \in \mathcal{I}$ .

Now, we state the matroid intersection algorithm, whose proof we will give in the next lecture. Since  $\mathcal{I}$  may be exponential in size, we assume our matroid is described by an oracle which, given  $I \subseteq S$ , can determine in polynomial time if  $I \in \mathcal{I}$ . Then the running time of the algorithm is polynomial in the number of calls to the oracle.

First, for  $I \subseteq S$ , define the digraph D(I) = (S, A) as follows: for  $y \in I$ ,  $x \notin I$ , we have an arc  $(y, x) \in A$  if  $I - y + x \in \mathcal{I}_1$  and  $(x, y) \in A$  if  $I - y + x \in \mathcal{I}_2$ . This is the union of the arcset  $A_{M_1}(I)$  corresponding to  $\mathcal{I}_1$  and the reverse of the arcset  $A_{M_2}(I)$  corresponding to  $\mathcal{I}_2$ . Consider the sets

$$X_1 = \{x \in S \setminus I : I + x \in \mathcal{I}_1\}, X_2 = \{x \in S \setminus I : I + x \in \mathcal{I}_2\}.$$

### Matroid Intersection Algorithm

Input Matroids  $\mathcal{M}_1 = (S, \mathcal{I}_1)$ ,  $\mathcal{M}_2 = (S, \mathcal{I}_2)$ Output  $I \in \mathcal{I}_1 \cap \mathcal{I}_2$  of maximum size  $I \leftarrow \emptyset$ while D(I) has a path from  $X_1$  to  $X_2$  $I \leftarrow I\Delta V(P)$ , where P is a shortest path from  $X_1$  to  $X_2$ .

We will prove the correctness of this algorithm in the next lecture.

---

#### 18.997 Topics in Combinatorial Optimization

18 March 2004

#### Lecture 12

Lecturer: Michel X. Goemans Scribe: Vahab S. Mirrokni

Last time, we stated the following theorem by Edmonds and Lawler about the maximum independent set common to two matroids.

**Theorem 1** Let  $\mathcal{M}_1 = (S, \mathcal{I}_1)$  and  $\mathcal{M}_2 = (S, \mathcal{I}_2)$  be two matroids on common ground set S with rank functions  $r_1$  and  $r_2$ , then

$$\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| = \min_{U \in S} (r_1(U) + r_2(S \setminus U)).$$

To prepare for the proof, we proved some lemmas and stated the following algorithm. For  $I \subseteq S$ , let the digraph D(I) = (S, A) be defined as follows: for  $y \in I$ ,  $x \notin I$ , we have an arc  $(y, x) \in A$  if  $I - y + x \in \mathcal{I}_1$  and  $(x, y) \in A$  if  $I - y + x \in \mathcal{I}_2$ . This is the union of the arcset  $A_{\mathcal{M}_1}(I)$  corresponding to  $\mathcal{I}_1$  and the reverse of the arcset  $A_{\mathcal{M}_2}(I)$  corresponding to  $\mathcal{I}_2$ . Consider the sets

$$X_1 = \{x \in S \setminus I : I + x \in \mathcal{I}_1\}, X_2 = \{x \in S \setminus I : I + x \in \mathcal{I}_2\}.$$

The algorithm is as follows:

Matroid Intersection Algorithm (MIA)

Input Matroids  $\mathcal{M}_1 = (S, \mathcal{I}_1), \, \mathcal{M}_2 = (S, \mathcal{I}_2)$ 

Output  $I \in \mathcal{I}_1 \cap \mathcal{I}_2$  of maximum size

 $I \leftarrow \emptyset$ 

while D(I) has a path from  $X_1$  to  $X_2$ 

 $I \leftarrow I\Delta V(P)$ , where P is a shortest path from  $X_1$  to  $X_2$ .

The choice of a *shortest* path P is crucial; otherwise, the algorithm is not correct. The correctness of the algorithm is proved below.

**Theorem 2** In any step of Algorithm MIA, if there is no path from  $X_1$  to  $X_2$  then I is of maximum size. Otherwise, if P is a shortest path from  $X_1$  to  $X_2$  then  $J = I\Delta V(P)$  is an independent set in  $\mathcal{I}_1$  and  $\mathcal{I}_2$ .

**Proof:** If there is no path from  $X_1$  to  $X_2$  then let U be the set of vertices that can reach  $X_2$ . By assumption,  $U \cap X_1 = \emptyset$  (and  $(S \setminus U) \cap X_2 = \emptyset$ ). We show that  $r_1(U) = |I \cap U|$  and  $r_2(S \setminus U) = |I \cap (S \setminus U)|$ . For contradiction, assume that  $|I \cap U| \neq r_1(U)$ , then  $|I \cap U| < r_1(U)$ . Thus, there exists  $x \in U \setminus I$  such that  $(I \cap U) + x \in \mathcal{I}_1$ , but we know that  $I + x \notin \mathcal{I}_1$ , since otherwise x would be both in  $X_1$  and in U and there would be a path from  $X_1$  to  $X_2$ . Since both  $(I \cap U) + x$  and I are independent, we can repeatedly add elements of the latter to the former until we get an independent set of size |I|. Thus there exists a  $y \in I \setminus U$  such that  $I + x - y \in \mathcal{I}_1$ . By definition, there is an edge from y to x in D(I) and it contradicts the definition of U. Similarly, one can prove that  $r_2(S \setminus U) = |I \cap (S \setminus U)|$ . This shows that I is of maximum size since  $|I| = |I \cap U| + |I \cap (S \setminus U)| = r_1(U) + r_2(S \setminus U)$ .

To prove the second statement, let P be a shortest path from  $X_1$  (say  $x_1 \notin I$ ) to  $X_2$  and  $J = I\Delta V(P)$ . We prove that  $J \in \mathcal{I}_1$  and similarly one can prove  $J \in \mathcal{I}_2$ . We augment the matroid  $\mathcal{M}$  to  $\mathcal{M}' = (S + t, \{I'|I' \setminus \{t\} \in \mathcal{I}_1\})$ . Now in  $D_{\mathcal{M}'}(I')$ , t is connected (only) to  $X_1$  and  $J \cup \{t\}$  has a unique matching. This matching comes from taking the arcs of P of  $A_{\mathcal{M}_1}(I)$  and adding  $(t, x_1)$ . The fact that it is unique comes from the fact that P is a shortest path; otherwise another matching would lead to a shortcut in P. Now, we use the following lemma that we proved last time,

**Lemma 3** Given matroid  $\mathcal{M} = (S, \mathcal{I}), I \in \mathcal{I}$ , and  $J \subseteq S$  with |I| = |J|, if  $A_{\mathcal{M}}(I)$  contains a unique matching on  $I\Delta J$ , then  $J \in \mathcal{I}$ .

Using this lemma,  $J \cup \{t\} \in \mathcal{I}(\mathcal{M}')$ . Thus,  $J \in \mathcal{I}_1$  as desired. Similarly, one can show that  $J \in \mathcal{I}_2$ .

Note that in the proof of Theorem 2, we showed that at the end of the algorithm (when there is no path from  $X_1$  to  $X_2$ ), there exists a set U for which the equality of Theorem 1 holds. Thus, the proof of Theorem 2 also shows Theorem 1.

## 1 Intersection of Many Matroids

Despite intersection of two matroids, the problem of finding the independent set of maximum size in the intersection of three matroids is NP-Hard.

**Theorem 4** Given three matroids  $\mathcal{M}_1, \mathcal{M}_2, \mathcal{M}_3$  where  $\mathcal{M}_i = (S, \mathcal{I}_i)$ , it is NP-hard to find the independent set I with maximum size in  $\mathcal{I}_1 \cap \mathcal{I}_2 \cap \mathcal{I}_3$ .

**Proof:** The reduction is from the Hamiltonian path problem. Let D=(V,E) be a directed graph and s and t are two vertices in D. Given an instance (D=(V,E),s,t) of the Hamiltonian path problem, we construct three matroids as follows:  $\mathcal{M}_1$  is equal to the graphic matroid of the undirected graph G which is the undirected version of D.  $\mathcal{M}_2=(E,\mathcal{I}_2)$  is a partition matroid in which a subset of edges in an independent set if each vertex has at most one incoming edge in this set, i.e,  $\mathcal{I}_2=\{F\subseteq E: |\delta^-(v)\cap F|\leq f_s(v)\}$  where  $f_s(v)=1$  if  $v\neq s$  and  $f_s(s)=0$ . Similarly, we define  $\mathcal{M}_3=(E,\mathcal{I}_3)$  such that  $\mathcal{I}_3=\{F\subseteq E: |\delta^+(v)\cap F|\leq f_t(v)\}$  where  $f_t(v)=1$  if  $v\neq t$  and  $f_t(t)=0$ . It is easy check that any set in the intersection of these matroids corresponds to the union of vertex-disjoint directed paths with one of them starting at s and one (possibly a different one) ending at s. Therefore, the size of this set is s0 if and only if there exists a Hamiltonian path from s1 to s2 in s3.

# 2 Maximum Weight Common Independent set of two matroids

We give an algorithm to find the maximum weight common independent set of two matroids. Here is a brief description of the algorithm. At step i of the algorithm, we find the maximum weight independent set of size i and at the end, we output the independent set of maximum weight among all of these independent sets.

We start from an empty set as  $I_0$ . Suppose  $I_i$  is a maximum weight common independent set of size i. Let l(s) = w(s) if  $s \in I_i$  and l(s) = -w(s) if  $s \notin I_i$ . We find the maximum weight common independent set of size i + 1 by first constructing the digraph D(I) as in the maximum cardinality matroid intersection algorithm and then by proceeding as follows:

- 1. If no path from  $X_1$  to  $X_2$  exists, then there is no larger common independent set
- 2. else find a path, P, from  $X_1$  to  $X_2$  of shortest total length l(P) and if several paths have the same weighted length l(P), we choose the path among them with minimum number of vertices. Then  $I_{i+1} = I_i \Delta V(P)$ .

The fact that we started from a maximum weight independent set of size i can be seen to imply that the weighted digraph we construct has no negative length directed cycles (and hence the computation of the shortest path P makes sense and can be done efficiently). For the proof of the correctness of this algorithm, we refer the reader to the textbook.

## 3 Matroid Intersection Polytope

Edmonds [1970] has characterized all inequalities defining the *matroid intersection polytope*, the convex hull of independent sets common to two matroids. In this lecture, we state the characterization of this polytope. In the next lecture, we prove its integrality by showing in a very elegant way that the corresponding system of linear inequalities is totally dual integral.

Given matroids  $\mathcal{M}_1(S,\mathcal{I}_1)$  and  $\mathcal{M}_2(S,\mathcal{I}_2)$ , the matroid intersection polytope is the following:

$$x(U) \le r_1(U) \quad \forall U \subseteq S$$
  
 $x(U) \le r_2(U) \quad \forall U \subseteq S$   
 $x_s \ge 0 \quad \forall s \in S$ 

where  $x_s$  is a variable for each element s of S; and  $x(U) = \sum_{s \in U} x_s$ .

#### 4 Matroid Union

Given k matroids  $(\mathcal{M}_i = (S_i, \mathcal{I}_i)|_{i=1}^k)$  on possibly different ground sets, it can be shown that the independence system  $(\bigcup_{i=1}^k S_i, \{\bigcup_{i=1}^k I_i | I_i \in \mathcal{I}_i \text{ for } 1 \leq i \leq k\})$  is a matroid called the union matroid of  $\mathcal{M}_1, \mathcal{M}_2, \ldots, \mathcal{M}_k$  denoted by  $\mathcal{M} = \mathcal{M}_1 \vee \mathcal{M}_2 \vee \ldots \vee \mathcal{M}_k$ . The rank function of matroid  $\mathcal{M}$  is  $r_{\mathcal{M}}(U) = \min_{T \subset U} \left[ (U \setminus T) + \sum_{i=1}^k r_i(T \cap S_i) \right]$  for any  $U \subset \bigcup_{i=1}^k S_i$  (the fact that the rank function is at most this quantity is very easy to see since  $I \cap T \cap S_i$  over all i covers  $I \cap T$ ). Next lecture, we will prove these facts about matroid union by deducing them from matroid intersection.

Let  $\mathcal{M}^{(k)}$  be the union of k copies of matroid  $\mathcal{M}$ . By the above formula, we have  $r_{\mathcal{M}^{(k)}}(U) = \min_{T \subseteq U}(|U \setminus T| + kr_{\mathcal{M}}(T))$ . Thus, S has k disjoint bases if and only if  $kr_{\mathcal{M}}(S) = \min_{T \subseteq U}(|U \setminus T| + kr_{\mathcal{M}}(T))$ . This is equivalent to saying that for all  $T \subseteq S$ :  $|S \setminus T| \ge k(r_{\mathcal{M}}(S) - r_{\mathcal{M}}(T))$ . In addition, S can be covered by k independent sets if and only if for all  $T \subseteq S$ :  $|T| \le kr_{\mathcal{M}}(T)$ . Nash-Williams and Tutte-Nash-Williams theorems in graphs are corollaries of these facts. See Lecture 14 for precise statement and proofs.

## 5 Shannon Switching Game

Here, we state the generalization of the two-player game from Lecture 11 (on general matroids) and show the winning strategy in these games. The game is played on a matroid  $\mathcal{M}=(S,\mathcal{I})$ . Player 2's moves consist of fixing an element of S and player 1's moves consist of deleting any unfixed element in S. The game ends when every element has been fixed or deleted. Player 1 plays first. Player 2 wins if he can fix a basis of the matroid. Otherwise player 1 wins. The question is to find the winning strategy of this game.

First, note that given a matroid  $\mathcal{M}$ , either player 1 or 2 has a winning strategy. So the problem is to characterize the set of all graphs for which player 2 has a winning strategy.

**Theorem 5** Player 2 has a winning strategy if and only if S has two disjoint bases.

#### **Proof:**

Case 1: If S does not have two disjoint bases then, from the results above regarding the union of two identical matroids, we derive that there exists a subset  $T \subseteq S$  such that  $|S \setminus T| < 2(r_{\mathcal{M}}(S) - r_{\mathcal{M}}(T))$ . Now the strategy of player 1 is to always delete an element from  $S \setminus T$ . Therefore, player 1 can delete at least  $\left\lceil \frac{|S \setminus T|}{2} \right\rceil$  of elements. Hence, player 2 can fix at most  $\left\lfloor \frac{|S \setminus T|}{2} \right\rfloor < r_{\mathcal{M}}(S) - r_{\mathcal{M}}(T)$  elements within  $S \setminus T$  and  $r_{\mathcal{M}}(T)$  elements within T. Thus, player 2 can fix less than  $r_{\mathcal{M}}(S)$  elements and will not be able to fix a basis.

Case 2: In this case,  $\mathcal{M}$  has two disjoint bases  $B_1$  and  $B_2$ . Note that fixing an element is like contracting an element in the matroid and removing one element is like deleting the element from the matroid. From Lecture 9, we know that for any two subsets E and F of  $\mathcal{M}$ ,  $(\mathcal{M} \setminus E)/F = (\mathcal{M}/F) \setminus E$ . This means that the order of deleting or contracting (fixing) the elements does not matter. After k moves of both players, let  $E = \{e_1, e_2, \ldots, e_k\}$  be the set of elements that player 1 has deleted and  $F = \{f_1, f_2, \ldots, f_k\}$  be the set of elements that player 2 has fixed. We prove by induction that player 2 can play in such a way that after his move, there still exist two disjoint bases  $A_1$  and  $A_2$  in the remaining matroid  $\mathcal{M}' = (\mathcal{M} \setminus E)/F$ . By assumption, the base of the induction is true by taking  $\mathcal{M}' = \mathcal{M}$  and  $A_1 = B_1$  and  $A_2 = B_2$ . We assume there exist two disjoint bases  $A_1$  and  $A_2$  in  $\mathcal{M}' = (\mathcal{M} \setminus E)/F$ . Now, if player 1 deletes element  $e_{k+1}$ , say from  $A_1$ , then from the basis exchange property, we can find  $f_{k+1} \in A_2$  such that  $A_1 - \{e_{k+1}\} + f_{k+1} \in \mathcal{I}'$ . Restated, this means that  $A_1 - \{e_{k+1}\}$  is a basis for  $\mathcal{M}' \setminus \{e_{k+1}\}/\{f_{k+1}\}$ , and so is  $A_2 - \{f_{k+1}\}$ . We therefore have two disjoint bases in  $\mathcal{M}' \setminus \{e_{k+1}\}/\{f_{k+1}\}$ , and we can proceed.

---

#### 18.997 Topics in Combinatorial Optimization

March 30, 2004

## Lecture 13

Lecturer: Michel X. Goemans Scribe: Constantine Caramanis

Last lecture we covered matroid intersection, and defined matroid union. In this lecture we review the definitions of matroid intersection, and then show that the matroid intersection polytope is TDI. This is Chapter 41 in Schrijver's book. Next we review matroid union, and show that unlike matroid intersection, the union of two matroids is again a matroid. This material is largely contained in Chapter 42 in Schrijver's book. We leave testing independence in the union matroid for the next lecture.

### 1 Matroid Intersection

Matroid intersection is defined for two matroids on the same ground set,  $M_1 = (S, \mathcal{I}_1)$ ,  $M_2 = (S, \mathcal{I}_2)$ . In the last lecture, we saw that the size of the largest independent set in the intersection is given by:

$$\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| = \min_{U \subseteq S} \{ r_1(U) + r_2(S \setminus U) \},$$

where  $r_1$  ( $r_2$ ) is the rank function of the first (second) matroid. Also in last lecture, we defined the matroid intersection polytope:

$$\mathcal{P} \stackrel{\triangle}{=} \left\{ \begin{array}{ll} x(U) & \leq & r_1(U) & \forall U \subseteq S \\ x(U) & \leq & r_2(U) & \forall U \subseteq S \\ x & \geq & 0 \end{array} \right\}.$$

**Theorem 1** The polytope  $\mathcal{P}$  defined above is totally dual integrable (TDI).

In fact more is true. Schrijver shows that  $\mathcal{P}$  is Box-TDI, which means that  $\mathcal{P}$  is TDI, and so is  $\mathcal{P} \cap \{x : l_i \leq x_i \leq u_i\}$ , for any integral lower and upper bounds  $l_i, u_i \in \mathbb{Z}$ .

**Proof:** We need to show that for all choices of integral weight function  $w \in \mathbb{Z}^n$ , the dual of the LP

$$\max: \quad w^T x$$
s.t.:  $x \in \mathcal{P}$ ,

is integral. The dual is given by

min: 
$$\sum_{U \subseteq S} y_1(U)r_1(U) + \sum_{U \subseteq S} y_2(U)r_2(U)$$
s.t.: 
$$\sum_{U:i \in U} (y_1(U) + y_2(U)) \le w_i, \quad \forall i$$
$$y_1(U), y_2(U) \ge 0.$$

Recall that a matrix A is called totally unimodular (TUM) if and only if any square submatrix B is such that  $\det(B) \in \{0, \pm 1\}$ . If an LP is defined by a TUM matrix A, then it must be integral. The matrix that defines the dual above is not, however, TUM. We show that we can restrict the dual, setting a subset of the variables to zero, still obtaining an equivalent formulation. We show that in this equivalent, restricted formulation, the defining matrix is in fact totally unimodular.

Let the optimum value of the dual be attained at the point  $(y_1^*, y_2^*)$ . The first component of the solution,  $y_1^*$ , can be regarded as the optimal solution to the problem

min: 
$$\sum_{U \subseteq S} y_1(U)r_1(U)$$
s.t.: 
$$\sum_{U:i \in U} y_1(U) \le w_i - \sum_{U:i \in U} y_2^*(U)$$

$$y_1(U) \ge 0.$$

This is the dual of a maximum independent set problem in  $M_1$ , with weight vector  $\hat{w}$ , where  $\hat{w}_i = w_i - \sum_{U:i \in U} y_2^*(U)$ . In Lecture 11 (and also in Schrijver, Chapter 40.2) we saw that the greedy algorithm optimally solves maximum independent set problems in matroids. The greedy algorithm orders the elements of the ground set in non-increasing order, according to the weight function  $\hat{w}$ . Then, letting  $U_i := \{s_1, \ldots, s_i\}$ , the greedy algorithm can be used to exhibit a dual solution where  $y_1(U_i) = \hat{w}(s_i) - \hat{w}(s_{i+1})$ , and  $y_1(U) = 0$  for  $U \neq U_i$  for some i. Let  $\mathcal{F}_1$  denote the sets U of the above form. Note that  $\mathcal{F}_1$  is a (nested) chain of sets. Therefore, using the greedy algorithm, we can assume that given  $y_2^*$ , the corresponding problem in  $y_1$  has an optimal solution  $y_1^*$  that satisfies  $y_1^*(U) = 0$  for  $U \notin \mathcal{F}_1$ .

Similarly, for any fixed  $y_1^*$ , the resulting problem in  $y_2$  can be solved as the dual to a maximum independent set problem, and therefore there is a nested chain of subsets  $\mathcal{F}_2$ , such that there exists an optimal solution  $y_2^*$  with  $y_2^*(U) = 0$  for  $U \notin \mathcal{F}_2$ .

Therefore we have shown that the dual problem above is equivalent to the restriction

$$\begin{aligned} & \text{min}: & & \sum_{U\subseteq S} y_1(U)r_1(U) + \sum_{U\subseteq S} y_2(U)r_2(U) \\ & \text{s.t.}: & & \sum_{U:i\in U} (y_1(U) + y_2(U)) \leq w_i, \quad \forall \, i \\ & & y_1(U) = 0, \quad \forall \, U \notin \mathcal{F}_1 \\ & & y_2(U) = 0, \quad \forall \, U \notin \mathcal{F}_2 \\ & & y_1(U), y_2(U) \geq 0. \end{aligned}$$

The important point is that  $\mathcal{F}_1$  and  $\mathcal{F}_2$  are sets of nested subsets of the ground set S. Let A denote the nonzero columns of the matrix defining the restricted dual problem above. The next theorem says that the restricted matrix A is in fact totally unimodular. This implies that the dual problem is integral, and hence concludes the proof of the theorem.

We have left to prove that the matrix A above is in fact totally unimodular. First, we give a definition:

**Definition 1** A collection of sets  $\mathcal{F}$  is called laminar if  $A, B \in \mathcal{F}$  implies that  $A \subseteq B$ ,  $B \subseteq A$ , or  $A \cap B = \emptyset$ .

**Theorem 2** If  $\mathcal{F}$  is the union of two laminar families of subsets of a set X, then the  $X \times \mathcal{F}$  incidence matrix of  $\mathcal{F}$ , is totally unimodular.

First, note that since  $\mathcal{F}_1$  and  $\mathcal{F}_2$  each are a nested chain of subsets, they are both laminar, and hence the matrix A indeed satisfies the hypotheses of the theorem. Also note that the theorem fails if  $\mathcal{F}$  is the union of *three* laminar families. For (a somewhat trivial) example, we have

$$\det\left(\left[\begin{array}{ccc} 1 & 1 & 0 \\ 1 & 0 & 1 \\ 0 & 1 & 1 \end{array}\right]\right) = -2.$$

The matrix is the incidence matrix of the union of three laminar families (each laminar family contains only one set), yet the determinant of the matrix is -2, and thus it cannot be totally unimodular.

**Proof:** Let A be our matrix, which is the incidence matrix of a set  $\mathcal{F}$ , which is the union of two laminar families:  $\mathcal{F} = \mathcal{F}_1 \cup \mathcal{F}_2$ . Let B be any square submatrix. We need to show that  $\det(B) \in \{0, \pm 1\}$ . The columns of A each correspond to an element of the family  $\mathcal{F}$ .

Consider now the columns of matrix B. Some of them come from  $\mathcal{F}_1$ , and others from  $\mathcal{F}_2$ . Consider any two columns  $C_1, C_2$  of B (or the sets corresponding to them) such that both are elements of one of the two families  $\mathcal{F}_i$  and  $C_1 \subseteq C_2$ . By replacing  $C_2$  by the componentwise difference,  $C_2 - C_1$ , we can at most change the sign of the determinant. Repeating this procedure for all pairs of columns of B coming from  $\mathcal{F}_1$ , and then for all columns coming from  $\mathcal{F}_2$ , we obtain a matrix  $\hat{B}$ , whose determinant has the same magnitude as the determinant of B. In addition all columns corresponding to  $\mathcal{F}_1$  (resp.  $\mathcal{F}_2$ ) correspond to disjoint sets.

The matrix  $\hat{B}$  has at most 2 one's in each row. If there exists a row with no one's, then  $\det(B) = 0$  and we are done. If there exists a row with a single one, then the proof follows by induction, since we can expand by minors about that entry, thus reducing the size of the matrix we are considering. Finally, if all rows have two ones, then by the construction of  $\hat{B}$ , the sum of the columns from  $\mathcal{F}_1$  must equal the sum of the columns from  $\mathcal{F}_2$ , and hence  $\det(\hat{B}) = \det(B) = 0$ . This concludes the proof of the theorem.

# 2 Matroid Union

We saw in the last lecture that the intersection of two matroids (on the same ground set) need not be a matroid (but nevertheless had nice properties). Consider, for example, the ground set  $\{a,b,c\}$ , and the two matroids given by the independent sets  $\mathcal{I}_1 = \{\emptyset, \{a\}, \{b\}, \{c\}, \{a,b\}, \{b,c\}\}\}$  and  $\mathcal{I}_2 = \{\emptyset, \{a\}, \{b\}, \{c\}, \{a,b\}, \{a,c\}\}\}$ . The intersection is not a matroid.

In this section, we show that the union of matroids is again a matroid. Then, take matroids,  $M_1 = (S_1, \mathcal{I}_1), \ldots, M_k = (S_k, \mathcal{I}_k)$ . The union matroid is defined as  $M = (S, \mathcal{I})$ , where  $S \stackrel{\triangle}{=} S_1 \cup \cdots \cup S_k$ , and

$$\mathcal{I} \stackrel{\triangle}{=} \mathcal{I}_1 \vee \cdots \vee \mathcal{I}_k = \{I_1 \cup \cdots \cup I_k : I_i \in \mathcal{I}_i, i = 1, \dots, k\}.$$

**Theorem 3** The union matroid  $M = (S, \mathcal{I})$  as given above, is indeed a matroid.

When the ground sets are disjoint, it is straightforward to see that M is in fact a matroid. For the case where the ground sets  $S_i$  are not all disjoint, we use the following lemma.

**Lemma 4** Given any matroid  $M' = (S', \mathcal{I}')$ , and any function (not necessarily injective)  $f: S' \to S$ , then  $M = (S, f(\mathcal{I}'))$  is a matroid, where

$$f(\mathcal{I}') = \{ f(I') : I' \in \mathcal{I}' \}.$$

**Proof:** Since f is a function, it is clear that if  $I \in f(\mathcal{I}')$ , then any subset of I is also in  $f(\mathcal{I}')$ . Now suppose  $I, J \in f(\mathcal{I}')$ , with |I| < |J|. We need to show that for some  $j \in J \setminus I$ ,  $I + j \in f(\mathcal{I}')$ . By assumption (and definition) I and J must be images of two independent sets I', J' of M'. Since f is not injective, there may be many ways to choose such sets. We take I', J' so that I = f(I') and |I| = |I'|, J = f(J') and |J| = |J'|, and finally, such that  $|I' \cap J'|$  is maximal.

Since |I'| < |J'| and M' is, by assumption, a matroid, then there exists an element  $t \in J' \setminus I'$  such that  $I + t \in \mathcal{I}'$ . If  $f(t) \in f(I') \cap f(J')$ , then there exists some  $u \in I'$  such that f(t) = f(u). Since |J'| = |J|, f maps J' injectively onto J, and thus  $u \in I' \setminus J'$ . But then the set  $I'' = I' - u + t \in \mathcal{I}$  (because  $I' + t \in \mathcal{I}$ ), f(I'') = I, |I''| = |I|, and  $|I'' \cap J'| > |I' \cap J'|$  contradicting maximality. Therefore  $f(t) \in f(J') \setminus f(I')$ , and  $f(I' + t) = f(I') + f(t) \in f(\mathcal{I})$ , as required.

The proof of the matroid union theorem follows quickly from the lemma.

**Proof:** Let  $\{S_i'\}_{i=1}^k$  be disjoint copies of the original ground sets  $S_i$ , and  $\mathcal{I}_i'$  the corresponding independent sets. Let  $S' = S_1' \cup \cdots \cup S_k'$ , and let  $\mathcal{I}' = \{I' = I_1' \cup \cdots \cup I_k' : I_i' \in \mathcal{I}_i'\}$ . Then  $M' = (S', \mathcal{I}')$  is a matroid. For S the union (not disjoint) of the ground sets of the matroids, we have a map  $f: S \to S'$ . The union matroid  $M = (S, \mathcal{I})$  is the image of the matroid M' above, under the map f. The above lemma now applies directly, and we conclude that  $M = (S, \mathcal{I}) = (S, f(\mathcal{I}'))$  is indeed a matroid.

Next we determine the rank function of the union matroid. Again we consider the more general setup of the lemma above. Under the same definitions, we have:

**Lemma 5** If the rank function of  $M' = (S', \mathcal{I}')$  is r', then the rank function of the matroid  $M = (S, f(\mathcal{I}'))$  is given by

$$r(U) = \min_{T \subseteq U} (|U \setminus T| + r'(f^{-1}(T))).$$

**Proof:** The independent sets of M are the images of independent sets in M'. Therefore the size of the largest independent set  $I \subset U$  in M, is the size of the largest independent set  $I' \in f^{-1}(U)$  in M', that maps injectively to I = f(I'). Therefore we are asking for the size of the largest common independent set in in M' and in the partition matroid we obtain from the inverse mapping  $f^{-1}$ . Recall that for two matroids  $M_1, M_2$  on the same ground set S, we have the formula

$$\max_{I \in \mathcal{I}_1 \cap \mathcal{I}_2} |I| = \min_{U \subseteq S} \{ r_1(U) + r_2(S \setminus U) \}.$$

Thus we have

$$r(U) = \min_{T \subset U} (|U \setminus T| + r'(f^{-1}(T))).$$

Applying this result to the union matroid, we find that the rank function is given by

$$r_{\mathrm{union}}(U) = \min_{T \subseteq U}(|U \setminus T| + r_1(T \cap S_1) + \dots + r_k(T \cap S_k)),$$

for  $U \subseteq S_1 \cup \cdots \cup S_k$ 

### 3 Next Lecture

We still have not discussed how we might actually test independence in a union matroid. To see that this is not a trivial problem, consider, for example, the matroid whose independent sets are the forests of a graph. We can consider the union matroid on k copies of the graph. Now a set will be independent if it is the union of k forests. Given such a union, how can we determine if a given edge e may be added in order to obtain a larger independent set? Even given an explicit decomposition of the union into k forests, this is a nontrivial problem, since the given decomposition need not be unique. This is one of the issues addressed in the next lecture.

---

## 18.997 Topics in Combinatorial Optimization

April 1st, 2004

## Lecture 14

Lecturer: Michel X. Goemans Scribe: Mohamed Mostaqir

In this lecture, we continue with more results on matroid union, as well as tie together some loose ends from the past couple of lectures.

## 1 Testing for Independence

Recall from the matroid union theorem (lectures 12 and 13) that if  $M_1 = (S_1, \mathcal{I}_1), ..., M_k = (S_k, \mathcal{I}_k)$  are matroids, then their union  $M_1 \vee ... \vee M_k = (S_1 \cup ... \cup S_k, \{I_1 \cup ... \cup I_k : I_i \in \mathcal{I}_i\})$  is also a matroid. If I is an independent set in the union, then  $I \in \mathcal{I}_1 \vee ... \vee \mathcal{I}_k$ . We're interested in determining whether I+s is also in the union, i.e. if we add an element s to I, then does  $I+s \in \mathcal{I}_1 \vee ... \vee \mathcal{I}_k$ ? Is I+s still independent? In order to help answer this question, we give the following construction. For each matroid  $M_i$ , define an arc set  $D_{M_i}(I_i) = \{(x,y) : x \in I_i, y \notin I_i, I_i - x + y \in \mathcal{I}_i\}$ . That is,  $D_{M_i}(I_i)$  is the set of pairs of elements, where removing the first element from I and adding the second still leaves us with an independent set. Let  $D = \bigcup D_{M_i}(I_i)$  be the superposition of all the  $D_{M_i}(I_i)$ 's. We will show that shortest paths in D can be used to obtain other independent sets in the union. We give one more definition before stating the main result of this section. Let  $F_i = \{x : I_i + x \in \mathcal{I}_i\}$ , and let  $F = \bigcup F_i$ .

**Theorem 1** Let I be an independent set in the union. Then  $I + s \in \mathcal{I}_1 \vee ... \vee \mathcal{I}_k$  iff  $\exists$  an F - s path in D.

**Proof:** ( $\Downarrow$ ) We first show that if there is no F-s path in D, then I+s is not independent. Define  $T=\{v:\exists \text{ a } v-s \text{ path in } D\}$ , and assume that  $\nexists$  an F-s path in D, i.e.  $T\cap F=\emptyset$ . The following claim helps us in proving this direction.

**Claim 2**  $|I_i \cap T|$  is a maximal independent subset of T in every matroid.

From the claim, we can see that  $|I_i \cap T| = r_i(T), i = 1, ..., k$ . This implies that  $(I+s) \cap T = ((I_1 \cup ... \cup I_k) + s) \cap T = (I_1 \cap T) \cup (I_2 \cap T) \cup ... \cup \{s\}$ , and therefore,  $|(I+s) \cap T| > r_1(T) + r_2(T) + \cdots + r_k(T) \ge r_{M_1 \vee M_2 \vee ... \vee M_k}(T)$ , and I+s is not independent. To prove the claim, we proceed as follows. We know that  $I_i \cap T$  is an independent set in  $\mathcal{I}_i$ . Suppose that this set is not maximal, then there exists an element  $y \in T \setminus I_i$  that can be added to the set with independence still maintained. We know that  $y \notin F$  because T and F are disjoint, so  $I_i + y \notin \mathcal{I}_i$ , which implies that there exists an x such that  $x \in I_i \setminus (I_i \cap T)$  and that we can remove x and add y to have  $I_i - x + y \in \mathcal{I}_i$ . But by definition of  $D_i$ , this means that there is an arc from x to y, which means that x can reach x and is therefore in x, a contradiction. A simpler way to show the existence of x is as follows. Take  $x \in I_i \cap T + y$ , which is independent, and note that  $x \in I_i \cap T + y$  is not independent. We can keep adding elements from  $x \in I_i \cap T + y$  until there's one element left in  $x \in I_i$ , this element is  $x \in I_i$ .

( $\uparrow$ ) Take a shortest F-s path P, with  $P=\{s_0,s_1,...,s_p=s\}$ , and assume  $s_0\in F_1$  (i.e.  $I_1\cup s_0\in \mathcal{I}_1$ .) Since P is a shortest path, the set of edges  $(s_i,s_{i+1})$  with i=0,...,p-1, and  $s_i\in I_j$  gives a unique perfect matching in  $D_{M_j}(I_j)$ . Let  $S_j$  be the endpoints of these edges. As a consequence of lemma 5 in lecture 11, this implies that  $I_j\triangle S_j\in \mathcal{I}_j$ , for all j (the fact that we take a shortest path means that the matching is unique). Also, as in lecture 11, we can also argue that  $(I_1\triangle S_1)\cup \{s_0\}\in \mathcal{I}_1$ . This implies that  $I\cup \{s\}\in \mathcal{I}$ .

So we can test membership if we have an independent set of the union expressed in terms of the independent sets of the matroids.

## 2 Some applications based on matroid union

For the remainder of this lecture, we will give various results related to matroid union, as well as some basic properties of the rank function. In the following,  $M=(S,\mathcal{I})$  is a matroid with rank function r; and  $k \in \mathbb{Z}_+$  is a positive integer.

Corollary 3 The maximum size of the union of k independent sets in M is

$$C = \min_{U \subseteq S} \quad [|S \setminus U| + k \cdot r(U)]$$

Since S can be covered by k bases iff C = |S|, we derive:

Corollary 4 (Matroid base covering) S can be covered by k bases iff  $\forall U : k \cdot r(U) \geq |U|$ .

Since there exist k disjoint bases iff C = kr(S), we get:

Corollary 5 (Matroid base packing) There exist k disjoint bases in M iff

$$\forall U : |S \setminus U| \ge k(r(S) - r(U))$$

Thinking about these corollaries in terms of graphic matroids, we get

**Theorem 6 (Nash-Williams)** G can be covered by k forests iff  $\forall T \subseteq V : |E(T)| \leq k(|T|-1)$ .

**Proof:** The only if direction is obvious. To see the other direction, consider any set  $U \subseteq E$ . Assume (V, U) has l connected components. Let  $T_1, T_2, \dots, T_l$  be these l connected components. By assumption, we have that  $|E(T_i)| \leq k(|T_i| - 1)$ . Summing over i, we get that

$$|U| \le \sum_{i} |E(T_i)| \sum_{i} k(|T_i| - 1) = kr(U),$$

and thus the claim follows from Corollary 4.

Similarly, we derive:

**Theorem 7 (Tutte, Nash-Williams)** G contains k edge-disjoint spanning trees iff  $\forall$  partitions  $\rho$  of V, with  $\rho = (V_1, ..., V_l)$ , we have  $|\delta(\rho)| \ge (l-1)k$ , where  $|\delta(\rho)| = \{(u, v) : u \in V_i, v \in V_j, i \ne j\}$ .

We now turn our attention to some of the properties of the rank function. For a matroid  $M = (S, \mathcal{I})$  with rank function  $r: 2^S \to \mathbb{R}$ , we have the following lemma

**Lemma 8** The rank function is submodular:  $\forall A \text{ and } B \subseteq S, \ r(A) + r(B) \ge r(A \cap B) + r(A \cup B).$ 

**Proof:** Let  $I \subseteq A \cap B$  be an inclusion-wise maximal set in  $\mathcal{I}$ , so  $r(A \cap B) = |I|$ , and let J be such that  $I \subseteq J \subseteq A \cup B$  and  $r(A \cup B) = |J|$ . Note that both  $J \cap A$  and  $J \cap B \in \mathcal{I}$  and therefore we have:

$$r(A) > |J \cap A|$$

$$r(B) \ge |J \cap B|$$

and 
$$r(A) + r(B) \ge |J \cap A| + |J \cap B| = |J \cap (A \cup B)| + |J \cap (A \cap B)| = |J| + |I| = r(A \cap B) + r(A \cup B)$$

In fact, the converse also applies, in the sense that if  $r: 2^S \to \mathbb{Z}_+$  is such that

i) 
$$r(A) \leq r(B)$$
 if  $A \subseteq B$ ,

ii) 
$$r(A) + r(B) \ge r(A \cap B) + r(A \cup B)$$
 for all  $A, B,$ 

iii) 
$$r(A) \leq |A|$$
.

Then  $(S, \{I : |I| = r(I)\})$  is a matroid.

As a consequence of submodularity, note that if we have a matroid polytope defined by

$$x(U) \le r(U)$$
  $\forall U \subseteq S$   
 $x_s > 0$   $\forall s \in S$ 

or a matroid intersection polytope defined by

$$x(U) \le r_1(U)$$
  $\forall U \subseteq S$   
 $x(U) \le r_2(U)$   $\forall U \subseteq S$   
 $x_s \ge 0$   $\forall s \in S$ .

Then we can solve the separation problem over these polytopes by solving

$$\min_{U \subseteq S} [r(U) - x(U)].$$

Where  $x(U) \leq r(U) \ \forall U$ , i.e. we can solve the separation problem by minimizing a submodular function. Cunningham gives a pseudo-polynomial time algorithm to do this. This was later improved to strongly polynomial time by Schrijver and by Fleischer, Fujishige and Iwata. Schrijver's algorithm will be covered in a few lectures. Submodular function minimization has many interesting applications.

We finish this lecture by returning to matroid unions and proving an interesting lemma about the exchange property for matroid bases (remember that we can switch elements and maintain bases).

**Lemma 9** If  $B_1$  and  $B_2$  are bases of M, and  $B_1$  is partitioned into  $X_1 \cup Y_1$ , then there exists a partition of  $B_2$  into  $X_2 \cup Y_2$  such that  $X_1 \cup Y_2$  and  $X_2 \cup Y_1$  are bases of M.

**Proof:** Let's define two matroids,  $M_1 = M/Y_1$  and  $M_2 = M/X_1$ . We want to show that  $B_2 \in \mathcal{I}_1 \vee \mathcal{I}_2$ . This would mean that  $B_2$  can be expressed as  $X_2 \cup Y_2$  with  $X_2 \in \mathcal{I}_1$  and  $Y_2 \in \mathcal{Y}_2$ , i.e.  $X_2 \cup Y_1$  and  $X_1 \cup Y_2$  are bases of M. We have from matroid union

$$\begin{array}{lcl} r_{M_1 \vee M_2}(B_2) & = & \min_{U \subseteq B_2} |B_2 \setminus U| + r_{M_1}(U \cap (S \setminus Y_1)) + r_{M_2}(U \cap (S \setminus X_1)) \\ \\ & = & \min_{U \subseteq B_2} |B_2 \setminus U| + r(U \cup Y_1) - r(Y_1) + r(U \cup X_1) - r(X_1) \\ \\ & \geq & |B_2 \setminus U| + r(U \cup Y_1 \cup X_1) + r(U) - |X_1| - |Y_1| \\ \\ & = & |B_2| - |U| + |U| = |B_2| \end{array}$$

Where the inequality in the second to last equation follows from submodularity. Note that in this equation, the second term cancels with the two last terms, and r(U) = |U| (as U is a subset of a basis) leading to the result.

We conclude our discussion by giving the following open problem. Suppose S can be partitioned into k bases. Is there a way to express S as  $S = \{e_0, e_1, ..., e_{p-1}\}$  where  $p = k \cdot r(S)$  such that for all i,  $\{e_{i+1}, ..., e_{i+r(S)}\}$  (where the indices are taken modulo p) is a base?

---

### 18.997 Topics in Combinatorial Optimization

April 6th, 2004

# Lecture 15

Lecturer: Michel X. Goemans Scribe: Supratim Deb

# 1 Matroid Matching

The Matroid matching Problem: Given a matroid  $M = (S, \mathcal{I})$ , let E be a set of pairs on S. The matroid matching problem is to find disjoint set of pairs  $F \subseteq E$ , such that  $\bigcup F \in \mathcal{I}$  and |F| is maximum. The maximum cardinality of the matching F is denoted by  $\nu(M)$ .

The following are a few illustrations of the matroid matching problem.

Examples (Matroid matching):

- 1. Let M be the trivial matroid on a set S, i.e.,  $M = (S, 2^S)$ . Let E be a collection of pairs on S which define a graph G = (S, E). Then the matroid matching problem is equivalent to finding a maximum size matching in G = (S, E).
- 2. Let  $M_1 = (S, \mathcal{I}_1)$  and  $M_2 = (S, \mathcal{I}_2)$  be two matroids on the ground set S. Then the matroid intersection problem can be formulated using the matroid matching problem in the following manner. Let S' be an identical copy of S where for every  $a \in S$  there is a corresponding  $a' \in S'$ . Define  $M_1$  on S and  $M_2$  on S', so that  $\mathcal{I}_1$  is defined on S and  $\mathcal{I}_2$  is defined on S'. Define M and E as follows.

$$M = (S \cup S', \{I_1 \cup I_2 : I_1 \in \mathcal{I}_1, I_2 \in \mathcal{I}_2\})$$
  
$$E = \{(a, a') : a \in S, a' \in S'\}$$

With the above definition, the matroid matching problem for M is equivalent to finding a maximum independent set in  $M_1 \cap M_2$ .

- 3. Consider the graphic matroid M(G) of a graph G = (V, E). Partition the edge set E into pairs. Then the matroid matching problem is to find the maximum forest consisting of the pairs in the partition of the edge set E.
- 4. Finding a maximum forest in a 3-uniform hypergraph. Consider the problem of finding a maximum forest in a 3-uniform hypergraph. In other words, the problem is to find a maximum subgraph without cycles. Recall that a cycle in a hypergraph is a sequence of hyperedges  $h_1, h_2 ... h_T$  such that,  $\exists \{s_i : i = 1, 2... T\}$ , and  $s_i s_{i+1} \in h_i$  for i = 1, 2... T (with  $s_{T+1} = s_1$ ). The problem can be formulated as a matroid matching problem by creating a graph G and having two edges (a, b) and (b, c) for each hyperedge  $\{a, b, c\}$ , creating a pair for these 2 edges, and considering the cycle matroid of G. choosing any two pairs in each of the hyperedges to construct the set of pairs.

#### 1.1 Is the matroid matching problem solvable in polynomial time?

We will first construct an example to show that the matroid matching problem is not solvable in polynomial time.

We show this by using an independent set testing oracle, which can check whether a given  $T \in \mathcal{I}$  is independent. Let  $M = (S, \mathcal{I})$  be a matroid, and let E be partition of S into pairs. Let the collection of independent sets be as follows.

$$\mathcal{I} = \{I : |I| \le 2k - 1\} \cup \{I : |I| = 2k, I \text{ is not a union of } k \text{ pairs in } E\}.$$

It is easy to check that M, with  $\mathcal{I}$  defined as above, is a matroid. To see this, let  $I_1, I_2 \in \mathcal{I}$  and  $|I_2| < |I_1|$ . If  $I_1 \le 2k - 1$ , then  $I_2$  can be trivially augmented using elements from  $I_2 \setminus I_1$ . If  $I_1 = 2k$ , then  $I_1$  intersects at least k + 1 pairs in E, and thus,  $I_2$  can again be augmented without creating exactly k pairs. Note that  $\nu(M) = k - 1$ . Now take any  $F \subseteq E$  such that |F| = k. Define  $M_F$  as

$$M_F = (S, \mathcal{I} \cup \{ \bigcup F \})$$

which, by the same reasoning, is a matroid for every choice of F. Clearly,  $\nu(M_F) = k$ . If it is known that the matroid is M or any of the  $M_F$ 's, The number of oracle calls required to check if there is a matching of size k is at least  $\binom{|E|}{k}$  since all the possible k-subsets from E have to checked.

The following construction also shows that the matroid matching need not be polynomial time solvable even when the matroid is given more explicitly. Suppose we are given a graph G whose vertex set is E. Let  $M = (S, \mathcal{I})$  be a matroid with  $\mathcal{I}$  defined as as

$$\mathcal{I} = \{I : |I| \le 2k - 1\} \cup \{I : |I| = 2k, I \text{ is not a union of } k \text{ pairs in } E\}$$
$$\cup \{I : |I| = 2k, I \text{ is a union of } k \text{ pairs in } E \text{ such that the pairs form a clique in } G\}$$

Now clearly,

$$\nu(M) = \begin{cases} k-1 & \text{if there is no clique of size } k \\ k & \text{o.w.} \end{cases}$$

Thus, checking whether  $\nu(M) = k$  is not possible in polynomial time unless P = NP.

## 1.2 Min-max relation for matroid matching

Lovász derived a min-max relationship for matroid matching for special class of matroids, namely linear matroids. He also gave a polynomial time algorithm for the problem. For example, the maximum forest problem in a 3-uniform hypergraph can be solved in polynomial time using Lovász' algorithm.

We next extend the definition of matroid for which one can apply Lovász' min-max theorem on matroid matching. The notion of infinite matroid is a generalization of linear spaces.

**Definition 1 (Infinite matroid)** The matroid  $M = (S, \mathcal{I})$  is an infinite matroid if the following properties hold:

- 1.  $I \in \mathcal{I}, \ J \subseteq I \Rightarrow J \in \mathcal{I},$
- 2.  $J \in \mathcal{I} \ \forall (J \subseteq I, |J| < \infty) \Rightarrow I \in \mathcal{I}$
- 3. If  $I, J \in \mathcal{I}$  and  $|I| < |J| < \infty$ , then  $\exists i \in J \setminus I$  such that  $I + i \in \mathcal{I}$ .

Note that the second property is essential to a matroid being an infinite matroid.

Before we state the min-max theorem, recall that a flat in a matroid  $M = (S, \mathcal{I})$  is defined as all  $F \subseteq S$  such that  $F = \operatorname{span}(F)$ . For linear matroids, flats are precisely the linear subspaces.

**Theorem 1 (Lovász)** Let  $M = (S, \mathcal{I})$  be a linear matroid (finite or infinite), let r be the rank function, and let E be a finite set of pairs in S. Then

$$\nu(M) = \min_{F} \left[ r(F) + \sum_{i=1}^{k} \lfloor \frac{1}{2} (r(F_i) - r(F)) \rfloor \right] , \qquad (1)$$

where the minimization is carried over the set

 $\{F: F \subseteq F_1 \cap F_2 \dots \cap F_k; F_1, F_2, \dots F_k \text{ are flats}; \forall (e \in E) \exists (F_i) \text{ such that } e \in F_i\}.$ 

One can check that our examples in Section 1.1 are not linear. We next discuss a few examples where Theorem 1 can be applied.

**Examples** (Application of Theorem 1):

1. Berge-Tutte formula: Let  $M = (S, 2^S)$  be the trivial matroid (in which all sets are independent) and let the edges in the graph G = (S, E) define the set of pairs E in S. Clearly,

$$\nu(M) = \text{maximum size matching in } G$$
.

Now we proceed to compute the RHS of (1). In this case

RHS of (1) = 
$$\min_{F} \left[ |F| + \sum_{i=1}^{k} \lfloor \frac{1}{2} (|F_i| - |F|) \rfloor \right].$$
 (2)

(For the trivial matroid, all sets are flats.) First, note that the minimization can be restricted to the all flats  $F_i$ 's such that the sets  $F_i \setminus F$  are disjoint. To see this, observe that, if for some i and j,  $(F_i \cap F_j) \setminus F \neq \emptyset$ , then, we can replace  $F_i$  and  $F_j$  by a single flat  $F_i \cup F_j$  and that will reduce the sum in (2). Thus, we assume the minimization in (2) is carried over flats such that  $F_i \setminus F$  are disjoint. Thus it means that  $F_i \setminus F_j \setminus F_j \setminus F_j \setminus F_j \setminus F_j$  is a partition of S. Moreover, all edges of G must belong to  $E(F_i)$  for some i. If all the quantities  $|F_i| - |F|$  were even, then (2) boils down to minimization over (1/2)(|F| + |S|). Taking into account the fact that some of the  $|F_i| - |F|$  can be odd, we can write (2) as

$$\frac{1}{2} \min_{F} [|F| + |S| - |\{i : |F_i \setminus F| \text{ odd}\}|],$$

which is precisely the Berge-Tutte formula since  $(F_i \setminus F)$  can be seen to be a connected component of  $G \setminus F$ .

2. **Graphic matroid:** Let G = (V, E) be a graph and P be a partition of the edges into pairs. The matroid matching problem is to find the maximum size forest that only contains pairs in the partition P. We will derive the min-max relation given by Theorem 1 in this special case. We first see what the flats correspond to in this case. Let Q be a partition of V into classes. The flats are all edges contained within the classes of Q. Thus for a flat F, if Q is the corresponding partition, then

$$r(F) = |V| - |Q|.$$

Now we can form super-flats by merging some of the classes in Q to form larger classes. Now partition E into classes  $E_1, E_2 \dots E_k$  such that each  $E_i$  only consists of pairs in P in the statement of the problem. Thus, in this case, the maximum size of a forest only consisting of pairs in P (which is  $2 \times RHS$  of (1) in Theorem 1) equals

$$\min_{Q,E_1,\dots,E_k} 2 \left[ |V| - |Q| + 2 \sum_{i=1}^k \lfloor \frac{1}{2} \delta_Q(E_i) \rfloor \right] ,$$

where  $\delta_Q(E_i)$  is the size of the largest forest in the graph  $(V, E_i)$  after shrinking the classes of Q.

### Comments of the linearity condition in Theorem 1:

The min-max relationship given by (1) in Theorem 1 holds under a more general condition. Let  $M = (S, \mathcal{I})$  be a matroid and let  $\mathcal{C}$  be the set of all the circuits. Then Theorem 1 holds if M and all

its contractions satisfy the relationship that

$$r\left(\bigcap_{C \in C'} \operatorname{span}(C)\right) > 0,\tag{3}$$

where

$$C' = \{ \text{circuit } C : C \subseteq C_1 \cup C_2, r(C) = |C_1 \cup C_2| - 2 \},$$

for any two circuits  $C_1$ ,  $C_2$  with  $C_1 \cap C_2 \neq \emptyset$ .

We next show that linear matroid satisfy the condition given by (3).

**Proposition 2** If  $M = (S, \mathcal{I})$  is a linear matroid, then it satisfies the condition given by (3).

**Proof:** Note that  $C_1 \setminus C_2 \in \mathcal{I}$  and  $C_1 \cap C_2 \in \mathcal{I}$ . Since span $(C_1 \setminus C_2)$ , span $(C_1 \cap C_2)$ , and span $(C_1)$  are linear subspaces, and further since,

$$r(C_1 \setminus C_2) + r(C_1 \cap C_2) = |C_1 \setminus C_2| + |C_1 \cap C_2| = |C_1| > r(C_1)$$

it follows that

$$P = \operatorname{span}(C_1 \setminus C_2) \cap \operatorname{span}(C_1 \cap C_2) \neq \emptyset.$$

Thus,  $\exists p \neq 0 \in P$ . We next argue that  $p \in \text{span}(C)$  for every  $C \subseteq C_1 \cup C_2$  with  $r(C) = |C_1 \cup C_2| - 2$ . Suppose not, i.e.,  $p \notin \text{span}(C)$ . Now,

$$p \in \operatorname{span}(C_1 \setminus C_2) \Rightarrow C_1 \setminus C_2 \not\subseteq C \Rightarrow \exists s \in C_1 \setminus C_2, \ s \notin C$$
.

and similarly

$$p \in \operatorname{span}(C_1 \cap C_2) \Rightarrow \exists t \in C_1 \cap C_2, \ t \notin C$$
.

Now,  $\operatorname{span}(C_2) = \operatorname{span}(C_2 - t)$  (this is always true for an element of a circuit) implies

$$t \in \operatorname{span}(C_2 - t) \subseteq \operatorname{span}(C_1 \cup C_2 \setminus \{s, t\})$$
,

as  $C_2 \setminus \{t\} \subseteq (C_1 \cup C_2) \setminus \{s,t\}$ . Therefore

$$s \in \operatorname{span}(C_1 - s) \subseteq \operatorname{span}((C_1 \cup C_2) \setminus \{s\}) = \operatorname{span}((C_1 \cup C_2) \setminus \{s, t\}),$$

as  $t \in \text{span}((C_1 \cup C_2) \setminus \{s, t\})$ . Thus

$$\{s,t\} \subseteq \operatorname{span}(C_1 \cup C_2 \setminus \{s,t\})$$
.

Since |C| > r(C) (as C is a circuit),  $r(C) = |C_1 \cup C_2| - 2$  (by assumption) and  $C \subseteq (C_1 \cup C_2) \setminus \{s, t\}$ , we obtain

$$|C| > r(C) = |C_1 \cup C_2| - 2 = |(C_1 \cup C_2) \setminus \{s, t\}| \ge |C|$$

and we have reached a contradiction.

---

### 18.997 Topics in Combinatorial Optimization

April 8, 2004

### Lecture 16

Lecturer: Michel X. Goemans Scribe: Jonathan Kelner

This lecture is about jump systems. While they are briefly discussed in chapter 41 of Schrijver's book, they are not covered extensively. A good reference for this material is a set of notes by Jim Geelen, available at http://www.math.uwaterloo.ca/~jfgeelen/publications/js.ps.

# 1 The Basics of Jump Systems

We begin with some notational definitions that will simplify the rest of our discussion.

**Definition 1.** For  $x, y \in \mathbb{Z}^n$ , we let the box [x, y] be the set

$$\{z \in \mathbb{Z}^n | \min(x_i, y_i) \le z_i \le \max(x_i, y_i) \forall i \in \{1, \dots, n\} \}.$$

In that which follows, we shall use the  $L_1$  metric unless otherwise stated. That is, for  $x, y \in \mathbb{Z}^n$ , we shall have

$$d(x,y) = ||x - y||_1 = \sum_{i=1}^{n} |x_i - y_i|.$$

**Definition 2.** For  $x, y \in \mathbb{Z}^n$ , a step x' from x to y is a point  $x' \in \mathbb{Z}^n$  such that  $x' \in [x, y]$  and d(x, x') = 1.

We can now define our main objects of study:

**Definition 3.** A jump system is a set  $J \subseteq \mathbb{Z}^n$  such that if x' is a step from x to y, then either

- 1.  $x' \in J$ , or
- 2. There exists a step x'' from x' to y such that  $x'' \in J$ .

We now consider some examples of jump systems.

Example 1. Let M be a matroid over a set S, |S| = n. We let each coordinate of  $\mathbb{Z}^n$  correspond to an element of S, and let  $J \subseteq \{0,1\}^n$  be the set of characteristic functions for bases of M,

$$J = \{\chi^B | B \text{ a basis of } M\}.$$

Claim 1. The set J is a jump system.

*Proof.* Let x and y be the respective characteristic vectors of two bases  $b_1$  and  $b_2$  of M. A step x' from x to y corresponds to either:

- 1. Adding to  $b_1$  an element of  $b_2 \setminus b_1$ , or
- 2. Removing from  $b_1$  some element of  $b_1 \setminus b_2$ .

Since all bases have the same size, the set corresponding to x' will never be a basis, so  $x' \notin J$ . We thus require there to be some step x'' from x' to y such that  $x'' \in J$ , i.e., such that the set corresponding to x'' is a basis. In both cases, this is guaranteed by Basis Exchange (see lecture 11).

Example 2. Let G = (V, E) be an undirected graph, and let n = |V|. For every subgraph H = (V, F) of G, we can construct its degree sequence  $d_H \in \mathbb{Z}^n$  by setting the  $i^{\text{th}}$  coordinate of  $d_H$  equal to the degree in H of the  $i^{\text{th}}$  vertex of G. Now let

$$J = \{d_H | H \text{ is a subgraph of } G\}$$

be the set of all degree sequences of subgraphs of G.

Claim 2. J is a jump system.

We could check this directly, but it would be rather tedious. Instead, we shall describe several operations that one can perform on jump systems that give rise to other jump systems. We will then show how to construct J using these operations, from which Claim 2 will follow.

# 2 Operations on Jump Systems

In this section, we describe several operations on jump systems. Throughout the sequel, let  $J \subseteq \mathbb{Z}^n$  be a jump system.

**Translation** If J is a jump system, J + a is a jump system for any vector  $a \in \mathbb{Z}^n$ .

**Reflection** For some  $i \in \{1, ..., n\}$  reflect the entire jump system through the  $x_i = 0$  plane, replacing each point  $(x_1, ..., x_n) \in J$  with  $(x_1, ..., -x_i, ..., x_n)$ . This clearly produces another jump system.

**Projection** Project onto some axis-parallel subspace of  $\mathbb{Z}^n$ . That is, let  $S \subseteq \{1, \ldots, n\}$  be some subset of the coordinates, and create a new set  $J_S = \{x|_S, x \in J\}$ . To see that  $J_S$  is a jump system, note that the projection of a step either gives a step or no motion at all.

**Sum** If  $J_1$  and  $J_2$  are jump systems, define a new set  $J_1 + J_2 := \{x + y | x \in J_1, y \in J_2\}.$ 

Claim 3.  $J_1 + J_2$  is a jump system.

*Proof.* Let  $x_1, y_1 \in J_1$ ,  $x_2, y_2 \in J_2$ ,  $x = x_1 + x_2$ ,  $y = y_1 + y_2$ , and suppose that x' is a step from x to y. We shall show that either  $x' \in J_1 + J_2$  or that there exists a step  $x'' \in J$  from x' to y.

Take  $z_1 \in J_1$ ,  $z_2 \in J_2$  such that  $d(x', z_1 + z_2) = 1$  and so that  $d(z_1, y_1) + d(z_2, y_2)$  is minimized. This is always possible, since  $d(x', x_1 + x_2) = 1$ . We now have two possibilities:

Case 1:  $z_1 + z_2 \in [x', y]$ .

In this case, we are already done, since  $z_1 + z_2 \in J$ , and  $z_1 + z_2$  is a step from x' to y.

Case 2:  $x' \in [z_1 + z_2, y]$ .

Let  $x' = z_1 + z_2 + s$ , so that  $z_1 + z_2 + s \in [z_1 + z_2, y_1 + y_2]$ . This implies that either  $z_1 + s \in [z_1, y_1]$  or  $z_2 + s \in [z_2, y_2]$ . By symmetry, we may assume without loss of generality that  $z_1 + s \in [z_1, y_1]$ . We now have two possibilities:

- 1.  $z_1 + s \in J_1$ , or
- 2.  $z_1 + s \notin J_1$ .

In the first case, we are done, since  $x'=(z_1+s)+z_2\in J_1+J_2$ , as required. In the second case, the fact that  $J_1$  is a jump system implies that there exists a step  $z_1'\in J_1$  from  $z_1+s$  to y. It thus follows easily that  $d(z_1'+y_1)+d(z_2,y_2)< d(z_1,y_1)+d(z_2,y_2)$ . However, since  $d(z_1'+z_2,x')=1$ , and since  $z_1+z_2$  was chosen from points satisfying this condition so as to minimize  $d(z_1,y_1)+d(z_2,y_2)$ , we must have  $d(z_1',y_1)+d(z_2,y_2)\geq d(z_1,y_1)+d(z_2,y_2)$ , thereby resulting in a contradiction.

We can now prove Claim 2 and show that the set described in Example 2 is in fact a jump system.

Proof of Claim 2. If G is a single edge connecting two vertices i and j, the degree sequences are just  $\{0, e_i + e_j\}$ , which is obviously a jump system. If G is a more complicated graph, its set of degree sequences is just the sum of the jump systems for each of its edges, which is a jump sequence by Claim 3.

# 3 Optimizing Over a Jump System

Suppose we have some vector  $(w_i)$ ,  $i=1,\ldots,n$ . In this section, we shall show how to maximize  $w^Tx$  for  $x \in J$ . By reflecting and reordering the coordinates if necessary, we may assume  $w_1 \geq w_2 \geq \cdots \geq w_n \geq 0$ . We shall find the optimum with the following greedy algorithm:

 $J_0 = J$ 

For i=1 to n

 $\mathtt{J_i} \leftarrow \arg\max_{\mathtt{x} \in \mathtt{J_{i-1}}} \mathtt{x_i}$ 

Return J<sub>n</sub>,

where the argmax returns the set of all values achieving the maximum.

Claim 4. This algorithm returns the desired maximum.

*Proof.* Suppose to the contrary. By induction on i, we can assume that the maximum taken over J is not equal to that taken over  $J_1$ . Call the vector that achieves the former quantity x, and call the vector that achieves the latter y. Our assumption implies that  $x_1 < y_1$ .

We have also assumed that  $w^T x > w^T y$ . Now, either

- 1.  $x + e_1 \in J$ , or
- 2.  $x + e_1 \pm e_k \in J$ .

Take x out of the optimal solutions to be the one that minimizes  $y_1 - x_1$ . In the first case, we have

$$w^{T}(x + e_1) = w^{T}x + w_1 \ge w^{T}x,$$

which yields a contradiction. In the second case, we have

$$w^{T}(x + e_1 \pm e_k) = w^{T}x + w_1 \pm w_k > w^{T}x$$

which again yields a contradiction. This completes the proof.

Observe that since we first computed the absolute values of the  $w_i$ 's, the greedy algorithm described here does not correspond to the classical greedy algorithm to compute a maximum weight basis of a matroid.

# 4 Membership in Jump Systems

The material in this section is almost exclusively due to Lovász. A paper covering this and much more is available at http://research.microsoft.com/users/lovasz/jump.ps.

Suppose we are given a jump system J in some sort of implicit form. In this section, we take up the question of when we can determine whether some point x is in J. This specializes to many standard problems that we have already considered in this class.

Example 3. Let G be a graph, and let  $J_G$  be its set of degree sequences. Asking whether the vector  $(1, \ldots, 1) \in J_G$  is equivalent to asking whether there is some subgraph of G in which every vertex of G has degree exactly one. This is exactly the question of whether G admits a perfect matching.

This can be generalized to the "factor problem": Given a graph G = (V, E) and a function  $f: V \to \mathbb{Z}_{\geq 0}$ , does there exist a subgraph  $F \subseteq E$  such that  $d_f(v) = f(v)$  for all v? (It turns out that, using classical methods, one can reduce this problem to solving perfect matching, so this doesn't really gain us too much generality.)

Example 4. Let  $M_1$  and  $M_2$  be matroids, and let  $J_1$  and  $J_2$  be their respective jump systems of bases, as described in Example 1. Now let  $J = J_1 - J_2$ . The question of whether 0 belongs to J is equivalent to asking whether  $M_1$  and  $M_2$  have a common basis.

So it would be great if we could get a good general solution to the membership problem for jump systems. Unfortunately, this is going to turn out to be too much to ask for. As the next example will show, the membership problem includes matroid matching, which we established in an earlier lecture to be NP-hard.

Example 5. Let  $M=(S,\mathcal{I})$  be a matroid, let E be a set of pairs of elements of S, let  $J_M$  be the jump system of bases of M (as in Example 1), and let  $J_G$  be the jump system of degree sequences of G=(S,E) (as in Example 2). Now, let  $J=J_M-J_G$ . Every vector in  $J_M$  is a  $\{0,1\}$ -vector of weight equal to the rank of M. Such a vector, when interpreted as an element of  $J_G$ , corresponds to a matching of weight  $\operatorname{rk}(M)$ . It thus follows that  $0 \in J$  if and only if there is a matching in G of weight  $\operatorname{rk}(M)$  that is independent in M. Checking if  $0 \in J$  is thus precisely equivalent to matroid matching, which, alas, is NP-hard.

We therefore can't hope to solve the membership problem in general. However, Lovász described a broad class of cases where we can solve it, which we will discuss here and in the next lecture.

#### 4.1 The Beginnings of a Min-Max Relation

It will be useful to generalize a little bit and consider the question of finding the closest element of a jump system to some box. Let J be a jump system, and let  $B = [a, b], a, b \in \mathbb{Z}^n$ , be a box. Now consider the quantity

$$d(J,B) = \min_{x \in J, y \in B} d(x,y) = \min_{x \in J, y \in B} \sum_{i} |x_i - y_i|.$$

If  $w \in \{0, +1, -1\}^n$ , then clearly

$$d(J,B) \ge \min_{x \in J, y \in B} w^{T}(x-y) = \min_{x \in J} w^{T}x - \max_{y \in B} w^{T}y.$$
 (1)

In some classes of systems, we will have equality in Equation (1), which will facilitate a solution to the membership problem. To state when this occurs, we will need some terminology. First, given a box B, let

$$J_B = \{ x \in J | d(x, B) = d(J, B) \}.$$

Theorem 1 (Lovász).  $J_B$  is a jump system.

Now, we will define two sets,  $V_B^+$  and  $V_B^-$ :

$$V_B^+ = \{ i \in \{1, \dots, n\} \mid \exists x \in J_B \text{ s.t. } x_i > b_i \},$$

$$V_B^- = \{ i \in \{1, \dots, n\} \mid \exists x \in J_B \text{ s.t. } x_i < a_i \}.$$

The main theorem, which we shall show in the next lecture, is:

**Theorem 2.** If  $V_B^+ \cap V_B^- = \emptyset$ , then we have equality in Equation (1).

---

| 18.997 Topics in Combinatorial Optimization | April 15th, 2004    |
|---------------------------------------------|---------------------|
| Lecture 18                                  |                     |
| Lecturer: Michel X. Goemans                 | Scribe: Nick Harvey |

## 18 Orientations, Directed Cuts and Submodular Flows

In this lecture, we will introduce three related topics: graph orientations, directed cuts, and sub-modular flows. In fact, we will use submodular flows to prove results from the other topics.

## 18.1 Graph Orientations

We first introduce some notation and definitions. Let G = (V, E) be an undirected graph. Recall that for a non-empty subset  $U \subset V$ , the notation  $\delta_G(U)$  denotes the set of edges with one endpoint in U and the other endpoint in  $V \setminus U$ .

**Definition 1** Let  $\lambda_G(u,v)$  denote the maximum number of edge-disjoint u-v paths in G. We say that G is **k-edge-connected** if  $\lambda_G(u,v) \geq k$  for all  $u,v \in V$ . An equivalent statement is that each cut contains at least k edges, i.e.,  $|\delta_G(U)| \geq k$  for all non-empty  $U \subset V$ .

Let D = (V, A) be a directed graph. For a non-empty subset  $U \subset V$ ,  $\delta_D^{\text{out}}(U)$  is the set of arcs with their tail in U and head in  $V \setminus U$ , and  $\delta_D^{\text{in}}(U)$  is the set of arcs in the reverse direction.

**Definition 2** Let  $\lambda_D(u,v)$  denote the maximum number of edge-disjoint directed paths in D from u to v. We say that D is **k-arc-connected** if  $\lambda_D(u,v) \geq k$  for each  $u,v \in V$ . An equivalent statement is that  $|\delta_D^{\text{out}}(U)| \geq k$  for all non-empty  $U \subset V$ . A digraph that is 1-arc-connected is also called strongly connected.

An **orientation** of a graph G is a digraph obtained by choosing a direction for each edge of G. We now give some results relating edge-connectivity of G to arc-connectivity of orientations of G.

**Theorem 3 (Robbins, 1939)** G is 2-edge-connected  $\iff$  there exists an orientation D of G that is strongly connected.

**Proof:**  $\Leftarrow$ : Fix a strongly-connected orientation D. For any non-empty  $U \subset V$ , we may choose  $u \in U$  and  $v \in V \setminus U$ . Since D is strongly connected, there is a directed u-v path and a directed v-u path. Thus  $|\delta_D^{\text{out}}(U)| \ge 1$  and  $|\delta_D^{\text{in}}(U)| \ge 1$ , implying  $|\delta_G(U)| \ge 2$ .

 $\Rightarrow$ : Since G is 2-edge-connected, it has an ear decomposition. We proceed by induction on the number of ears. If G is a cycle then we may orient the edges to form a directed cycle D, which is obviously strongly connected. Otherwise, G consists of an ear P and subgraph G' with a strongly connected orientation D'. The ear is an undirected path with endpoints  $x, y \in V(G')$  (possibly x = y). We orient P so that it is a directed path from x to y and add this to D', thereby obtaining an orientation D of G.

To show that D is strongly connected, consider any  $u, v \in V(G)$ . If  $u, v \in V(G')$  then by induction there is a u-v dipath. If  $u \in P$  and  $v \in V(G')$  then there is a u-v dipath and by induction there is a y-v dipath. Concatenating these gives a u-v dipath. The case  $u \in V(G')$  and  $v \in P$  is symmetric. If both  $u, v \in P$  then either a subpath of P is a u-v path, or there exist a u-v path, a v-v-path, and a v-v-path. (The v-v-path exists by induction). Concatenating these three paths gives a v-v-path.

The natural generalization of this theorem also holds.

**Theorem 4 (Nash-Williams, 1960)** G is 2k-edge-connected  $\iff$  there exists an orientation D of G that is k-arc-connected.

Before proving Nash-Williams' theorem, we need a result about how to construct 2k-edge-connected graphs. This theorem 5 is proved in a subsequent lecture.

**Theorem 5** Every 2k-edge-connected graph can be constructed as follows. Start from the multigraph  $G_1$  consisting of two vertices u and v, with 2k parallel edges joining u and v. Repeatedly perform one of the following operations:

- 1. Add a new edge.
- 2. "Pinch" a set S of k edges. This means to add a new vertex z and to replace each edge  $xy \in S$  with the two edges xz and zy.

**Proof of Theorem 4:**  $\Leftarrow$ : Identical to the corresponding direction in the proof of Theorem 3.

 $\Rightarrow$ : By induction on the number of operations used to construct G in Theorem 5. The starting graph  $G_1$  is clearly 2k-edge-connected. Orienting k of the edges from u to v and the other k from v to u gives an orientation that is k-arc-connected.

So suppose that G is 2k-edge-connected and has a k-arc-connected orientation D. If we add an edge to G then this edge may be added to D and oriented arbitrarily without violating k-arc-connectivity. Now suppose we pinch a edge-set S, obtaining a graph G'. The directions of the pinched edges induce directions on the new edges of G' in the natural way. That is, if  $xy \in S$  and xy is oriented from x to y then we orient the new edges xz, zy from x to z and from y to z. If  $xy \notin S$  then xy is oriented as in D. This yields an orientation D' of G'.

To show that D' is k-arc-connected, we can for example show that  $\delta_{D'}^{in}(U) \geq k$  and  $\delta_{D'}^{out}(U) \geq k$  for every  $\emptyset \neq U \subseteq V$ , where V is the vertex set of G; the vertex set of G' being  $V' = V \cup \{z\}$ . This is clear for U = V as we pinched k edges (and we get k incoming to z and k outgoing arcs from z in D'). For  $U \subset V$ , we have that  $\delta_{D'}^{in}(U) \geq \delta_D^{in}(U) \geq k$  and  $\delta_{D'}^{out}(U) \geq \delta_D^{out}(U) \geq k$  as we replaced the arc xy with xz and zy and D is a k-arc-connected orientation.

As mentioned earlier, Theorem 5 will be proved in a susbsequent lecture. We will also give another proof of Nash-Williams orientation theorem based on submodular flows. Nash-Williams also proved the following, much stronger theorem.

**Theorem 6 (Nash-Williams, 1960)** For any graph G, there exists an orientation D such that  $\lambda_D(u,v) \geq |\lambda_G(u,v)/2|$ .

The proof of this theorem is quite involved; see Theorem 61.6 in Schrijver. We now prove it for special case that all vertices of G have even degree.

**Proof:** Since G is Eulerian, there exists an orientation D such that  $d_D^{\text{in}}(v) = d_D^{\text{out}}(v) \ \forall v \in V$ . Thus for any non-empty  $U \subset V$ , the total in-degree of the vertices in U must equal the total out-degree. Any arcs with both endpoints in U contribute 1 to both the total in-degree and out-degree. Thus the number of arcs leaving U must equal the number of arcs entering U. That is,  $|\delta_D^{\text{in}}(U)| = |\delta_D^{\text{out}}(U)| = |\delta_G(U)|/2$ . The theorem follows by observing that  $\lambda_D(u, v)$  and  $\lambda_G(u, v)$  respectively equal the minimum of  $|\delta_D^{\text{out}}(U)|$  and  $|\delta_G(U)|$  over all cuts U separating u and v.  $\square$ 

## 18.2 Directed Cuts

One might expect a directed cut to be a set of edges whose removal destroys strong connectivity of a digraph. Our definition of directed cuts is quite the opposite: it is clear from the following definition that a digraph has a directed cut if and only if it is not strongly connected.

**Definition 7** Let D = (V, A) be a directed graph. A **directed cut** in D is a set of arcs of the form  $\delta_D^{\text{in}}(U)$  where U is a non-empty proper subset of V and  $\delta_D^{\text{out}}(U) = \emptyset$ .

**Definition 8** A dijoin is a minimal set of arcs that intersect every directed cut. A dijoin is also known as a directed cut cover.

**Theorem 9 (Lucchesi-Younger, 1978)** For every weakly-connected digraph, the minimum size of a dijoin equals the maximum number of disjoint directed cuts.

The Lucchesi-Younger theorem is yet another example of a min-max theorem in combinatorial optimization involving objects that "block" each other. A more well-known example is the max-flow min-cut theorem: the minimum size of an *s-t* cut equals the maximum number of disjoint *s-t* paths.

The min-cut max-flow theorem remains true after swapping the terms cut and path: the minimum length of an s-t path equals the maximum number of disjoint s-t cuts. To see that the max does not exceed the min, fix a shortest s-t path P and let d be the length of P. Each s-t cut must contain at least one edge of P, so there can be at most d disjoint cuts. We now give an intuitive argument that in fact d disjoint cuts exist. Imagine the edges of the graph as being strings of one inch in length, tied together at the vertices. Hold the graph at vertex s, letting gravity pull the other vertices downwards. It is easy to see that the vertices at distance i from s (in the graph-theoretic sense) will be suspended i inches below s. The edges connecting the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices at distance i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the vertices i to the

Woodall conjectured that the Lucchesi-Younger theorem remains true after swapping the terms directed cut and dijoin.

Conjecture 10 (Woodall, 1978) For every digraph, the minimum size of a directed cut equals the maximum number of disjoint dijoins.

Woodall's conjecture remains open, although it has been proven in several special cases; see Chapter 56 of Schrijver.

**Proposition 11** Let D = (V, A) be a weakly-connected digraph, let B be a subset of A, and let  $B' = \{ (v, u) : (u, v) \in B \}$ . Then B is a dijoin  $\iff$  the digraph  $D' = (V, A \cup B')$  is strongly connected.

**Proof:**  $\Rightarrow$ : Let U be a non-empty proper subset of V. If  $\delta_D^{\text{in}}(U)$  is not a directed cut then  $\delta_{D'}^{\text{in}}(U)$  is not either since D is a subgraph of D'. So suppose that  $\delta_D^{\text{in}}(U)$  is a directed cut. Then there exists an arc  $(x,y) \in \delta_D^{\text{in}}(U) \cap B$ , since B is a dijoin. The reverse arc (y,x) is an arc of D', by definition of B'. Thus  $\delta_{D'}^{\text{out}}(U) \neq \emptyset$ , implying that  $\delta_{D'}^{\text{in}}(U)$  is not a directed cut. Since D' has no directed cuts, it is strongly connected.

 $\Leftarrow$ : Suppose that B is not a dijoin. Then there exists a directed cut  $\delta_D^{\text{in}}(U)$  with  $\delta_D^{\text{in}}(U) \cap B = \emptyset$ . Then we have  $\delta_D^{\text{out}}(U) = \emptyset$  and for every  $(x,y) \in \delta_D^{\text{in}}(U)$ ,  $(y,x) \notin B'$ . This shows that  $\delta_D^{\text{out}}(U) = \emptyset$ , so  $\delta_{D'}^{\text{in}}(U)$  is a directed cut. We conclude that D' is not strongly connected.

Since checking that a graph is strongly connected can be done in linear time, Proposition 11 implies a polynomial time algorithm to check that a set is a dijoin. It is also easy to check that a collection of sets are disjoint directed cuts, so the Lucchesi-Younger theorem gives a "good characterization" for the problem of finding a minimum size dijoin or a maximum collection of directed cuts. We will see in a later lecture that a minimum size dijoin and a maximum packing of directed cuts can be found in polynomial time, via a reduction to matroid intersection.

If D is a planar digraph, we can construct its planar dual  $D^*$  as follows. Let  $G_D$  be the underlying undirected graph of D, and let  $G_D^*$  be its planar dual. For each arc wx of D, let yz be the corresponding dual edge in  $G_D^*$ . We choose a direction for the edge yz such that it crosses teh arc

**Figure 1:** A digraph D in black and its planar dual  $D^*$  in gray. Note that the arcs  $\{BA, DC, FE\}$  are a directed cut for D, and the corresponding dual arcs  $\{e_4, e_7, e_1\}$  are a directed cycle in  $D^*$ .

wx from left to right. Intuitively, the direction for yz is obtained by rotating the arc wx clockwise. The resulting directed graph is the planar dual  $D^*$ .

As we can see from Figure 1, the dicycles of  $D^*$  correspond to the directed cuts of D. A dijoin B in D is a set that intersects every directed cut, and hence B corresponds to a set F of arcs in  $D^*$  that intersects every dicycle. Such a set F is called a **feedback arc set**. Thus we obtain the following corollary of the Lucchesi-Younger theorem.

Corollary 12 For planar digraphs, the minimum size of a feedback arc set equals the maximum number of disjoint directed cuts.

## 18.3 Submodular Flows

We now introduce submodular flows, and use this framework to prove results about graph orientation and directed cuts.

**Definition 13** Let D = (V, A) be a directed graph and let  $\mathscr{C} \subseteq 2^V$  be a family of subsets of V.  $\mathscr{C}$  is called a **crossing family** if:

$$X,Y \in \mathcal{C}, \ X \cap Y \neq \emptyset, \ X \cup Y \neq V \implies X \cap Y \in \mathcal{C} \ and \ X \cup Y \in \mathcal{C}.$$

**Example 14** The family  $\mathscr{C} = 2^V \setminus \{\emptyset, V\}$  is a crossing family.

**Example 15** Fix  $s, t \in V$ . The family  $\mathscr{C} = \{ S : s \in S, t \notin S \}$  is a crossing family.

**Example 16** . Let  $\mathscr C$  be the family of vertex sets that induce directed cuts in D. More formally, let  $\mathscr C=\set{U:\emptyset\neq U\subset V\text{ and }\delta_D^{\mathrm{out}}(U)=\emptyset}$ . We claim that  $\mathscr C$  is a crossing family.

**Proof:** Suppose that  $X, Y \in \mathcal{C}$ ,  $X \cap Y \neq \emptyset$ , and  $X \cup Y \neq V$ . By definition of  $\mathcal{C}$ ,  $\delta_D^{\text{out}}(X) = \emptyset$ , implying that D contains no arc (x, z) with  $x \in X$  and  $z \in V \setminus X$ . Similarly, D contains no arc (x, z) with  $x \in Y$  and  $z \in V \setminus Y$ .

First we show that  $X \cap Y \in \mathscr{C}$ . By our previous remarks, for any  $x \in X \cap Y$ , if (x, z) is an arc then we cannot have  $z \in V \setminus X$  or  $z \in V \setminus Y$ . That is,  $z \notin (V \setminus X) \cup (V \setminus Y) = V \setminus (X \cap Y)$ . This shows that  $\delta_D^{\text{out}}(X \cap Y) = \emptyset$ , so  $X \cap Y \in \mathscr{C}$ .

Next we show that  $X \cup Y \in \mathscr{C}$ . Suppose z is neither in X nor in Y. If  $x \in X$  then (x, z) cannot be an arc. Similarly, if  $x \in Y$  then (x, z) cannot be an arc. This shows that there is no arc (x, z) with  $x \in X \cup Y$  and  $z \in (V \setminus X) \cap (V \setminus Y) = V \setminus (X \cup Y)$ . Thus  $\delta_D^{\text{out}}(X \cup Y) = \emptyset$ , so  $X \cup Y \in \mathscr{C}$ .  $\square$ 

**Definition 17** *Let*  $\mathscr{C}$  *be a crossing family. A function*  $f : \mathscr{C} \to \mathbb{R}$  *is called* **crossing submodular** *(relative to*  $\mathscr{C}$ *) if it satisfies:* 

$$f(X) + f(Y) \ge f(X \cap Y) + f(X \cup Y)$$
  $\forall X, Y \in \mathscr{C} \text{ with } X \cap Y \ne \emptyset \text{ and } X \cup Y \ne V.$ 

**Definition 18** Let D = (V, A) be a digraph, let  $\mathscr{C}$  be a crossing family, and let f be a crossing submodular function on  $\mathscr{C}$ . We associate with each arc  $a \in A$  a variable  $x_a$  and an interval  $[d_a, c_a]$ . The vector  $x \in \mathbb{R}^A$  is called a **submodular flow** if it is contained in the polyhedron:

$$x(\delta^{\text{in}}(U)) - x(\delta^{\text{out}}(U)) \leq f(U) \qquad \forall U \in \mathscr{C}$$

$$d_a \leq x_a \leq c_a \qquad \forall a \in A$$

$$(1)$$

**Theorem 19 (Edmonds-Giles, 1977)** The polyhedron (1) is Box-TDI. That is, for any vectors  $c, d \in \mathbb{R}^A$  and any crossing submodular function f, all vertices of (1) are integral.

We will prove the Edmonds-Giles theorem in a later lecture. In the remainder of this lecture, we will show some of its applications. First we show that Theorem 4 follows from the Edmond-Giles theorem.

Corollary 20 G is 2k-edge-connected  $\iff$  there exists an orientation of G that is k-arc-connected.

**Proof:** This proof is due to Frank (1980). Choose an orientation D = (V, A) of G arbitrarily. If D is k-arc-connected then there is nothing to prove, so assume otherwise. We will try to find a subset of the arcs such that reversing those arcs' directions yields a k-arc-connected orientation. For each arc  $a \in A$  we define a variable  $x_a$ , where  $x_a = 1$  means that we switch the direction of arc a, and  $x_a = 0$  means that we do not.

Let  $\emptyset \neq U \subset V$  be arbitrary. After switching the arcs, we want at least k arcs inbound to set U. Before switching, we have  $|\delta_D^{\text{in}}(U)|$  such arcs. The number of inbound arcs gained by switching is  $x(\delta_D^{\text{out}}(U)) - x(\delta_D^{\text{in}}(U))$ . Thus we want to have  $|\delta_D^{\text{in}}(U)| - x(\delta_D^{\text{in}}(U)) + x(\delta_D^{\text{out}}(U)) \geq k$ . That is, we want to find an integral vector  $x \in \mathbb{R}^A$  satisfying:

$$x(\delta_D^{\text{in}}(U)) - x(\delta_D^{\text{out}}(U)) \leq |\delta_D^{\text{out}}(U)| - k \qquad \forall \emptyset \neq U \subset V$$

$$0 \leq x_a \leq 1 \qquad \qquad \forall a \in A$$

$$(2)$$

We have shown that  $\mathscr{C} = \{ U : \emptyset \neq U \subset V \} = 2^V \setminus \{\emptyset, V\}$  is a crossing family (Example 14). In order to use the Edmonds-Giles theorem, we need to show that the function  $f(U) = |\delta_D^{\text{out}}(U)| - k$  is crossing submodular. So suppose that  $X, Y \in \mathscr{C}, X \cap Y \neq \emptyset$ , and  $X \cup Y \neq V$ . It is easy to see that

$$|\delta_D^{\text{out}}(X)| + |\delta_D^{\text{out}}(Y)| \ge |\delta_D^{\text{out}}(X \cap Y)| + |\delta_D^{\text{out}}(X \cup Y)|.$$

(To see that the left can be greater than the right, note that arcs connecting  $X \setminus Y$  and  $Y \setminus X$  contribute 1 to the left but 0 to the right.) This implies that  $f(X) + f(Y) \ge f(X \cap Y) + f(X \cup Y)$ , since the k's cancel.

Thus the Edmonds-Giles theorem shows that every vertex of the polyhedron (2) is integral. However, we have yet to show that the polyhedron is non-empty. To show this, set each  $x_a = 1/2$ , so that that  $x(\delta_D^{\rm in}(U)) = |\delta_D^{\rm in}(U)|/2$  and  $x(\delta_D^{\rm out}(U)) = |\delta_D^{\rm out}(U)|/2$ . Then

$$|\delta_D^{\text{in}}(U)| - x(\delta_D^{\text{in}}(U)) + x(\delta_D^{\text{out}}(U)) = |\delta_D^{\text{in}}(U)|/2 + |\delta_D^{\text{out}}(U)|/2 = |\delta_G(U)|/2 \ge k.$$

This shows that all constraints are satisfied, so the polyhedron (2) is non-empty; in particular, it has at least one integral vertex  $x^*$ . Swapping the direction of the edges indicated by the 1-coordinates of  $x^*$  yields a k-arc-connected orientation of G.

Next, we show that the Lucchesi-Younger theorem also follows from the Edmond-Giles theorem.

Corollary 21 Let D = (V, A) be a weakly-connected digraph. The minimum size of a dijoin equals the maximum number of disjoint directed cuts in D.

**Proof:** Take  $\mathscr{C} = \{ U : \emptyset \neq U \subset V \text{ and } \delta_D^{\text{out}}(U) = \emptyset \}$ . Example 16 shows that  $\mathscr{C}$  is a crossing family. Take  $f : \mathscr{C} \to \mathbb{R}$  to be the function f(U) = -1 for all  $U \in \mathscr{C}$ . Clearly f is crossing submodular. So the Edmonds-Giles theorem shows that the following polyhedron is Box-TDI:

$$x(\delta^{\text{in}}(U)) - x(\delta^{\text{out}}(U)) \leq f(U) \qquad \forall U \in \mathscr{C}$$

$$d_a \leq x_a \leq c_a \qquad \forall a \in A$$

$$(3)$$

Next, for each  $a \in A$ , we define  $d_a = -\infty$  and  $c_a = 0$ . By the definition of  $\mathscr{C}$  and f, we may replace  $x(\delta_D^{\text{out}}(U))$  with 0 and f(U) with -1. Adding the following objective function yields the LP:

$$\max \sum_{a \in A} x_a$$
s.t.  $x(\delta^{\text{in}}(U)) \leq -1 \quad \forall U \in \mathscr{C}$ 

$$x_a \leq 0 \quad \forall a \in A$$

$$(4)$$

It is easier to interpret the meaning of this LP after replacing  $x_a$  with  $-x_a$ :

min 
$$\sum_{a \in A} x_a$$
  
s.t.  $x(\delta^{\text{in}}(U)) \ge 1 \quad \forall U \in \mathscr{C}$   
 $x_a \ge 0 \quad \forall a \in A$  (5)

Note that setting  $x_a > 1$  is never necessary to satisfy any constraints and furthermore penalizes the objective function. Thus we may assume that  $x_a \leq 1$ . The feasible integral solutions are therefore  $\{0,1\}$  solutions, corresponding to dijoins of D. Since (3) is Box-TDI, the LP (5) has an integral optimal solution  $x^*$ , corresponding to a minimum size dijoin. The dual of (5) is:

$$\max \sum_{U \in \mathscr{C}} y_{U}$$
s.t. 
$$\sum_{U: a \in \delta^{\text{in}}(U)} y_{U} \leq 1 \quad \forall a \in A$$

$$y_{U} \geq 0 \quad \forall U \in \mathscr{C}$$

$$(6)$$

The constraints ensure that  $y_U \leq 1$  for each  $U \in \mathcal{C}$ . The feasible integral solutions are therefore  $\{0,1\}$  solutions, each corresponding to a packing of directed cuts of D. Since (3) is Box-TDI, (6) has an integral optimal solution, corresponding to a maximum packing of directed cuts. Strong duality implies that the minimum size of a dijoin equals the maximum number of disjoint directed cuts.  $\square$

---

| 18.997 Topics in Combinatorial Optimization | April 22th, 2004  |
|---------------------------------------------|-------------------|
| Lecture 19                                  |                   |
| Lecturer: Michel X. Goemans                 | Scribe: Ben Recht |

## 1 Special cases of submodular flows

We saw last time that orientation of a 2k-edge connected graph into a k-arc connected digraph and the Lucchesi and Younger Theorem were special cases of submodular flows. Other familiar problems can also be phrased as submodular flows.

## 1.1 Example: Circulation

Let  $\mathcal{C} = 2^V \setminus \{\emptyset, V\}$  and let f be identically zero. Then for any  $U \in \mathcal{C}$ ,

$$x(\delta^{in}(U)) - x(\delta^{out}(U) \le 0$$

$$x(\delta^{in}(V \setminus U)) - x(\delta^{out}(V \setminus U) \le 0$$
(1)

which implies that  $x(\delta^{in}(U)) = x(\delta^{out}(U))$  for all  $U \subset V$ . In particular, we have that  $x(\delta^{in}(v)) = x(\delta^{out}(v))$  for all  $v \in V$ . In this case, the submodular flow reduces to the circulation problem from network flows.

## 1.2 Example: Matroid Intersection

Given two matroids on the same ground set,  $M_1 = (S, \mathcal{I}_1)$  and  $M_2 = (S, \mathcal{I}_2)$ , let  $S_1$  and  $S_2$  be identical copies of S and let  $V=S_1 \cup S_2$ .

Consider the collection

$$C = \{ U \subset V, U \neq \emptyset : U \subseteq S_1 \text{ or } S_1 \subseteq U \}.$$
 (2)

If A and B are elements of C with nonempty intersection and  $A \cup B \neq V$ , then

- $S_1 \subseteq A$ ,  $S_1 \subseteq B \implies S_1 \subseteq A \cap B$  and  $S_1 \subseteq A \cup B$
- $S_1 \subseteq A$ ,  $B \subseteq S_1 \implies A \cap B = B \subseteq S_1$  and  $S_1 \subseteq A \cup B = A$
- $A \subseteq S_1$ ,  $B \subseteq S_1 \implies A \cap B \subseteq S_1$  and  $A \cup B \subseteq S_1$

and hence for all cases,  $A \cup B$  and  $A \cap B$  are in  $\mathcal{C}$  proving that  $\mathcal{C}$  is a crossing family.

Let

$$f(U) = \begin{cases} r_1(U) & U \subseteq S_1 \\ r_2(V \setminus U) & S_1 \subseteq U \end{cases}$$
 (3)

f is readily seen to be crossing submodular by checking cases. If  $A \subseteq S_1$ ,  $B \subseteq S_1$  then the submodular inequality for f follows from submodularity of  $r_1$ . If  $S_1 \subseteq A$ ,  $S_1 \subseteq B$  then by deMorgan's laws

$$V \setminus (A \cup B) = (V \setminus A) \cap (V \setminus B)$$
  

$$V \setminus (A \cap B) = (V \setminus A) \cup (V \setminus B).$$
(4)

Therefore, submodularity of f follows from the submodularity of  $r_2$ . Finally, if  $S_1 \subseteq A$ ,  $B \subseteq S_1$  then  $f(A \cap B) = r_1(A \cap B)$  and  $f(A \cup B) = r_2(V \setminus (A \cup B))$ . Since  $|B| \ge |A \cap B|$  and  $|V \setminus A| \ge |V \setminus (A \cup B)|$ , the submodular inequality holds here as well.

To define the arc set on V, let arcs connect the elements in  $S_2$  to their bijective copy in  $S_1$ . That is,

$$A = \{(s_2, s_1) : s \in S\} \tag{5}$$

Now consider the submodular flow constraints. On this graph  $\delta^{out}(U) = \emptyset$  for all  $U \in \mathcal{C}$ . If  $U \subset S_1$ ,

$$x(U) = x(\delta^{in}(U)) \le r_1(U). \tag{6}$$

If  $S_1 \subset U$ ,  $U = V \setminus U'$  and hence

$$x(U') = x(\delta^{in}(U)) \le r_2(U'). \tag{7}$$

Putting this all together, we find that the submodular flow polytope is defined by

$$\left\{
\begin{array}{ll}
x(U) \le r_1(U) & \forall U \subset S \\
x(U) \le r_2(U) & \forall U \subset S \\
x_s \ge 0 & \forall s \in S
\end{array}
\right\}$$
(8)

which is the matroid intersection polytope.

We will see shortly that the proof of the Edmonds and Giles theorem will use similar techniques as those presented in the proof of the total dual integrality of the matroid intersection polytope.

## 2 Proof of Edmonds and Giles Theorem

We will prove the Edmonds and Giles theorem by showing that the optimal solution is defined by a totally unimodular system of equations. Here the particular notion we will exploit is

**Definition 1** A set  $\mathcal{F} \subseteq 2^V$  is cross-free if for any  $F_1$ ,  $F_2$  in  $\mathcal{F}$ , either  $F_1 \subseteq F_2$ ,  $F_2 \subseteq F_1$ ,  $F_1 \cap F_2 = \emptyset$  or  $F_1 \cup F_2 = V$ .

We can now proceed to prove the following

**Theorem 1 (Edmonds-Giles)** Let C be a crossing family on V, let  $f: C \to \mathbb{R}$  be crossing submodular, then the polytope

$$\begin{cases}
 x(\delta^{in}(U)) - x(\delta^{out}(U)) \le f(U) & \forall U \in \mathcal{C} \\
 d_a \le x_a \le c_a & \forall a \in A
\end{cases}$$
(9)

is totally dual integral.

**Proof:** Take w to be an integral vector and consider the linear program

$$\max_{s.t.} \quad \sum_{a} w_{a} x_{a}$$

$$s.t. \quad x(\delta^{in}(U)) - x(\delta^{out}(U)) \le f(U) \quad \forall U \in \mathcal{C}$$

$$d_{a} \le x_{a} \le c_{a} \qquad \forall a \in A.$$

$$(10)$$

The associated dual problem is

$$\min_{\mathbf{s.t}} \quad \sum_{\substack{U \in \mathcal{C} \\ v \notin U \\ v \in U}} f(U)y_U - \sum_{\substack{a \\ u \in U \\ v \notin U}} d_a s_a + \sum_{\substack{a \\ u \in u \\ v \notin U}} c_a t_a \\ \forall a = (u, v) \in A$$

$$\forall a = (u, v) \in A$$

$$y_U \ge 0, \ s_a \ge 0 \ t_a \ge 0.$$
(11)

We will now construct an optimum dual solution such that the set  $\mathcal{F} = \{U : y_U > 0\}$  is cross-free. Suppose there are sets  $F_1$  and  $F_2$  in  $\mathcal{F}$  such that  $F_1 \not\subseteq F_2$ ,  $F_2 \not\subseteq F_1$ ,  $F_1 \cap F_2 \neq \emptyset$  and  $F_1 \cup F_2 \neq V$ .

Let  $\epsilon = \min\{y_A, y_B\}$  and define a new dual vector y' as

$$y_T' = \begin{cases} y_T - \epsilon & T = F_1 \text{ or } T = F_2 \\ y_T + \epsilon & T = F_1 \cap F_2 \text{ or } T = F_1 \cup F_2 \\ y_T & \text{otherwise} \end{cases}$$
 (12)

y' is readily seen to be feasible as any decrease in the value of  $y_{F_1}$  or  $y_{F_2}$  is matched by an increase in the value of  $y_{F_1 \cup F_2}$  and  $y_{F_1 \cap F_2}$ . Furthermore, y' is optimal as

$$c(y') = c(y) - \epsilon[f(F_1) + f(F_2) - f(F_1 \cap F_2) - f(F_1 \cup F_2)] \le c(y)$$
(13)

We can repeat this process of eliminating crosses until we are left with a cross free family. The process terminates because if we consider the potential function

$$\psi(y) = \sum_{U \in \mathcal{C}} y_U |U| |V \setminus U| \tag{14}$$

then  $\psi(y') \leq \psi(y)$ .

It suffices to show that the matrix defined by

$$\sum_{U:u \notin U, v \in U} y_U - \sum_{U:u \in U, v \notin U} y_U \qquad U \in \mathcal{F}$$
 (15)

is totally unimodular when  $\mathcal{F}$  is cross-free. This follows from

**Theorem 2** Let  $\mathcal{F}$  be a cross-free family on  $2^V$ . Let M be an  $|A| \times |\mathcal{F}|$  matrix such that column f is the vector  $\chi^{\delta^{in}(U)} - \chi^{\delta^{out}(U)}$ . Then M is totally unimodular.

which is proved in chapter 13 of Shrijver and follows from an inductive argument similar to the one presented for matroid intersection.

# 3 Algorithms for submodular flows

Knowing that the submodular flow polytope is totally dual integral does not explicitly tell us how to optimize over it. However, optimization can be performed in polynomial time using submodular function minimization. Given an  $x \in \mathbb{R}^{|V|}$  the function

$$f(U) - x(\delta^{in}(U)) + x(\delta^{out}(U)) \tag{16}$$

is submodular on  $\mathcal{C}$ . This is because

$$g(U) = -x(\delta^{in}(U)) + x(\delta^{out}(U)) \tag{17}$$

is modular. Indeed, for  $A, B \subset V$ 

$$x(\delta^{in}(A)) + x(\delta^{in}(B)) = x(\delta^{in}(A \cap B)) + x(\delta^{in}(A \cup B)). \tag{18}$$

and similar equality holds for  $\delta^{out}$ . Since minimizing a submodular function can be performed in polynomial time, we can compute

$$\min_{U \in \mathcal{C}} f(U) - x(\delta^{in}(U)) + x(\delta^{out}(U)) \tag{19}$$

efficiently. This provides the minimal violated constraint which we can use to construct a separating hyperplane and run the the ellipsoid algorithm.

This method is not efficient in practice, so typically submodular flows are solved via a reduction to polymatroid intersection. Polymatroids are generalizations of matroids where the rank of a set may be larger than the cardinality of that set. But there are special cases where even this is machinery not necessary. One such example is orienting a 2k-edge connected graph into a k-arc connected digraph where we only need to employ matroid intersection.

#### 3.1 Orienting a 2k-edge connected graph

Let S denote the set of all pairs of vertices (u, v). Construct two matroids with ground set S as follows. Let  $M_1$  be the partition matroid which allows only one of (u, v) or (v, u) to be selected. Define the bases for  $M_2$  to be sets  $B \subset S$  such that |B| = |E| and for U a nonempty subset of V which does not equal V

$$|B \cap H(U)| \le |E(U)| + |\delta(U)| - k \tag{20}$$

here  $H(U) = \{(u, v) \in S : v \in U\}.$ 

We assert the following to be proved next time

**Proposition 3**  $M_2$  is a matroid

**Proposition 4** Testing independence in  $M_2$  can be performed by network flows.

The theorem of Nash-Williams from last time shows that these two matroids have a common basis (and the minmax relation for matroid intersection would also show it). Assuming the two propositions, it follows immediately that we can find this basis using matroid intersection. It is similarly immediate that a common basis for  $M_1$  and  $M_2$  is an orientation of G which is k-arc connected.

---

| 18.997 | <b>Topics</b> | in | Combinatorial | Optimization |
|--------|---------------|----|---------------|--------------|
|--------|---------------|----|---------------|--------------|

April 27, 2004

## Lecture 20

Lecturer: Michel X. Goemans Scribe: Jan Vondrák

## 1 k-arc-connected orientations

We continue the discussion of how a 2k-edge-connected graph can be oriented so that the resulting digraph is k-arc-connected. Last time we have seen that this can be achieved using submodular flows. Today we present a different approach, which relates the problem to matroid intersection.

Let G = (V, E) be a 2k-edge-connected graph and let D = (V, A) denote the bidirected version of G, with two arcs (u, v) and (v, u) for each edge  $\{u, v\}$ . (All graphs in this lecture can be multigraphs.) We define two matroids on the ground set of arcs A. The first one is a partition matroid:

$$\mathcal{M}_1 = (A, \{B \subseteq A : \forall \text{edge } (u, v); B \text{ contains at most one of the arcs } (u, v), (v, u)\}).$$

The bases of  $\mathcal{M}_1$  are exactly the orientations of G. The second matroid, which will force the orientation to be k-arc-connected, is more involved. Define

- $H(U) = \{(v, u) \in A : u \in U\}$
- $C = \{H(U) : \emptyset \subset U \subset V\}$
- $f(H(U)) = |E(U)| + |\delta(U)| k = |E| |E(V \setminus U)| k$

In other words, H(U) is the set of arcs with their "head" in U (either crossing the cut into U or contained inside U), and f(H(U)) is the maximum number of edges oriented like this, so that k arcs leaving U are still available. Note that  $\mathcal{C}$  forms a crossing family:  $\forall H_1, H_2 \in \mathcal{C}; H_1 \cap H_2 \neq \emptyset, H_1 \cup H_2 \neq A \Rightarrow H_1 \cap H_2 \in \mathcal{C}, H_1 \cup H_2 \in \mathcal{C}$ . This is simply because  $H(U_1) \cap H(U_2) = H(U_1 \cap U_2)$  and  $H(U_1) \cup H(U_2) = H(U_1 \cup U_2)$ . Also,  $f(H(U)) = |E| - |E(V \setminus U)| - k$  is a crossing submodular function on  $\mathcal{C}$ : since  $|E(V \setminus U_1)| + |E(V \setminus U_2)| \leq |E(V \setminus (U_1 \cap U_2))| + |E(V \setminus (U_1 \cup U_2))|$ ,  $f(H_1 \cap H_2) + f(H_1 \cup H_2) \leq f(H_1) + f(H_2)$ . Given these properties, we shall prove that

$$\mathcal{M}_2 = (A, \{B \subseteq A : |B| \le |E| \& \forall H \in \mathcal{C}; |B \cap H| \le f(H)\})$$

is a matroid. Then, k-arc-connected orientations correspond exactly to common bases of  $\mathcal{M}_1 \cap \mathcal{M}_2$ : bases of  $\mathcal{M}_1$  are orientations of G, and an orientation is a base of  $\mathcal{M}_2$  if and only if it has at most  $\delta(U) - k$  arcs across any directed cut  $\delta^{in}(U)$ , i.e. it must have at least k arcs across  $\delta^{out}(U)$ . Therefore a k-arc-connected orientation can be found using matroid intersection. <sup>1</sup>

It remains to prove that  $\mathcal{M}_2$  is a matroid. This is implied by the following lemma.

**Lemma 1** Let  $C \subseteq 2^A$  be a crossing family and  $f: C \to \mathbf{Z}$  a crossing submodular function. Then for any  $k \in \mathbf{Z}_+$ ,

$$\mathcal{B} = \{ B \subset A : |B| = k \& \forall H \in \mathcal{C}; |B \cap H| < f(H) \}$$

are the bases of a matroid.

**Proof:** We have to prove the exchange property for  $\mathcal{B}$ . Let  $B_1, B_2 \in \mathcal{B}$ ,  $i \in B_1 \setminus B_2$  and  $j \in B_2 \setminus B_1$ . If  $B_1 - i + j \notin \mathcal{B}$ , it means that for some  $H \in \mathcal{C}$ ,  $|B_1 \cap H| = f(H)$ ,  $i \notin H$  and  $j \in H$ , so that we violate the condition by exchanging j for i. Assume that this holds for every  $j \in B_2 \setminus B_1$ .

<sup>&</sup>lt;sup>1</sup>provided that membership in  $\mathcal{M}_2$  can be tested efficiently, which is not explained here.

For each  $j \in B_2 \setminus B_1$ , let  $H_j \in \mathcal{C}$  be the maximal set such that  $i \notin H_j, j \in H_j$  and  $|B_1 \cap H_j| = f(H_j)$ . These sets are disjoint; if  $H_j \cap H_{j'} \neq \emptyset$  and  $|B_1 \cap H_j| = f(H_j)$ ,  $|B_1 \cap H_{j'}| = f(H_{j'})$ , then by crossing submodularity  $|B_1 \cap (H_j \cup H_{j'})| = f(H_j \cup H_{j'})$  which contradicts the maximality of  $H_j$  and  $H_{j'}$ . Let  $\mathcal{P} = \{H_j : j \in B_2 \setminus B_1\}$  denote the collection of these disjoint sets, and  $W = A \setminus \bigcup \mathcal{P}$  the set of remaining uncovered elements. For each  $H_j \in \mathcal{P}$ , we have  $|B_2 \cap H_j| \leq f(H_j) = |B_1 \cap H_j|$ . All the elements of  $B_2 \setminus B_1$  are covered by  $\mathcal{P}$ , so  $B_2 \cap W \subseteq B_1 \cap W$ , and there is an element  $i \in W$  which belongs to  $B_1$  but not  $B_2$ . Therefore  $|B_2 \cap W| < |B_1 \cap W|$  and  $|B_2| < |B_1|$  which is a contradiction.

## 2 Splitting off

Now we turn to a technique developed by László Lovász, which is very useful for *connectivity augmentation* and other questions concerning edge connectivity.

**Theorem 2** Let G = (V + s, E) be a graph, such that the degree of s is even, and

$$\forall U; \emptyset \subset U \subset V \Rightarrow |\delta(U)| \ge k \tag{1}$$

Then there are edges (s, u), (s, t) such that

$$G' = (V+s, E \setminus \{(s,u),(s,t)\} \cup \{(t,u)\})$$

satisfies Condition 1.

In other words, we can "split off" a vertex s of even degree, by replacing pairs of edges incident with s by other edges in the graph, and we preserve k-edge-connectivity between all vertices different than s in the remaining graph. We prove the theorem later. Now let's demonstrate its application to the construction of all 2k-edge-connected graphs. We first need a lemma.

**Lemma 3** Every edge-minimal k-edge connected graph has a vertex of degree k.

**Proof:** In a k-edge-connected graph, every cut contains at least k edges. If it's edge-minimal, every edge is contained in a cut of size exactly k (otherwise we can remove the edge without decresing connectivity). Let  $S \subset V$  be minimal such that  $|\delta(S)| = k$ . If |S| = 1, we get a vertex of degree k. We prove that |S| > 1 leads to a contradiction. G[S] is connected (otherwise S is not minimal), and so G[S] contains an edge e. Let  $\delta(T)$  be a cut of size k, cutting e (therefore  $S \cap T \neq \emptyset$ ). If  $S \cup T \neq V$ , by submodularity,  $\delta(S \cap T)$  and  $\delta(S \cup T)$  are also cuts of size k. If  $S \cup T = V$ , then  $\delta(S \setminus T) = \delta(T)$  would be a cut of size k. In any case, we get a contradiction with the minimality of S.

**Theorem 4** Let  $M_{2k}$  denote a multigraph of 2k parallel edges between two vertices. Any 2k-edge-connected graph can be built from  $M_{2k}$  by

- adding edges
- pinching k edges: taking k edges  $(u_1, v_1), \ldots (u_k, v_k)$ , adding a new vertex s, and replacing each  $(u_i, v_i)$  by  $(s, u_i)$  and  $(s, v_i)$ .

**Proof:** Start with a 2k-edge-connected graph. Remove edges, until there is a vertex s of degree 2k (whose existence follows from the previous lemma). Apply the splitting-off lemma k times, and remove vertex s while preserving k-edge-connectivity. Then continue, until G shrinks to a 2-vertex graph, which must be a multigraph of at least 2k parallel edges. We remove some edge to obtain  $M_{2k}$ . The reverse procedure consists of repeatedly adding edges and pinching collections of k edges.

**Note:** This gives another proof that any 2k-edge-connected graph G has a k-arc-connected orientation. We start from  $M_{2k}$ , where k edges are oriented each way. We build G by adding edges (with arbitraty orientation) and pinching edges, replacing an arc by two arcs oriented the same way. This procedure preserves k-arc-connectivity.

## 3 Connectivity augmentation

In this section, we use splitting-off to solve the problem of augmenting a graph by adding some edges, so that the graph becomes k-edge-connected. Let  $U \subset V$  and  $x : V \to \mathbf{Z}$ . We denote  $d_E(U) = |\delta(U) \cap E|$  and  $x(U) = \sum_{v \in U} x(v)$ .

**Lemma 5** Given G = (V, E), there exists of set of edges F such that  $(V, E \cup F)$  is k-edge-connected and F has prescribed degrees  $d_F(v) = x(v)$ , if and only if

- x(V) is even, and
- $\forall U; \emptyset \subset U \subset V \Rightarrow d_E(U) + x(U) \geq k$ .

**Proof:** These conditions are clearly necessary; we'll now show their sufficiency. For G = (V, E) and  $x : V \to \mathbf{Z}$ , add a new vertex s, connecting it to each  $v \in V$  by x(v) parallel edges. If x(V) is even, the degree of s is even. Due to the second condition, we have augmented all cuts  $\delta(U), \emptyset \subset U \subset V$ , to size at least k, so we can apply splitting off. It follows that edges incident with s can be replaced by a set of edges F with prescribed degrees x(v), while preserving k-edge-connectivity.  $\Box$ 

This yields an approach to finding the smallest augmenting set F. Find x(v) such that  $\forall U, \emptyset \subset U \subset V; d_E(U) + x(U) \geq k$  and x(V) is minimal. If x(V) turns out odd, we increase some x(v) by 1 (arbitrarily). In any case, we can augment G to a k-edge-connected subgraph by adding  $\lceil x(V)/2 \rceil$  edges, which is optimal.

**Theorem 6** G can be augmented to a k-edge-connected graph by adding  $\gamma$  edges, if and only if for any collection of disjoint subsets of vertices  $\mathcal{P}$ :

$$\sum_{U \in \mathcal{P}} (k - d_E(U)) \le 2\gamma.$$

**Proof:** Again the condition is clearly necessary; we now show sufficiency. Assume that  $\gamma$  satisfies the condition of the lemma. Start with x(v) = k. Decrease the x(v) values arbitrarily, maintaining

$$\forall U: \emptyset \subset U \subset V \Rightarrow x(U) > k - d_E(U).$$

If we cannot decrease any x(v) anymore, each v with  $x(v) \geq 1$  must be contained in a subset U for which equality  $x(U) = k - d_E(U)$  holds. Let  $\mathcal{P}$  denote the collection of maximal subsets  $U \subset V$  such that  $x(U) = k - d_E(U)$ . Consider any  $S, T \in \mathcal{P}$ ; if  $S \cup T = V$ , then  $x(V) \leq x(S) + x(T) = (k - d_E(V \setminus S)) + (k - d_E(V \setminus T)) \leq 2\gamma$ .

If  $S \cup T \neq V$  for any  $S, T \in \mathcal{P}$ , then  $\mathcal{P}$  must be a collection of disjoint sets. Assume  $S \cap T \neq \emptyset$ : then  $x(S) + x(T) = (k - d_E(S)) + (k - d_E(T)) \leq (k - d_E(S \cap T)) + (k - d_E(S \cup T)) \leq x(S \cap T) + x(S \cup T) = x(S) + x(T)$ , i.e. all inequalities are equalities and  $x(S \cup T) = k - d_E(S \cup T)$  which contradicts the maximality of S, T. Therefore,  $\mathcal{P}$  is a partition of  $\{v \in V : x(v) \geq 1\}$  and

$$x(V) = \sum_{U \in \mathcal{P}} x(U) = \sum_{U \in \mathcal{P}} (k - d_E(U)) \le 2\gamma.$$

Finally, we increment some x(v) to make x(V) even, if necessary. Consequently, x satisfies the conditions of Lemma 5,  $x(V) \leq 2\gamma$ , and therefore we can augment G to a k-edge-connected subgraph by adding at most  $\gamma$  edges.

The condition on x(v) in the proof can be checked efficiently (by min-cut computations). Therefore we can find the minimum set of  $\gamma$  edges which augment edge connectivity to k, in polynomial time. In contrast, the connectivity augmentation problem with edge weights is NP-hard.

---

April 29th, 2004

## Lecture 21

Lecturer: Michel X. Goemans Scribe: Mohammad Mahdian

## 1 The Lovasz splitting-off lemma

Lovasz's splitting-off lemma states the following.

**Theorem 1** Let  $G = (V \cup \{s\}, E)$  be a graph such that

$$\forall \emptyset \neq U \subseteq V: \quad d(U) \ge k,\tag{1}$$

where d(U) denotes the number of edges between U and  $\bar{U}$ , and  $k \geq 2$ . Also, assume that d(s) (the degree of the vertex s) is even. Then for every  $(s,t) \in E$ , there exists  $(s,u) \in E$  such that the graph  $G' = (V \cup s, E \setminus \{(s,t),(s,u)\} \cup \{(t,u)\})$  also satisfies the condition (1).

**Proof:** Let S denote the set of neighbors of s in G (i.e.,  $S = \{u \in V : (s,u) \in E\}$ ). Fix a  $t \in S$ . We would like to show that there exists a  $u \in S$  such that condition (1) holds for the graph  $G' = (V \cup s, E \setminus \{(s,t),(s,u)\} \cup \{(t,u)\})$ . For the sake of contradiction, assume this does not hold. This means that for every  $u \in S$ , there exists a set U,  $\emptyset \neq U \subsetneq V$ , such that  $d(U) \leq k+1$  and  $u,t \in U$  (See Figure 1). In other words, the collection of all sets U with  $d(U) \leq k+1$  and  $t \in U$  covers S. Let C be a collection of maximal sets U with  $d(U) \leq k+1$  and  $t \in U$  that covers S.

Figure 1: A set U with  $d(U) \leq k+1$  and  $u \in U$ 

For every  $U \in \mathcal{C}$ , we have  $d(U) \leq k+1$  and  $d(U \cup \{s\}) \geq k$  (the latter inequality holds because  $d(U \cup \{s\}) = d(V \setminus U) \geq k$  by (1)). Therefore,

$$1 \ge d(U) - d(U \cup \{s\}) = d(s, U) - d(s, V \setminus U),$$

and so  $d(s, V \setminus U) + 1 \ge d(s, U)$ . On the other hand,  $d(s, V \setminus U) + d(s, U)$  is equal to the degree of s, which is an even number. Thus,  $d(s, V \setminus U)$  and d(s, U) have the same parity. Therefore,  $d(s, V \setminus U) \ge d(s, U)$ . In other words,  $d(s, U) \le \frac{1}{2}d(s)$ . This, together with the fact that  $t \in U$  for

Figure 2: Three sets  $U_1, U_2, U_3$  satisfying properties (2)

every  $U \in \mathcal{C}$ , shows that two of the sets  $U \in \mathcal{C}$  are not enough to cover S (i.e.,  $U_i \cup U_j \neq S$  for every  $U_i, U_j \in \mathcal{C}$ ). Therefore,  $\mathcal{C}$  must contain at least three sets  $U_1, U_2, U_3$  such that

$$t \in U_1 \cap U_2 \cap U_3$$

$$U_1 \setminus (U_2 \cup U_3) \neq \emptyset$$

$$U_2 \setminus (U_1 \cup U_3) \neq \emptyset$$

$$U_3 \setminus (U_1 \cup U_2) \neq \emptyset.$$
(2)

See Figure 2. We now use the following inequality which is a consequence of the *three-way* submodularity of the function d.

$$d(U_{1}) + d(U_{2}) + d(U_{3}) \geq d(U_{1} \cap U_{2} \cap U_{3}) + d(U_{1} \setminus (U_{2} \cup U_{3})) + d(U_{2} \setminus (U_{1} \cup U_{3})) + d(U_{3} \setminus (U_{1} \cup U_{2})).$$

$$(3)$$

It is straightforward to check all cases for an edge e and show that in each case, e is counted at least as many times on the left-hand side as it is counted on the right-hand side. This proves the above inequality. In fact, there is at least one edge st that is counted three times on the left-hand side, but only once on the right-hand side. Therefore, we can strengthen inequality (3) by adding a +2 to its right-hand side. Since every term on the left-hand side of (3) is at most k+1 (by the definition of  $U_i$ 's) and every term on the right-hand side is at least k (by assumption (1) on the graph G and properties (2)), the above inequality implies:

$$3k + 3 \ge 4k + 2 \Rightarrow k \le 1.$$

This gives us a contradiction since K was assumed to be at least 2.

## 2 Submodular function minimization

In the rest of this lecture, we sketch an algorithm for submodular function minimization. This is from Chapter 45 of Lex Schrijver's book.

Figure 3: The extended polymatroid  $EP_f$ 

**Problem Statement.** Given an oracle for a function  $f: 2^S \mapsto \mathbb{Z}$ , find a set  $U \subseteq S$  that minimizes f(U) over all subsets of S. We assume, without loss of generality, that  $f(\emptyset) = 0$ , otherwise we can minimize the function  $f(U) - f(\emptyset)$  instead of f.

This problem has many applications. As an example, consider the matroid intersection problem that we discussed in previous lectures. We showed that the convex hull of the of the intersection of two matroids is the set of all vectors x such that for every  $U \subseteq S$ ,  $x(U) \le r_1(U)$  and  $x(U) \le r_2(U)$ , where  $r_1$  and  $r_2$  are rank functions of the matroids. Therefore, we can optimize over the intersection of two matroids by solving a linear program with the above constraints. It is not obvious how to solve this linear program, since it is of exponential size. However, we can get polynomial-time separation by minimizing  $r_i(U) - x(U)$  over all  $U \subseteq S$ , and checking if the minimum is non-negative (for i = 1, 2). This can be done using an algorithm that solves the submodular function minimization, since  $r_1 - x$  is a submodular function.

Notice that it is not obvious that minimizing a submodular function given by an oracle is possible in polynomial time. Clearly, without the assumption of submodularity, it is not possible to find the minimum of the function before calling the oracle on all  $2^n$  points on which the function is defined. However, in the rest of this lecture we will sketch an algorithm due to Lex Schrijver that solves this problem for submodular functions in polynomial time.

We start by defining two polyhedra related to a submodular function f. The first polyhedron is called the *extended polymatroid* associated with f, and is defined as follows:

$$EP_f = \{ x \in \mathbb{R}^S : x(U) < f(U), \ \forall U \subseteq S \}.$$

Notice that this definition does not require  $x \ge 0$ . As an example, if  $S = \{1, 2\}$  and f is defined by  $f(\emptyset) = 0$ ,  $f(\{1\}) = 1$ ,  $f(\{2\}) = -1$ ,  $f(\{1, 2\}) = 0$ , then the extended polymatroid  $EP_f$  is the shaded area in Figure 3.

Prior to the algorithm of Schrijver, there was a polynomial-time (but not strongly polynomial-time) algorithm for submodular function minimization based on the ellipsoid algorithm and the polyhedron  $EP_f$ .

We define the second polyhedron, which is called the base polyhedron, as follows:

$$B_f = \{ x \in \mathbb{R}^S : \ x(S) = f(S), \ x(U) \le f(U), \ \forall U \subset S \}.$$

For example, for the function in the previous example, the polyhedron  $B_f$  consists of one point that is marked by a cross in Figure 3.

Our goal is the following.

**Goal.** Find a set  $U \subseteq S$  and a vector  $x \in B_f$  such that

$$x(v) \le 0 \qquad \forall v \in U \tag{4}$$

$$x(v) \ge 0 \qquad \forall v \notin U$$
 (5)

$$x(U) = f(U) \tag{6}$$

(7)

**Claim 2** If we can find a set U and vector  $x \in B_f$  satisfying properties (4)–(6), then U is the set that minimizes f(U).

**Proof:** This is because for every set  $W \subset S$ ,

$$f(U) = x(U) \le x(W) \le f(W),$$

where the first equality follows from property (6), the second inequality follows from (4) and (5), and the third inequality is a consequence of  $x \in B_f$ .

It is not clear how one can *prove* that a vector x belongs to  $B_f$ , since  $B_f$  is defined by exponentially many inequalities. We do this by expressing x as a convex combination of elements that are "obviously" in  $B_f$ . Such elements are defined below. In fact, these elements are extreme points (and the only extreme points) of  $B_f$ , but we do not need this fact in our proof.

Choose a total order  $\prec$  on S. For every  $v \in S$ , we define  $v_{\prec} = \{w \in S : w \prec v\}$ . The vector  $b^{\prec} \in \mathbb{R}^{S}$  is defined by

$$b^{\prec}(v) = f(v_{\prec} \cup \{v\}) - f(v_{\prec}).$$

Claim 3 For every total order  $\prec$  on  $S, b^{\prec} \in B_f$ .

**Proof:** By the definition of  $b^{\prec}$ ,  $b^{\prec}(S)$  is a telescopic sum that is equal to  $f(S) - f(\emptyset) = f(S)$ . Now, we prove that for every  $U \subseteq S$ ,  $b^{\prec}(U) \leq f(U)$ . We can prove this by induction on the size of U. If |U| = 0, then the statement is trivial. Otherwise, let v be the maximal element of U (with respect to  $\prec$ ), and apply the induction hypothesis on  $U \setminus \{v\}$ . This gives us  $b^{\prec}(U \setminus \{v\}) \leq f(U \setminus \{v\})$ . Since v is the maximal element of U, we have  $U \subseteq v_{\prec} \cup \{v\}$ . Therefore, by the submodularity of f, we have  $b^{\prec}(v) = f(v_{\prec} \cup \{v\}) - f(v_{\prec}) \leq f(U) - f(U \setminus \{v\})$ . By adding this inequality with the previous inequality we obtain  $b^{\prec}(U) = b^{\prec}(U \setminus \{v\}) + b^{\prec}(v) \leq f(U)$ .

We will find a vector x satisfying properties (4)–(6) and express the vector x as a convex combination of  $b^{\prec}$ 's, thereby showing that  $x \in B_f$ . We do this by starting from an arbitrary x that can be written as a convex combination of  $b^{\prec}$ 's, and modify x (along with the expression that gives x as a convex combination of  $b^{\prec}$ 's) until there exists a U such that (x, U) satisfies the desired properties.

Suppose we have a vector x that can be written as  $x = \sum_{i=1}^k \lambda_i b^{\prec_i}$ , where  $\lambda_i > 0$  for all i. Since  $B_f \subseteq \mathbb{R}^S = \mathbb{R}^n$  and all points in  $B_f$  must satisfy an equality, the dimension of  $B_f$  is at most n-1, and hence x can be expressed as a convex combination of n extreme points. So, we assume  $k \leq n$ .

For every  $\prec$  and every  $v \in S$ ,  $b^{\prec}(v_{\prec}) = f(v_{\prec})$ . We call the set  $v_{\prec}$  a prefix (also known as a lower ideal) of  $\prec$ . Therefore, if  $U \subset S$  is a prefix of  $\prec_i$  for every  $1 \leq i \leq k$ , then  $x(U) = \sum_{i=1}^k \lambda_i b^{\prec_i}(U) = \sum_{i=1}^k \lambda_i f(U) = f(U)$ . Thus, if we can find a set U that is a prefix of  $\prec_i$  for every  $1 \leq i \leq k$  and satisfies  $x(v) \leq 0$  for  $v \in U$  and  $x(v) \geq 0$  for  $v \notin U$ , then we are done. This motivates the following definition: Let D = (S, A) be a directed graph on the set of vertices S with the arc set  $A = \{(u, v) : u \prec_i v \text{ for some } 1 \leq i \leq k\}$ . By this definition, a set U is a prefix of every  $\prec_i$  if and only if  $\delta^{in}(U) = \emptyset$  in D.

Now, let  $\mathcal{P} = \{v : x(v) > 0\}$  and  $\mathcal{N} = \{v : x(v) < 0\}$ . We consider two cases:

- Case 1. D has no directed path from  $\mathcal{P}$  to  $\mathcal{N}$ . In this case, let U be the set of vertices v such that there is a path from v to some vertex of  $\mathcal{N}$ . Therefore, U contains  $\mathcal{N}$  but nothing from  $\mathcal{P}$ , and is a prefix for every  $\prec_i$ . Therefore, (x, U) satisfy the properties (4)–(6), and we are done.
- Case 2. There is a directed path from  $\mathcal{P}$  to  $\mathcal{N}$ . In this case, we change either x or the way x is expressed as a convex combination of  $b^{\prec}$ 's. Pick s and t on the path from  $\mathcal{P}$  to  $\mathcal{N}$  such that  $t \in \mathcal{N}, s \notin \mathcal{N}$ , and there is an arc from s to t in D (details of the selection rule is omitted). We would like to change x or its representation to kill the path from  $\mathcal{P}$  to  $\mathcal{N}$ . We can do this either by removing t from  $\mathcal{N}$  (i.e., increasing  $x_t$ ), or by removing the arc (s,t) from D. The arc (s,t) is present because  $s \prec_i t$  for some i. We focus on one such i, and will try to get s closer to t in  $\prec_i$ .

Figure 4: Path from  $\mathcal{P}$  to  $\mathcal{N}$  and the vertices s and t

Let  $\chi^t$  denote the unit vector along along the coordinate t (and similarly for  $\chi^s$ ). We show that for some  $\delta \geq 0$ ,  $x + \delta(\chi^t - \chi^s) \in B_f$ , and moreover, we can write  $x + \delta(\chi^t - \chi^s)$  as a convex combination in which s is *closer* to t. More precisely, we use the following lemma as a subroutine.

**Lemma 4** Given  $\prec$ , s, and t, express the vector  $b^{\prec} + \delta(\chi^t - \chi^s)$  for some  $\delta \geq 0$  as a convex combination of  $b^{\prec_{s,u}}$  for  $u \in (s,t]_{\prec} = \{u : s \prec u \leq t\}$ , where  $\prec_{s,u}$  is the total order that is obtained from  $\prec$  by moving u before s.

**Proof:** We assume that  $b^{\prec} = 0$ . This assumption is without loss of generality, because we can replace f(U) by  $f(U) - b^{\prec}(U)$  and apply the argument on this new function. By the submodularity of f, we have

$$b^{\prec_{s,u}}(v) = \begin{cases} b^{\prec}(v) = 0 & \text{if } v \prec s \text{ or } v \succ u \\ \leq 0 & \text{if } s \leq v \prec u \\ \geq 0 & \text{if } v = u. \end{cases}$$

The following table shows the pattern of non-negative and non-positive entries in  $b^{\prec_{s,u}}$ 's, for every  $u \in (s,u]_{\prec}$ . In this table, — denotes a non-positive entry, + denotes a non-negative

entry, and 0 denotes an entry that is zero.

| u |   | s |   |   |   |    |   | t |
|---|---|---|---|---|---|----|---|---|
| s |   |   |   |   |   |    |   |   |
|   | 0 | _ | + | 0 |   |    |   |   |
|   | 0 | _ | _ | + | 0 |    |   |   |
|   | 0 | _ | _ | _ | + | 0  |   | 0 |
|   |   |   |   |   |   |    |   |   |
|   |   | : |   |   |   | ٠. |   |   |
|   |   |   |   |   |   |    |   |   |
| t | 0 | _ | _ | _ |   |    | _ | + |

If the non-negative entry (+) on one row is zero (i.e.,  $b^{\prec_{s,u}}(u) = 0$  for some u), then all other entries of that row must also be zero, since the sum of the entries in each row must be the same as the sum of the entries in  $b^{\prec}$  (since they are both equal to f(S)), which is zero. Therefore, in this case, we can take  $\delta = 0$  and use  $b^{\prec_{s,u}}$  as the desired convex combination. The other case is when  $b^{\prec_{s,u}}(u) > 0$  for every  $u \in (s,t]_{\prec}$ . In this case, we can start from the last row of the table (i.e., the vector  $b^{\prec_{s,t}}$ ), and for every row of the table, from the row before t to the row after s, add a multiple of the row to the current vector so that the t entry cancels out the corresponding entry in the current vector. At the end, we will obtain a vector that has only one negative entry at position t and one positive entry at position t. Furthermore, since the sum of all entries should be zero, the absolute value of these two entries are equal. This means that for some t0, we can write t1, where t2 are convex combination of t3, t3. t4.

We iterate the procedure in the above lemma. Intuitively, every time we get s closer to t in at least one of  $\prec_i$ 's, without changing other  $\prec_i$ 's. We might also increase  $x_t$ . Therefore, after a finite number of iterations, we will either remove the arc (s,t) from D, or will remove t from N. For how s and t are chosen and the analysis of the running time of this procedure, see Lex Schrijver's book.

---

### Lecture 22

Lecturer: Michel X. Goemans Scribe: Alantha Newman

# 1 Multiflows and Disjoint Paths

Let G = (V, E) be a graph and let  $s_1, t_1, s_2, t_2, \ldots s_k, t_k \in V$  be terminals. Our goal is to find disjoint paths between  $s_i$  and  $t_i$  for each  $i, 1 \leq i \leq k$ . There are directed and undirected versions of this problem, i.e. G can be directed or undirected and we may want to find directed paths from  $s_i$  to  $t_i$  or undirected paths between these terminal pairs. Additionally, we specify if we want to find vertex disjoint paths or edge disjoint paths (arc disjoint paths for directed graphs). These disjoint path problems can be viewed as specific cases of the *multiflow problem*.

### 1.1 Multiflows

Suppose we are given the following inputs:

- a graph G = (V, E) (directed or undirected),
- terminals  $s_1, t_1, s_2, t_2, \dots s_k, t_k \in V$ ,
- demands  $d_i : i = 1, \ldots, k$ ,
- integer (or rational) capacities on the edges,  $c: E \to \mathcal{Z}^+$ .

For each i, find an  $(s_i, t_i)$ -flow  $f_i$  of value  $d_i$ . Note that even for undirected graphs, flow is directed. Let  $f_i(e)$  be the amount of flow from  $s_i$  to  $t_i$  that uses edge e. A valid flow must obey the capacity constraint: for each edge  $e \in E$ ,  $\sum_{i=1}^k f_i(e) \le c(e)$ .

#### 1.2 Edge Disjoint Paths

To find edge disjoint paths, we can set c(e) = 1 for all  $e \in E$  and then find an integer multiflow. The problem of finding vertex disjoint paths in a directed graph can be reduced to the problem of finding edge disjoint paths in a directed graph; every vertex  $v \in V$  undergoes the transformation shown in figure 1. Thus, a set of edge disjoint paths in the modified graph corresponds to a set of paths in the original graph in which each vertex is used at most once.

Figure 1: Each vertex undergoes the illustrated transformation.

Today, we focus on finding edge disjoint paths in undirected graphs. Note that the problem of finding edge disjoint paths is *very* different in terms of complexity for directed and undirected graphs.

Edge Disjoint Paths in Undirected Graphs: G is an undirected graph. Do there exist two edge disjoint paths between s and t? This problem can be solved easily by determining if the minimum s-t cut contains at least two edges.

Arc Disjoint Paths in Directed Graphs: G is a directed graph. Do there exist two arc disjoint paths, one from s to t and one from t to s? This problem is NP-hard!

The edge disjoint paths problem in undirected graphs can be reduced to the arc disjoint paths problem in directed graphs. Each edge in the original undirected graph is replaced by the gadget shown in figure 2.

Figure 2: Each edge in the original undirected graph is replaced by the above gadget.

### 1.3 Fractional Multiflow

We focus on edge disjoint paths (multiflows) in undirected graphs. When k = 1, flow is easy. We can find integer flow using the max-flow min-cut theorem. In general, deciding if a multiflow exists can be determined by solving a linear program consisting of flow and capacity constraints.

Let  $\mathcal{P}_i$  be set of all paths between  $s_i$  and  $t_i$ . We have a variable  $x_p$  for every such path  $p \in \mathcal{P}_i$ . We have the following primal LP:

$$\max_{p \in \mathcal{P}_i} 0 \cdot x$$

$$\sum_{p \in \mathcal{P}_i} x_p = d_i$$

$$\sum_{i: p \in \mathcal{P}_i, e \in p} x_p \leq c(e)$$

$$x_p \geq 0.$$

What does dual mean in this case? We use variables  $\ell(e)$  for each edge  $e \in E$ , and variables  $b_i$  for i = 1, ..., k.

$$\min \sum_{e \in E} c(e)\ell(e) - \sum_{i=1}^{k} b_i d_i$$

$$\sum_{e \in p} \ell(e) - b_i \geq 0 \quad \forall p \in \mathcal{P}_i \ i = 1, \dots k$$

$$\ell(e) \geq 0.$$
(1)

To make the term  $\left(-\sum_{i=1}^k b_i d_i\right)$  small, we should make  $b_i$  as large as possible. Fix the edge function  $\ell: E \to \mathcal{Q}$ . Then  $b_i$  is the (minimum)  $\operatorname{dist}_{\ell}(s_i, t_i)$ . The objective function of the dual (1) can be rewritten:

$$\sum_{e \in E} c(e)\ell(e) - \sum_{i=1}^k d_i \ dist_{\ell}(s_i, t_i).$$

If the primal LP is feasible, then there is no solution for the dual LP with a negative objective value. So there exists a fractional multiflow if and only if  $\forall \ell(e) \geq 0, e \in E$ , the following holds:

$$\sum_{e \in E} c(e)\ell(e) \ge \sum_{i=1}^{k} d_i \operatorname{dist}_{\ell}(s_i, t_i). \tag{2}$$

Duality shows that this is a necessary and sufficient for the existence of a fractional multiflow.

# 2 Integer Multiflows

In general, the problem of determining when there is an integer multiflow is NP-complete. However, there are special conditions that imply the existence of an integer multiflow in certain classes of graphs.

Let R be a set of edges:

$$R = \{(s_i, t_i) : i = 1, \dots k\}.$$
(3)

The set of edges in E outgoing from vertex set U is denoted by  $\delta_E(U)$  and the set of edges in R outgoing from vertex set U is denoted by  $\delta_R(U)$ . A necessary condition for the existence of a multiflow (and thus of an integer multiflow) is the cut condition:

$$c(\delta_E(U)) > d(\delta_R(U)), \quad \forall U \subset V.$$

In general, the cut condition is not sufficient to guarantee the existence of an integer multiflow (or fractional multiflow) in a graph. However, in some cases of the multiflow problem, the cut condition is sufficient for the existence of a fractional multiflow. Furthermore, there are several cases known where the cut condition implies the existence of an integer multiflow when the *Euler condition* is satisfied:

$$c(\delta_E(v)) + d(\delta_R(v))$$
 is even, for each vertex v.

For example, when k = 2, we have the following implications:

- (i) Cut condition  $\Rightarrow$  fractional multiflow.
- (ii) Cut condition and integer capacities  $\Rightarrow$  half-integral multiflow.
- (iii) Cut condition, integer capacities, and Euler condition ⇒ integral multiflow.

The first proof of (i) and (ii) for the case when k=2 was is due to Hu. The proof of (iii) is due to Rothschild and Winston. Note that (iii) implies (i) and (ii). For example, Consider the graph in Figure 3, let  $d_1=1, d_2=1$ . Let the capacity of each edge be 2. Note that the cut condition is satisfied but the Euler condition is not. However, suppose we double every capacity and demand, then the Euler condition is satisfied. We can convert an integer solution for this latter problem to a half-integral solution for the original problem.

Some "good" cases in which conditions (i), (ii) and (iii) are satisfied are:

1. If there are two commodities, i.e. k = 2, then cut condition and Euler condition are sufficient for integer multiflow.

Figure 3: When the capacity of each edge in this graph is 2 and  $d_1, d_2 = 1$ , the Euler condition is not satisfied. There exists a half-integral multiflow, but no integral multiflow.

- 2. G + D has no  $K_5$  minor, e.g. G + D is planar, where D is the demand graph, D = (V, R) (see (3)).
- 3.  $|\{(s_1, t_1), \dots, (s_k, t_k)\}| \le 4$ .
- 4. G is planar and all  $(s_i, t_i)$  are on boundary of outside face. (Note that this does not imply case 2.)
- 5. If there are 2 faces and for each i,  $(s_i, t_j)$  are both on the inside face or both on the outside face.

# 3 Two-Commodity Flows

**Theorem 1 (Rothschild and Whinston)** G = (V, E) is an undirected graph such that  $c(e) \in \mathcal{Z}^+$  for  $e \in E$ . Terminals  $s_1, t_1, s_2, t_2$  are in V, and demands  $d_1, d_2$  are positive integers. Additionally, the Euler condition is satisfied for G. Then G has an integer two-commodity flow if and only if the cut condition is satisfied.

**Proof:** Our goal is to find flows from  $s_1$  to  $t_1$  and from  $s_2$  to  $t_2$  with values  $d_1$  and  $d_2$ , respectively. We will show that if the cut condition is satisfied on G, then we can find such flows.

Figure 4: The graphs G' and G'' are constructed based on the given graph G.

First, based on the graph G, construct the graph G' as shown in figure 4. Let the edges  $(s', s_1)$  and  $(t_1, t')$  in G' have capacity  $d_1$  and the edges  $(s', s_2)$  and  $(t_2, t')$  in G' have capacity  $d_2$ . By the max-flow min-cut theorem, we can find an integer s'-t' flow g with value  $d_1 + d_2$ , since the min-cut of G' has value  $d_1 + d_2$ . Note that this s'-t' flow does not necessarily give a two-commodity flow for the original problem (since some of the flow going through  $s_1$  may end up in  $t_2$ ).

Since the Euler condition is satisfied, we will prove that we can assume that  $g(e) \equiv c(e) \mod 2$ . To show this, first notice that the Euler condition implies that the total capacity incident to any vertex of G' is even. Furthermore, any integral flow will use up an even amount of capacity incident to any vertex. Now consider all the edges  $e \in E$  such that  $g(e) \not\equiv c(e) \mod 2$ . Since it is the case

that  $\sum_{e \in \delta(v)} (g(e) - c(e)) = 0 \mod 2$ , it follows that an even number of edges adjacent to vertex v have  $g(e) \not\equiv c(e) \mod 2$ . Thus, the edges such that  $g(e) \not\equiv c(e) \mod 2$  make up an Eulerian graph (and do not contain the arcs incident to s' and t' that we added to G to make up G'). We can decompose this Eulerian graph into cycles, and push push one unit of flow across all these cycles (either increasing or decreasing the flow by one unit along it depending on the orientation), changing the parity of g(e) for each such edge. Thus, for all edges  $e \in E$ , we have that  $g(e) \equiv c(e) \mod 2$ .

For G'', we have the same argument. Thus, we find an integer flow h in G'' with value  $d_1 + d_2$  such that h(e) = c(e),  $\forall e \in E$ . Thus, for all edges  $e \in E$ ,  $h(e) = g(e) \mod 2$ . We arbitrarily orient the edges of E to obtain A. So for all  $a \in A$ ,  $h(a) \equiv g(a) \mod 2$ .

Now we define two flows on the graph G:

$$f_1(a) = \frac{1}{2}[g(a) + h(a)]$$
  
$$f_2(a) = \frac{1}{2}[g(a) - h(a)].$$

The following properties are true for the flows  $f_1$  and  $f_2$ :

- 1.  $f_1(a), f_2(a)$  are integer flows (since f(a) and g(a) have the same parity).
- 2.  $|f_1(a)| + |f_2(a)| = \frac{1}{2}|g(a) + h(a)| + \frac{1}{2}|g(a) h(a)| \le \max(|g(a)|, |h(a)|) \le c(a)$ .
- 3.  $f_1$  is  $d_1$  units of flow from  $s_1$  to  $t_1$  and  $f_2$  is  $d_2$  units of flow from  $s_2$  to  $t_2$ .

The last property holds because we can show that  $f_1(\delta^+(s_1)) - f_1(\delta^-(s_1)) = d_1$  and  $f_1(\delta^-(t_1)) - f_1(\delta^+(t_1)) = d_1$ . By conservation of flow, if we consider the vertex  $s_1$  in G, we have:

$$g(\delta^{+}(s_1)) - g(\delta^{-}(s_1)) = d_1 \tag{4}$$

$$h(\delta^{+}(s_1)) - h(\delta^{-}(s_1)) = d_1 \tag{5}$$

Equations (4) and (5) imply  $f_1(\delta^+(s_1)) - f_1(\delta^-(s_1)) = d_1$ .

$$g(\delta^{-}(t_1)) - g(\delta^{+}(t_1)) = d_1 \tag{6}$$

$$h(\delta^{-}(t_1)) - h(\delta^{+}(t_1)) = d_1. \tag{7}$$

Equations (6) and (7) imply  $f_1(\delta^-(t_1)) - f_1(\delta^+(t_1)) = d_1$ . Similarly, we can show that the last property holds for flow  $f_2$ . If we consider vertices  $s_2$  and  $t_2$  in G, we have:

$$g(\delta^{+}(s_2)) - g(\delta^{-}(s_2)) = d_2 \tag{8}$$

$$h(\delta^{-}(s_2)) - h(\delta^{+}(s_2)) = d_2 \tag{9}$$

$$g(\delta^{-}(t_2)) - g(\delta^{+}(t_2)) = d_2 \tag{10}$$

$$h(\delta^{+}(t_2)) - h(\delta^{-}(t_2)) = d_2. \tag{11}$$

Equations (8) and (9) imply  $f_2(\delta^+(s_2)) - f_2(\delta^-(s_2)) = d_2$  and equations (10) and (11) imply  $f_2(\delta^-(t_2)) - f_2(\delta^+(s_2)) = d_2$ .

As a final note, consider the problem of maximizing the sum of the flow between  $s_1$  and  $t_1$  and between  $s_2$  and  $t_2$ . This is the *max biflow problem*. A *bicut* is a cut separating  $s_1$  from  $t_1$  and  $s_2$  from  $t_2$ , thus it is either a cut separating  $s_1, s_2$  from  $t_1, t_2$  or a cut separating  $s_1, t_2$  from  $s_2, t_1$ . One can show that the following theorem follows from Theorem 1.

**Theorem 2** The maximum biflow equals the minimum bicut.

---

| 18.997 Topics in Combinatorial Optimization | May 13th, 2004       |
|---------------------------------------------|----------------------|
| Lecture 23                                  |                      |
| Lecturer: Michel X. Goemans                 | Scribe: Dan Stratila |

Consider a planar graph G = (V, E) and a set of terminal pairs  $R = \{(s_i, t_i) : i = \overline{1, k}\}$ . Assume G is planar,  $(V, E \cup R)$  is Eulerian, and all terminals lie on the outer face of G. In this lecture, we will cover the following results.

- The Okamura-Seymour theorem on the equivalence between the existence of  $s_i$ - $t_i$  edge-disjoint paths and the cut condition  $|\delta_E(S)| \leq |\delta_R(S)|, \forall S \subseteq V$  [OS81].
- The Wagner-Weihe linear-time algorithm for finding the edge-disjoint paths [WW93, RLWW95, WW95].

Chapter 74 of [Sch03] contains a proof of the Okamura-Seymour theorem, as well as a survey of related results.

# 1 The Okamura-Seymour Theorem

We begin with the main theorem.

**Theorem 1 (Okamura-Seymour)** Consider an undirected planar graph G = (V, E) and a set of terminal pairs  $R = \{(s_i, t_i) : s_i \in V, t_i \in V, i = 1, \dots, k\}$  s.t. the following conditions are satisfied:

- 1. The terminals are on the boundary of the outside face of G.<sup>1</sup>
- 2. The Euler condition:  $(V, E \cup R)$  is Eulerian.
- 3. The cut condition:  $|\delta_E(S)| \leq |\delta_R(S)|, \forall S \subseteq V$ .

Then there exist edge disjoint paths between  $s_i$  and  $t_i$ ,  $i = 1, \dots, k$ .

Note that since given 1 and 2, the necessity of 3 is obvious, the Theorem can also be stated as an equivalence condition, as is done, for example, in [Sch03].

To prove Theorem 1, we will use two lemmas. First, we show it suffices to consider cuts that result in connected subgraphs, and then we reduce the problem to the 2-connected case. As before, let  $d_E(S) := |\delta_E(S)|$ .

**Lemma 2** For any edge-disjoint path problem,  $d_E(S) \ge d_R(S), \forall \emptyset \ne S \subsetneq V$  if and only if  $d_E(S) \ge d_R(S), \forall \emptyset \ne S \subsetneq V$  s.t. G[S] and  $G[V \setminus S]$  are connected.

**Proof:** W.l.o.g. assume that G[S] is disconnected and consists of connected components  $G[S_1]$  and  $G[S_2]$ . If  $d_E(S) < d_R(S)$ , then

$$d_E(S_1) + d_E(S_2) \stackrel{(*)}{=} d_E(S) < d_R(S) \stackrel{(**)}{\leq} d_R(S_1) + d_R(S_2), \tag{1}$$

where (\*) holds since G[S] is disconnected, and (\*\*) holds since  $\delta(S) \subseteq \delta(S_1) \cup \delta(S_2)$ . Since  $d(\cdot) \geq 0$ , this implies  $d_E(S_1) < d_R(S_1)$  or  $d_E(S_2) < d_R(S_2)$ .

 $<sup>^{1}</sup>$ We will assume there is a fixed planar embedding associated with G.

Figure 1: A 1-connected graph separated by cut vertex v into 4 smaller components. Path edges are in bold; the original requirement set is  $R = \{(s_1, t_1), (s_2, t_2), (s_3, t_3)\}$ , and the new requirement set is  $R' = \{(s_1, v), (t_1, v), (s_2, t_2), (s_3, v), (t_3, v)\}$ .

**Lemma 3** We can assume w.l.o.g. that G is 2-connected.

**Proof:** If G is not connected, we can inductively reduce the problem to a set of smaller subproblems, one for each connected component. If G is 1-connected, then there exists a vertex v s.t. G - v is disconnected.

For any i, if  $s_i$  and  $t_i$  are in the same component of G - v, then any solution can be transformed into a solution where the  $s_i$ - $t_i$  path is entirely contained in that component. If  $s_i$  and  $t_i$  are in different components, then v will belong to any  $s_i$ - $t_i$  path, and replacing R with

$$R \setminus \{(s_i, t_i)\} \cup \{(s_i, v), (t_i, v)\}$$

$$\tag{2}$$

yields an equivalent instance (see Figure 1).

Repeating this for all i we reduce the problem to a set of smaller problems with terminals on the boundary and that satisfy the Euler condition. Moreover, each problem satisfies the (induced) cut condition if and only the original problem does. By induction, we assume that each subproblem has a solution to the edge-disjoint paths problem if the cut condition is satisfied. Since we can reconstruct the solution to the original problem from the subproblem solutions, it follows that the original problem has a solution to the edge-disjoint paths problem if the cut condition is satisfied.

We can also begin with the counterexample construction, and show that a (2|E| - |R|)-minimal counterexample needs to be 2-connected, as is done in [Sch03].

### Outline of proof of Theorem 1:

- 1. We take a minimal (according to some criterion) counterexample.
- 2. We show that properties (3, 4, 5) hold for the counterexample.
- 3. We take a cardinality minimal tight set  $X \subseteq V$ , and using (3, 4, 5) derive the final contradiction.

Figure 2: Example of set S that contains non-consecutive vertices of C, and thus disconnects  $G[V \setminus S]$ . The path P is in bold.

**Proof of Theorem 1:** Suppose the theorem is not true, and consider the set of edge-minimal counterexamples; from this set, select a counterexample with as many terminals as possible. Let C be the simple cycle along the border of the outside face.

Suppose there is pair s.t.  $s_i$  and  $t_i$  are adjacent in E, then we can remove both the edge from E and the pair from R. The resulting instance satisfies the Euler condition, since we deleted two parallel edges from  $(V, E \cup R)$ ; it also satisfies the cut condition, since any cut either crosses both the edge and  $(s_i, t_i)$  or neither. However, since a feasible solution to the modified instance yields a feasible solution to the original instance, the modified instance has no feasible solution., and is thus a counterexample. This contradicts the minimality of the original counterexample, hence

there is no pair with 
$$(s_i, t_i) \in E$$
. (3)

We will call a set S tight if  $\delta_E(S) = \delta_R(S)$ . Suppose that there is no tight set, and remove some edge  $e = (u, v) \in E(C)$  and add (u, v) to R. Let the corresponding sets of the new instance be E' and R'. Fix a set  $S \subset V$ , and note that  $\delta_{E'}(S) - \delta_{R'}(S)$ , and  $\delta_E(S) - \delta_R(S) \geq 0$  are both even. Therefore the cut condition can only be violated for S in the new instance if S was tight in the original instance. It follows that the new instance satisfies the cut condition, which contradicts the minimality of the counterexample (again because we can translate a feasible solution to the new instance into one for the original instance), thus

Next, we show that since G[S] and  $G[V \setminus S]$  are connected, both S and  $V \setminus S$  cannot contain non-consecutive elements of V(C). To see this, suppose w.l.o.g. that S contains vertices  $v, w \in V(C)$  s.t. for either side of C between v and w, not all vertices between v and w are in S. Since G[S] is connected, there is a path P from v to w in G[S]. Since G is planar and v, w belong to the outside face, this path implies  $G[V \setminus S]$  is disconnected (see Figure 2). This is a contradiction, thus

both S and 
$$V \setminus S$$
 contain consecutive elements of  $V(C)$ , (5)

or in other words  $|\delta_E(S) \cap E(C)| = 2$ .

Take a |X|-minimal tight set X, let  $(w, u) \in E(C)$  with  $w \in X, u \notin X$ , and select a terminal pair  $(s_r, t_r)$  s.t.  $s_r \in X, t_r \notin X$ , and  $t_r$  is closest (w.r.t the number of edges in a

a) The set-up.

b) The contradiction.

Figure 3: The counterexample construction for Theorem 1. Edges crossing the cut X are in bold. Demand pairs are denoted by dotted lines, and the node yielding the contradiction is drawn hollow.

path) to u. By (3), we can take  $v \in \{w, u\} \setminus \{s_r, t_r\}$  (see Figure 3.a)). Consider a new set of demand pairs

$$R' = R \setminus \{(s_r, t_r)\} \cup \{(s_r, v), (t_r, v)\},\tag{6}$$

and note that the terminals are still on the boundary of the outside face, and the Euler condition is still satisfied, because in  $(V, E \cup R)$  the degree of v increased by 2, while all other degrees remained unchanged. Therefore, the cut condition must be violated for R', otherwise it would contradict the minimality of the counterexample.

This implies we can pick a violating set  $Y, v \in Y$ , which immediately implies by construction of R',  $s_r \notin Y, t_r \notin Y$ , hence  $v \notin \{s_r, t_r\}$  at all. Moreover,  $d_E(Y) < d_{R'}(Y)$  implies  $d_E(Y) = d_R(Y)$ , i.e. Y was tight. Now, note that

$$d_R(X \cap Y) + d_R(X \cup Y) \stackrel{\text{(i)}}{=} d_R(X) + d_R(Y) \stackrel{\text{(ii)}}{=} d_E(X) + d_E(Y)$$

$$\stackrel{\text{(iii)}}{\geq} d_E(X \cap Y) + d_E(X \cup Y) \stackrel{\text{(iv)}}{\geq} d_R(X \cap Y) + d_R(X \cup Y), \quad (7)$$

since:

- (i)  $d_R(X \cap Y) + d_R(X \cup Y) \leq d_R(X) + d_R(Y)$  due to submodularity, and a strict inequality can only occur if there is a demand pair from  $X \setminus Y$  to  $Y \setminus X$ . This cannot happen, since  $t_r \notin Y$  and  $u \in Y$  imply the endpoint of this pair in  $Y \setminus X$  would be closer to u, due to (5) (see Figure 3.b)).
- (ii) This is simply because both X and Y are tight.
- (iii) This is again due to submodularity of cut cardinality.
- (iv) The cut condition implies  $d_E(X \cap Y) \ge d_R(X \cap Y)$  and  $d_E(X \cup Y) \ge d_R(X \cup Y)$ .

Therefore, equality holds throughout, and since  $d_E(X \cap Y) \ge d_R(X \cap Y)$  and  $d_E(X \cup Y) \ge d_R(X \cup Y)$  and all quantities are nonnegative, we get  $d_E(X \cap Y) = d_R(X \cap Y)$ . However  $|X \cap Y| < |X|$ , since  $s_r \in X$ ,  $s_r \not Y$ .

Unless  $X \cap Y = \emptyset$ , this violates the minimality of X (if  $X \cap Y$  is disconnected, then one of the components will be violating the cut condition, and the minimality of X). If  $X \cap Y = \emptyset$ , then  $w \notin Y$ , hence  $v = u \in Y$ . Since  $w \in X$  and  $u \notin X$ , this implies (u, w) connects  $X \setminus Y$  and  $Y \setminus X$ , which contradicts the "sandwich" equality (iii) of (7).

## 2 The Wagner-Weihe algorithm

In this section we present the Wagner-Weihe algorithm. The algorithm either finds the  $s_i$ - $t_i$  edge-disjoint paths, or a proof of infeasibility in the form of a violated cut. The running time is O(n), and, for our description, we assume a planar embedding and a sorted list of edges to be given. In the algorithm we will also assume, w.l.o.g., that each terminal source or destination is a separate node connected to the original node by an edge.

#### Step 1: Re-pair.

- a) Choose a terminal  $x \in \bigcup_{i=1}^k \{s_i, t_i\}$ , and enumerate the vertices of V(C) counterclockwise. When encountering a vertex in a demand pair  $\{s_i, t_i\}$  for the first time, associate to it an opening parenthesis, and when encountering one for the second time, associate to it a closing parenthesis.
- b) Obviously, the parenthesis in the result string are correctly nested. Each pair of matching parenthesis will define a new demand pair  $\{s_i', t_i'\}$ , and we will number them in order of closing parenthesis.

For example, for the graph in Figure 4, we renumber starting from the pair 5 terminal on the left side of the graph, and obtain (the new numbering is denoted, through a slight abuse of notation, by  $1', 2', \ldots$ ):

| Original demand pair | 5  | 3  | 4  | 2  | 4  | 5  | 1  | 3  | 2  | 1  |
|----------------------|----|----|----|----|----|----|----|----|----|----|
| Parenthesis          | (  | (  | (  | (  | )  | )  | (  | )  | )  |    |
| New demand pair      | 5' | 4' | 2' | 1' | 1' | 2' | 3' | 3' | 4' | 5' |

c) For i = 1' to k', proceed from  $s_i$  by "right-first" search, i.e. when at a node, always take the right-most edge (clockwise) that is not already in use. If stuck in the graph, or if reached the wrong terminal, stop, one can find a violated cut.

#### Step 2: return to original pairing.

- a) Remove edges unused in the paths from step 1, and orient the remaining edges in the direction used.
- b) Enumerate the pairs of R in the order of their closing parenthesis. For each pair, do "right-first search" on the resulting graph. If stuck in the graph, or if reached the wrong terminal, stop, one can find a violated cut.

Denote the instance obtained through re-pairing starting with terminal x by  $I_x$ , and its requirement set by  $R_x$ . We will only prove the following lemma.

**Lemma 4** The cut condition holds for the original instance I if and only if it holds for any re-paired instance  $I_x$ .

**Proof:** For necessity, let S be a violated cut for some instance  $I_x$ . Recall that the number of edges is  $\delta_E(S)$  is unchanged, so we evaluate  $\delta_R(S)$  and  $\delta_{R_x}(S)$ .

W.l.o.g. we can assume that  $x \notin S$ , and S contains consecutive nodes of V(C). Then, the terminal pairs in S represent a consecutive set of paranthesis in the string obtained at step 1.b). Since the parenthesis are correctly nested, the set of parenthesis corresponding

to demand pairs crossing S consists of  $k' \geq 0$  unmatched closing parenthesis, followed by a  $k'' \geq 0$  unmatched opening parenthesis;  $k' + k'' = \delta_{R_r}(S)$ .

Let S', S'' be the terminals in S before and including the last unmatched ")", and in S after the last unmatched ")", respectively. Then, S' contains k' more ")" than "(", thus there are k' pairs in R crossing it, and since in R every ")" is preceded by its ")", these pairs also cross S. Similarly, S' contains k'' more "(" than ")", thus there are k'' more pairs in R crossing S. Hence  $\delta_R(S) \geq \delta_{R_r}(S) > \delta_E(S)$ .

Conversely, to see sufficiency, let S be a cut violated w.r.t R. Choose x to be the first vertex in S. Then, every pair in R that crosses S will have an opening parenthesis, but not a closing one associated to it. As a result, S will contain  $\delta_R(S)$  more "(" than ")" in it, and thus  $\delta_{R_x}(S) \geq \delta_R(S) > \delta_E(S)$ .

A successful run of the algorithm is illustrated in figures 4–7; an unsuccessful run, together with the violating cut is illustrated in figures 8–11. For the latter, the re-pairing is:

| Original demand pair | 3  | 2  | 1  | 4  | 3  | 2  | 1  | 4  |
|----------------------|----|----|----|----|----|----|----|----|
| Parenthesis          | (  | (  | (  | (  | )  | )  | )  | )  |
| New demand pair      | 4' | 3' | 2' | 1' | 1' | 2' | 3' | 4' |

A violated cut can be obtained by using the path that got stuck or arrived at the wrong destination, and is illustrated in Figure 12.

## References

- [OS81] Haruko Okamura and P. D. Seymour. Multicommodity flows in planar graphs. J. Combin. Theory Ser. B, 31(1):75–81, 1981.
- [RLWW95] Heike Ripphausen-Lipa, Dorothea Wagner, and Karsten Weihe. Efficient algorithms for disjoint paths in planar graphs. In *Combinatorial optimization* (New Brunswick, NJ, 1992–1993), volume 20 of DIMACS Ser. Discrete Math. Theoret. Comput. Sci., pages 295–354. Amer. Math. Soc., Providence, RI, 1995.
- [Sch03] Alexander Schrijver. Combinatorial optimization. Polyhedra and efficiency. Vol. C, volume 24 of Algorithms and Combinatorics. Springer-Verlag, Berlin, 2003. Disjoint paths, hypergraphs, Chapters 70–83.
- [WW93] Dorothea Wagner and Karsten Weihe. A linear-time algorithm for edge-disjoint paths in planar graphs. In *Algorithms—ESA '93 (Bad Honnef, 1993)*, volume 726 of *Lecture Notes in Comput. Sci.*, pages 384–395. Springer, Berlin, 1993.
- [WW95] Dorothea Wagner and Karsten Weihe. A linear-time algorithm for edge-disjoint paths in planar graphs. *Combinatorica*, 15(1):135–150, 1995.

Figure 4: Initial graph for the Wagner-Weihe algorithm, together with the terminal pairs resulting from re-pairing. We will illustrate a successful run of the algorithm on this graph.

Figure 5: The results of the "right-first search" w.r.t. the re-paired terminals. Path between different terminal pairs are styled differently. Plain undirected edges are unused.

Figure 6: The resulting directed graph with the unused edges deleted.

Figure 7: The results of "right-first search" w.r.t. the original terminal pairs. This is also a solution to the original disjoint paths problem. Edges not used in the final solution are omitted.

Figure 8: Initial graph for the Wagner-Weihe algorithm, together with the terminal pairs resulting from re-pairing. We will illustrate an unsuccessful run of the algorithm on this graph.

Figure 9: The results of the "right-first search" w.r.t. the re-paired terminals. Path between different terminal pairs are styled differently. Plain undirected edges are unused.

Figure 10: The resulting directed graph with the unused edges deleted.

Figure 11: The results of "right-first search" w.r.t. the original terminal pairs. Note that path from source 1 arrives at 4 instead of destination 1, disconnects the graph into two parts, and thus defines a cut. Edges not used in the drawn paths are omitted.

Figure 12: The path from the previous figure results in the following violated cut, with  $\delta_R(S)=4>\delta_E(S)=2.$
