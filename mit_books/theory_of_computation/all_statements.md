# All Mathematical Statements: Theory of Computation

## Statement 1
**Theorem (Closure under Union).** If $A_1$, $A_2$ are regular languages, so is $A_1 \cup A_2$.
(Line 195)

## Statement 2
**Theorem (Closure under Concatenation).** If $A_1$, $A_2$ are regular languages, so is $A_1A_2$.
(Line 228)

## Statement 3
**Theorem (Closure under Concatenation, restated).** If $A_1, A_2$ are regular languages, so is $A_1A_2$ (closure under $\circ$).
(Line 298, 401)

## Statement 4
**Theorem (NFA to Regular).** If an NFA recognizes A then A is regular.
(Line 361)

## Statement 5
**Theorem (Closure under Star).** If A is a regular language, so is $A^*$.
(Line 415)

## Statement 6
**Theorem (Regular Expressions to NFA).** If R is a regular expression and A = L(R) then A is regular.
(Line 433)

## Statement 7
**Theorem (DFA to Regular Expressions).** If A is regular then A = L(R) for some regular expression R.
(Line 522)

## Statement 8
**Lemma (GNFA to Regular Expressions).** Every GNFA G has an equivalent regular expression R.
(Line 543)

## Statement 9
**Pumping Lemma (for Regular Languages).** For every regular language A, there is a number p (the "pumping length") such that if $s \in A$ and $|s| \ge p$ then s = xyz where 1) $xy^iz \in A$ for all $i \ge 0$, 2) $y \neq \epsilon$, 3) $|xy| \leq p$.
(Line 602)

## Statement 10
**Theorem (CFG to PDA).** If A is a CFL then some PDA recognizes A.
(Line 907, 927)

## Statement 11
**Theorem (Equivalence of CFGs and PDAs).** A is a CFL iff some PDA recognizes A.
(Line 949)

## Statement 12
**Corollary.** 1) Every regular language is a CFL. 2) If A is a CFL and B is regular then $A \cap B$ is a CFL.
(Line 1010-1013)

## Statement 13
**Pumping Lemma for CFLs.** For every CFL A, there is a p such that if $s \in A$ and $|s| \ge p$ then s = uvxyz where 1) $uv^ixy^iz \in A$ for all $i \ge 0$, 2) $vy \neq \varepsilon$, 3) $|vxy| \le p$.
(Line 1029)

## Statement 14
**Theorem (Multi-tape TMs).** A is T-recognizable iff some multi-tape TM recognizes A.
(Line 1264)

## Statement 15
**Theorem (Nondeterministic TMs).** A is T-recognizable iff some NTM recognizes A.
(Line 1282)

## Statement 16
**Theorem (Turing Enumerators).** A is T-recognizable iff A = L(E) for some T-enumerator E.
(Line 1306)

## Statement 17
**Theorem ($A_{DFA}$ is decidable).** $A_{DFA} = \{\langle B, w \rangle | B \text{ is a DFA and } B \text{ accepts } w\}$ is decidable.
(Line 1488)

## Statement 18
**Theorem ($A_{NFA}$ is decidable).** $A_{NFA} = \{\langle B, w \rangle | B \text{ is a NFA and } B \text{ accepts } w\}$ is decidable.
(Line 1507)

## Statement 19
**Theorem ($E_{DFA}$ is decidable).** $E_{DFA} = \{\langle B \rangle | B \text{ is a DFA and } L(B) = \emptyset \}$ is decidable.
(Line 1523)

## Statement 20
**Theorem ($EQ_{DFA}$ is decidable).** $EQ_{DFA} = \{\langle A, B \rangle | A \text{ and } B \text{ are DFAs and } L(A) = L(B) \}$ is decidable.
(Line 1539)

## Statement 21
**Theorem ($A_{CFG}$ is decidable).** $A_{CFG} = \{\langle G, w \rangle | G \text{ is a CFG and } w \in L(G)\}$ is decidable.
(Line 1557)

## Statement 22
**Lemma 1.** Can convert every CFG into Chomsky Normal Form (CNF).
(Line 1581)

## Statement 23
**Lemma 2.** If H is in CNF and $w \in L(H)$ then every derivation of w has 2|w|-1 steps.
(Line 1583)

## Statement 24
**Theorem ($E_{CFG}$ is decidable).** $E_{CFG} = \{\langle G \rangle | G \text{ is a CFG and } L(G) = \emptyset \}$ is decidable.
(Line 1591)

## Statement 25
**Theorem ($EQ_{CFG}$ is NOT decidable).** $EQ_{CFG} = \{\langle G, H \rangle | G, H \text{ are CFGs and } L(G) = L(H) \}$ is NOT decidable.
(Line 1611)

## Statement 26
**Theorem ($A_{TM}$ is not decidable).** $A_{TM} = \{\langle M, w \rangle | M \text{ is a TM and } M \text{ accepts } w\}$ is not decidable.
(Line 1629)

## Statement 27
**Theorem ($A_{TM}$ is T-recognizable).** $A_{TM}$ is T-recognizable.
(Line 1633)

## Statement 28
**Theorem ($\mathbb{R}$ is uncountable).** $\mathbb{R}$ is uncountable.
(Line 1740)

## Statement 29
**Corollary 1.** $\mathcal{L}$ (all languages) is uncountable.
(Line 1772)

## Statement 30
**Corollary 2.** Some language is not decidable.
(Line 1780)

## Statement 31
**Theorem ($A_{TM}$ is not decidable, restated).** $A_{TM}$ is not decidable.
(Line 1797)

## Statement 32
**Theorem (Recognizable and co-recognizable implies decidable).** If A and $\overline{A}$ are T-recognizable then A is decidable.
(Line 1834)

## Statement 33
**Corollary.** $\overline{A_{TM}}$ is T-unrecognizable.
(Line 1845)

## Statement 34
**Theorem ($HALT_{TM}$ is undecidable).** $HALT_{TM} = \{\langle M, w \rangle | M \text{ halts on input } w \}$ is undecidable.
(Line 1867)

## Statement 35
**Theorem ($E_{TM}$ is undecidable).** $E_{TM} = \{ \langle M \rangle | M \text{ is a TM and } L(M) = \emptyset \}$ is undecidable.
(Line 1968)

## Statement 36
**Theorem (Mapping reducibility and decidability).** If $A \leq_m B$ and B is decidable then so is A.
(Line 2015)

## Statement 37
**Corollary.** If $A \leq_m B$ and A is undecidable then so is B.
(Line 2025)

## Statement 38
**Theorem (Mapping reducibility and T-recognizability).** If $A \leq_m B$ and B is T-recognizable then so is A.
(Line 2027)

## Statement 39
**Corollary.** If $A \leq_m B$ and A is T-unrecognizable then so is B.
(Line 2031)

## Statement 40
**Theorem ($E_{TM}$ is T-unrecognizable).** $E_{TM}$ is T-unrecognizable.
(Line 2095)

## Statement 41
**Theorem ($EQ_{TM}$ and $\overline{EQ_{TM}}$ are T-unrecognizable).** Both $EQ_{TM}$ and $\overline{EQ_{TM}}$ are T-unrecognizable.
(Line 2117)

## Statement 42
**Theorem (Hilbert's 10th, 1971).** $D = \{\langle p \rangle | \text{ polynomial } p(x_1, x_2, \dots, x_k) = 0 \text{ has integer solution} \}$ is not decidable.
(Line 2184)

## Statement 43
**Theorem ($A_{LBA}$ is decidable).** $A_{LBA} = \{\langle B, w \rangle | LBA B \text{ accepts } w \}$ is decidable.
(Line 2261)

## Statement 44
**Theorem ($E_{LBA}$ is undecidable).** $E_{LBA} = \{\langle B \rangle | B \text{ is an LBA and } L(B) = \emptyset \}$ is undecidable.
(Line 2284)

## Statement 45
**Theorem (PCP is undecidable).** PCP is undecidable.
(Line 2317)

## Statement 46
**Theorem ($ALL_{CFG}$ is undecidable).** $ALL_{CFG} = \{\langle G \rangle | G \text{ is a CFG and } L(G) = \Sigma^* \}$ is undecidable.
(Line 2367)

## Statement 47
**Theorem (Self-Reproducing TM).** There is a TM SELF which (on any input) halts with $\langle SELF \rangle$ on the tape.
(Line 2493)

## Statement 48
**Lemma (Computable function q).** There is a computable function $q: \Sigma^* \to \Sigma^*$ such that $q(w) = \langle P_w \rangle$ for every w, where $P_w$ is the TM that prints w on the tape and halts.
(Line 2495)

## Statement 49
**Theorem (Recursion Theorem).** For any TM T there is a TM R where for all w, R on input w operates in the same way as T on input $\langle w, R \rangle$.
(Line 2528)

## Statement 50
**Theorem ($A_{TM}$ is undecidable, new proof).** $A_{TM}$ is not decidable.
(Line 2552)

## Statement 51
**Theorem (Fixed-point Theorem).** For any computable function $f: \Sigma^* \to \Sigma^*$, there is a TM R such that L(R) = L(S) where $f(\langle R \rangle) = \langle S \rangle$.
(Line 2567)

## Statement 52
**Theorem ($MIN_{TM}$ is T-unrecognizable).** $MIN_{TM} = \{\langle M \rangle | M \text{ is a minimal TM } \}$ is T-unrecognizable.
(Line 2588)

## Statement 53
**Theorem (Godel's First Incompleteness Theorem, informal).** In any reasonable formal system, some true statements are not provable.
(Line 2620-2622)

## Statement 54
**Theorem (True but unprovable statement).** (1) $\phi_U$ has no proof. (2) $\phi_U$ is true.
(Line 2652-2654)

## Statement 55
**Theorem ($A = \{a^k b^k | k \ge 0\}$ in $O(n^2)$ time).** A 1-tape TM M can decide A where, on inputs of length n, M uses at most $cn^2$ steps, for some fixed constant c.
(Line 2716)

## Statement 56
**Theorem ($A = \{a^k b^k | k \ge 0\}$ in $O(n \log n)$ time).** A 1-tape TM M can decide A by using $O(n \log n)$ steps.
(Line 2746)

## Statement 57
**Theorem (Lower bound for $A = \{a^k b^k | k \ge 0\}$).** A 1-tape TM M cannot decide A by using $o(n \log n)$ steps.
(Line 2773)

## Statement 58
**Theorem ($A = \{a^k b^k | k \ge 0\}$ in O(n) time on multi-tape).** A multi-tape TM M can decide A using O(n) steps.
(Line 2779)

## Statement 59
**Theorem (Multi-tape to 1-tape time).** Let $t(n) \ge n$. If a multi-tape TM decides B in time t(n), then $B \in TIME(t^2(n))$.
(Line 2845-2847)

## Statement 60
**Theorem ($PATH \in P$).** $PATH = \{\langle G, s, t \rangle | G \text{ is a directed graph with a path from } s \text{ to } t \}$ is in P.
(Line 2878)

## Statement 61
**Theorem ($HAMPATH \in NP$).** $HAMPATH \in NP$.
(Line 2995)

## Statement 62
**Theorem ($COMPOSITES \in NP$).** $COMPOSITES \in NP$.
(Line 3012)

## Statement 63
**Theorem ($COMPOSITES \in P$, 2002).** $COMPOSITES \in P$.
(Line 3023)

## Statement 64
**Theorem ($A_{CFG} \in NP$).** $A_{CFG} \in NP$.
(Line 3066)

## Statement 65
**Theorem ($A_{CFG} \in P$).** $A_{CFG} \in P$.
(Line 3075, 3098, 3126)

## Statement 66
**Theorem (Cook-Levin, 1971).** $SAT \in P \rightarrow P = NP$.
(Line 3154)

## Statement 67
**Theorem (Polynomial-time reducibility).** If $A \leq_P B$ and $B \in P$ then $A \in P$.
(Line 3169, 3207)

## Statement 68
**Theorem ($3SAT \leq_P CLIQUE$).** $3SAT \leq_P CLIQUE$.
(Line 3254)

## Statement 69
**Corollary.** $CLIQUE \in P \rightarrow 3SAT \in P$.
(Line 3273)

## Statement 70
**Cook-Levin Theorem.** SAT is NP-complete.
(Line 3295, 3398)

## Statement 71
**Theorem (HAMPATH is NP-complete).** HAMPATH is NP-complete.
(Line 3313)

## Statement 72
**Theorem (3SAT is NP-complete).** 3SAT is NP-complete.
(Line 3485)

## Statement 73
**Theorem (TIME and SPACE relationship).** For $t(n) \ge n$: 1) $TIME(t(n)) \subseteq SPACE(t(n))$, 2) $SPACE(t(n)) \subseteq TIME(2^{O(t(n))})$.
(Line 3561)

## Statement 74
**Corollary.** $P \subseteq PSPACE$.
(Line 3571)

## Statement 75
**Theorem.** $NP \subseteq PSPACE$.
(Line 3573, 3577)

## Statement 76
**Theorem ($TQBF \in PSPACE$).** $TQBF \in PSPACE$.
(Line 3614, 3627)

## Statement 77
**Theorem ($LADDER_{DFA} \in NPSPACE$).** $LADDER_{DFA} \in NPSPACE$.
(Line 3651, 3664)

## Statement 78
**Theorem ($LADDER_{DFA} \in PSPACE$).** $LADDER_{DFA} \in PSPACE$.
(Line 3683)

## Statement 79
**Theorem ($LADDER_{DFA} \in SPACE(n^2)$).** $LADDER_{DFA} \in SPACE(n^2)$.
(Line 3687, 3769)

## Statement 80
**Savitch's Theorem.** For $f(n) \ge n$, $NSPACE(f(n)) \subseteq SPACE(f^2(n))$.
(Line 3809)

## Statement 81
**Theorem (TQBF is PSPACE-complete).** TQBF is PSPACE-complete.
(Line 3862)

## Statement 82
**Theorem (GG is PSPACE-complete).** $GG = \{\langle G, a \rangle | \text{ Player I has a forced win in Generalized Geography on graph } G \text{ starting at node } a \}$ is PSPACE-complete.
(Line 4002, 4040)

## Statement 83
**Theorem ($L \subseteq P$).** $L \subseteq P$.
(Line 4090, 4177)

## Statement 84
**Theorem ($NL \subseteq SPACE(\log^2 n)$).** $NL \subseteq SPACE(\log^2 n)$.
(Line 4100, 4191)

## Statement 85
**Theorem ($NL \subseteq P$).** $NL \subseteq P$.
(Line 4106, 4203)

## Statement 86
**Theorem (Log-space reducibility).** If $A \leq_L B$ and $B \in L$ then $A \in L$.
(Line 4250)

## Statement 87
**Theorem (PATH is NL-complete).** PATH is NL-complete.
(Line 4261)

## Statement 88
**Theorem ($\overline{2SAT}$ is NL-complete).** $\overline{2SAT}$ is NL-complete.
(Line 4287)

## Statement 89
**Theorem (Immerman-Szelepcsényi).** NL = coNL.
(Line 4310, 4445)

## Statement 90
**Theorem (NL-machine computes c implies path).** If some NL-machine computes c, then some NL-machine computes path.
(Line 4347, 4482, 4500)

## Statement 91
**Theorem (NL-machine computes $c_d$ implies $path_d$).** If some NL-machine computes $c_d$, then some NL-machine computes $path_d$.
(Line 4369, 4517)

## Statement 92
**Theorem (NL-machine computes $c_d$ implies $path_{d+1}$).** If some NL-machine computes $c_d$, then some NL-machine computes $path_{d+1}$.
(Line 4385, 4535)

## Statement 93
**Corollary.** Some NL-machine computes $c_{d+1}$ from $c_d$.
(Line 4401, 4551)

## Statement 94
**Theorem (Space Hierarchy Theorem).** For any $f: \mathbb{N} \to \mathbb{N}$ (where f satisfies a technical condition), there is a language A where A requires O(f(n)) space, i.e., 1) A is decidable in O(f(n)) space, and 2) A is not decidable in o(f(n)) space. In other words, $SPACE(o(f(n))) \subsetneq SPACE(f(n))$.
(Line 4584)

## Statement 95
**Theorem (Time Hierarchy Theorem).** For any $f: \mathbb{N} \to \mathbb{N}$ where f is time constructible, there is a language A where A requires O(f(n)) time, i.e., 1) A is decidable in O(f(n)) time, and 2) A is not decidable in $o(f(n)/\log(f(n)))$ time. In other words, $TIME(o(f(n)/\log(f(n)))) \subsetneq TIME(f(n))$.
(Line 4641)

## Statement 96
**Corollary.** NL $\subsetneq$ PSPACE.
(Line 4729)

## Statement 97
**Theorem (If B is EXPTIME-complete then $B \notin P$).** If B is EXPTIME-complete then $B \notin P$.
(Line 4759)

## Statement 98
**Theorem (If B is EXPSPACE-complete then $B \notin PSPACE$).** If B is EXPSPACE-complete then $B \notin PSPACE$ (and $B \notin P$).
(Line 4761)

## Statement 99
**Theorem ($EQ_{REX} \in PSPACE$).** $EQ_{REX} \in PSPACE$.
(Line 4769, 4952)

## Statement 100
**Theorem ($EQ_{REX\uparrow}$ is EXPSPACE-complete).** $EQ_{REX\uparrow} = \{\langle R_1, R_2 \rangle | R_1 \text{ and } R_2 \text{ are equivalent regular expressions with exponentiation} \}$ is EXPSPACE-complete.
(Line 4777, 4790)

## Statement 101
**Theorem (Oracle with $P^A = NP^A$).** There is an oracle A where $P^A = NP^A$.
(Line 4908)

## Statement 102
**Amplification Lemma.** If $M_1$ is a poly-time PTM with error $\epsilon_1 < 1/2$ then, for any $0 < \epsilon_2 < 1/2$, there is an equivalent poly-time PTM $M_2$ with error $\epsilon_2$.
(Line 5001)

## Statement 103
**Theorem ($EQ_{BP}$ is coNP-complete).** $EQ_{BP}$ is coNP-complete.
(Line 5040)

## Statement 104
**Theorem ($EQ_{ROBP} \in BPP$).** $EQ_{ROBP} \in BPP$.
(Line 5052, 5066, 5200)

## Statement 105
**Polynomial Lemma.** If $p(x) \neq 0$ is a polynomial of degree $\leq d$ then $p$ has $\leq d$ roots.
(Line 5264)

## Statement 106
**Corollary 1 (of Polynomial Lemma).** If $p_1(x)$ and $p_2(x)$ are both degree $\leq d$ and $p_1 \neq p_2$ then $p_1(a) = p_2(a)$ for $\leq d$ values $a$.
(Line 5266)

## Statement 107
**Corollary 2 (of Polynomial Lemma).** If $p(x) \neq 0$ has degree $\leq d$ and we pick a random $r \in \mathbb{F}_q$, then $\Pr[p(r) = 0] \leq d/q$.
(Line 5270)

## Statement 108
**Theorem (Schwartz-Zippel).** If $p(x_1,...,x_m) \neq 0$ has degree $\leq d$ in each $x_i$ and we pick random $r_1,...,r_m \in \mathbb{F}_q$ then $\Pr[p(r_1,...,r_m)=0] \leq md/q$.
(Line 5272)

## Statement 109
**Theorem ($\overline{ISO} \in IP$).** $\overline{ISO} \in IP$.
(Line 5467)

## Statement 110
**Theorem (IP = PSPACE).** IP = PSPACE.
(Line 5495, 5644)

## Statement 111
**Theorem (#SAT is coNP-hard).** #SAT is coNP-hard.
(Line 5511)

## Statement 112
**Theorem ($\#SAT \in IP$).** $\#SAT \in IP$.
(Line 5523, 5654)
