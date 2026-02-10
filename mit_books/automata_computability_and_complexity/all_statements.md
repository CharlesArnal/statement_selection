# All Extracted Statements

## Statement 1: Definition (Deterministic Finite Automaton / DFA)
A DFA is a 5-tuple (Q, Sigma, delta, q0, F) where Q is a finite set of states, Sigma is a finite input alphabet, delta: Q x Sigma -> Q is a transition function, q0 in Q is the start state, and F subset of Q is the set of accept states.

## Statement 2: Definition (Language of a DFA)
The language recognized by a DFA M, denoted L(M), is the set of strings that M accepts: L(M) = { w in Sigma* | M accepts w }.

## Statement 3: Definition (Regular Language)
A language is regular if some DFA recognizes it.

## Statement 4: Theorem (Closure of Regular Languages under Union)
The class of regular languages is closed under union. If A1 and A2 are regular languages, then A1 union A2 is also regular.

## Statement 5: Theorem (Closure of Regular Languages under Intersection)
The class of regular languages is closed under intersection. If A1 and A2 are regular languages, then A1 intersect A2 is also regular.

## Statement 6: Theorem (Closure of Regular Languages under Complement)
The class of regular languages is closed under complement. If A is a regular language, then the complement of A is also regular.

## Statement 7: Definition (Nondeterministic Finite Automaton / NFA)
An NFA is a 5-tuple (Q, Sigma, delta, q0, F) where Q is a finite set of states, Sigma is a finite alphabet, delta: Q x (Sigma union {epsilon}) -> P(Q) is a transition function, q0 in Q is the start state, and F subset of Q is the set of accept states.

## Statement 8: Theorem (Equivalence of NFAs and DFAs)
Every NFA has an equivalent DFA. That is, a language is recognized by some NFA if and only if it is recognized by some DFA.

## Statement 9: Theorem (Closure of Regular Languages under Concatenation)
The class of regular languages is closed under concatenation.

## Statement 10: Theorem (Closure of Regular Languages under Kleene Star)
The class of regular languages is closed under the star operation.

## Statement 11: Definition (Regular Expressions)
A regular expression R is defined inductively: a (for a in Sigma), epsilon, empty set, R1 union R2, R1 circ R2, R1*.

## Statement 12: Theorem (Equivalence of Regular Expressions and Regular Languages)
A language is regular if and only if some regular expression describes it.

## Statement 13: Theorem (Pumping Lemma for Regular Languages)
If A is a regular language, then there is a number p (the pumping length) where, if s is any string in A of length at least p, then s may be divided into three pieces s = xyz, satisfying: (1) for each i >= 0, xy^i z is in A, (2) |y| > 0, (3) |xy| <= p.

## Statement 14: Theorem (0^n 1^n is not regular)
The language B = {0^n 1^n | n >= 0} is not regular.

## Statement 15: Definition (Context-Free Grammar / CFG)
A context-free grammar is a 4-tuple (V, Sigma, R, S) where V is a finite set of variables, Sigma is a finite set of terminals (alphabet), R is a set of production rules, and S in V is the start variable.

## Statement 16: Definition (Context-Free Language)
A language is context-free if and only if some context-free grammar generates it.

## Statement 17: Definition (Pushdown Automaton / PDA)
A PDA is a 6-tuple (Q, Sigma, Gamma, delta, q0, F) where Q is a finite set of states, Sigma is the input alphabet, Gamma is the stack alphabet, delta: Q x (Sigma union {epsilon}) x (Gamma union {epsilon}) -> P(Q x (Gamma union {epsilon})) is the transition function, q0 in Q is the start state, and F subset of Q is the set of accept states.

## Statement 18: Theorem (Equivalence of CFGs and PDAs)
A language is context-free if and only if some pushdown automaton recognizes it.

## Statement 19: Theorem (Every regular language is context-free)
Every regular language is context-free.

## Statement 20: Theorem (Pumping Lemma for Context-Free Languages)
If A is a context-free language, then there is a number p where, if s is any string in A of length at least p, then s may be divided into five pieces s = uvxyz, satisfying: (1) for each i >= 0, uv^i xy^i z is in A, (2) |vy| > 0, (3) |vxy| <= p.

## Statement 21: Definition (Turing Machine)
A Turing machine is a 7-tuple (Q, Sigma, Gamma, delta, q0, q_accept, q_reject) where Q is a finite set of states, Sigma is the input alphabet (not containing blank), Gamma is the tape alphabet (containing blank and Sigma), delta: Q x Gamma -> Q x Gamma x {L, R} is the transition function, q0 is the start state, q_accept is the accept state, q_reject is the reject state (q_reject != q_accept).

## Statement 22: Definition (Turing-recognizable / recursively enumerable)
A language is Turing-recognizable if some Turing machine recognizes it.

## Statement 23: Definition (Decidable / Turing-decidable)
A language is decidable if some Turing machine decides it (halts on all inputs, accepting or rejecting).

## Statement 24: Theorem (Every decidable language is Turing-recognizable)
Every decidable language is Turing-recognizable.

## Statement 25: Theorem (Multi-tape TM equivalence)
Every multi-tape Turing machine has an equivalent single-tape Turing machine.

## Statement 26: Theorem (Nondeterministic TM equivalence)
Every nondeterministic Turing machine has an equivalent deterministic Turing machine.

## Statement 27: Definition (Enumerator)
An enumerator is a Turing machine with an attached printer that prints strings from Sigma*.

## Statement 28: Theorem (Enumerator characterization of Turing-recognizable)
A language is Turing-recognizable if and only if some enumerator enumerates it.

## Statement 29: Church-Turing Thesis
The informal notion of algorithm is equivalent to the formal notion of a Turing machine (or any equivalent model). This is a thesis, not a theorem.

## Statement 30: Definition (A_TM - Acceptance problem for TMs)
A_TM = { <M, w> | M is a TM and M accepts w }.

## Statement 31: Theorem (A_TM is Turing-recognizable)
A_TM is Turing-recognizable (via the universal TM).

## Statement 32: Theorem (A_TM is undecidable)
A_TM is undecidable. There is no Turing machine that decides A_TM.

## Statement 33: Corollary (Some languages are not Turing-recognizable)
There exist languages that are not Turing-recognizable (by a counting/diagonalization argument).

## Statement 34: Theorem (Undecidability of the Halting Problem)
HALT_TM = { <M, w> | M is a TM and M halts on input w } is undecidable.

## Statement 35: Theorem (Undecidability of E_TM)
E_TM = { <M> | M is a TM and L(M) = empty } is undecidable.

## Statement 36: Theorem (Rice's Theorem)
For any nontrivial property P of Turing-recognizable languages, the problem of determining whether the language recognized by a given TM has property P is undecidable.

## Statement 37: Definition (Mapping Reducibility)
Language A is mapping reducible to language B, written A <=_m B, if there exists a computable function f: Sigma* -> Sigma* such that for every w, w in A if and only if f(w) in B.

## Statement 38: Theorem (Mapping reducibility and decidability)
If A <=_m B and B is decidable, then A is decidable.

## Statement 39: Theorem (Mapping reducibility and recognizability)
If A <=_m B and B is Turing-recognizable, then A is Turing-recognizable.

## Statement 40: Theorem (Complement of A_TM is not Turing-recognizable)
The complement of A_TM is not Turing-recognizable.

## Statement 41: Theorem (Decidable iff both L and complement are recognizable)
A language is decidable if and only if it is Turing-recognizable and co-Turing-recognizable.

## Statement 42: Definition (TIME(t(n)))
Let t: N -> R^{>=0}. TIME(t(n)) = { L | L is decided by some O(t(n))-time Turing machine }.

## Statement 43: Definition (The class P)
P = union_{k >= 0} TIME(n^k), the class of languages decidable in polynomial time by a deterministic Turing machine.

## Statement 44: Theorem (Polynomial-time reducibility and P)
If A <=_p B and B in P then A in P.

## Statement 45: Theorem (Transitivity of polynomial-time reducibility)
If A <=_p B and B <=_p C then A <=_p C.

## Statement 46: Theorem (Multi-tape to single-tape time simulation)
If t(n) >= n then every t(n)-time multi-tape TM has an equivalent O(t^2(n))-time single-tape TM.

## Statement 47: Theorem (Time hierarchy / diagonalization)
For any computable function t, there is a language that is decidable, but cannot be decided by any basic Turing machine in time t(n).

## Statement 48: Definition (NP)
NP = { L | there is some polynomial-time nondeterministic Turing machine that decides L }. Equivalently, L in NP iff there exist a polynomial-time verifier V and polynomial p such that x in L iff (exists c, |c| <= p(|x|)) [V(x, c) accepts].

## Statement 49: Theorem (P is contained in NP)
P is a subset of NP.

## Statement 50: Definition (Polynomial-time reducibility)
A is polynomial-time reducible to B, A <=_p B, if there is a polynomial-time computable function f: Sigma* -> Sigma* such that for all w, w in A iff f(w) in B.

## Statement 51: Definition (NP-complete)
Language B is NP-complete if (a) B in NP, and (b) for any language A in NP, A <=_p B.

## Statement 52: Definition (NP-hard)
Language B is NP-hard if for any language A in NP, A <=_p B.

## Statement 53: Theorem (NP-complete language in P implies P = NP)
If some NP-complete language is in P, then P = NP.

## Statement 54: Theorem (Equivalence of P = NP conditions)
The following are equivalent: (1) P = NP. (2) Every NP-complete language is in P. (3) Some NP-complete language is in P.

## Statement 55: Theorem (SAT is NP-complete / Cook-Levin Theorem)
SAT = { <phi> | phi is a satisfiable Boolean formula } is NP-complete.

## Statement 56: Theorem (3SAT is NP-complete)
3SAT (the satisfiability problem restricted to 3-CNF formulas) is NP-complete.

## Statement 57: Theorem (CLIQUE is NP-complete)
CLIQUE = { <G, k> | G is a graph with a k-clique } is NP-complete.

## Statement 58: Theorem (VERTEX-COVER is NP-complete)
VERTEX-COVER = { <G, k> | G is a graph with a vertex cover of size k } is NP-complete.

## Statement 59: Theorem (CLIQUE <=_p VERTEX-COVER)
CLIQUE is polynomial-time reducible to VERTEX-COVER. Specifically, G has a k-clique iff G' (the complement graph) has a (n-k) vertex cover.

## Statement 60: Theorem (VERTEX-COVER <=_p CLIQUE)
VERTEX-COVER is polynomial-time reducible to CLIQUE.

## Statement 61: Theorem (If A <=_p B and B in NP then A in NP)
If A <=_p B and B in NP, then A in NP.

## Statement 62: Theorem (DHAMPATH is NP-complete)
DHAMPATH = { <G, s, t> | G is a directed graph with a Hamiltonian path from s to t } is NP-complete. Proved via 3SAT <=_p DHAMPATH.

## Statement 63: Theorem (UHAMPATH is NP-complete)
UHAMPATH = { <G, s, t> | G is an undirected graph with a Hamiltonian path from s to t } is NP-complete.

## Statement 64: Theorem (DHAMCIRCUIT is NP-complete)
DHAMCIRCUIT = { <G> | G is a directed graph with a Hamiltonian circuit } is NP-complete.

## Statement 65: Theorem (UHAMCIRCUIT is NP-complete)
UHAMCIRCUIT = { <G> | G is an undirected graph with a Hamiltonian circuit } is NP-complete.

## Statement 66: Theorem (TSP is NP-complete)
TSP = { <G, c, k> | G is a complete graph with cost function c and has a tour of total cost <= k } is NP-complete.

## Statement 67: Theorem (SUBSET-SUM is NP-complete)
SUBSET-SUM = { <S, t> | S is a multiset of naturals and t is expressible as the sum of some elements of S } is NP-complete.

## Statement 68: Theorem (PARTITION is NP-complete)
PARTITION = { <S> | S is a multiset of naturals that can be split into two multisets with equal sums } is NP-complete.

## Statement 69: Theorem (MULTIPROCESSOR SCHEDULING is NP-complete)
MPS (the multiprocessor scheduling problem) is NP-complete, via PARTITION <=_p MPS.

## Statement 70: Conjecture (P = BPP)
Every randomized algorithm can be simulated by a deterministic algorithm with at most polynomial slowdown. Formally, P = BPP.

## Statement 71: Definition (Cryptographic Pseudorandom Generator / CPRG)
A CPRG (Yao 1982) is a function f: {0,1}^n -> {0,1}^{n+1} such that (1) f is computable in polynomial time, and (2) for all polynomial-time algorithms A, |Pr_{y}[A(y) accepts] - Pr_{x}[A(f(x)) accepts]| is negligibly small.

## Statement 72: Definition (One-Way Function)
A one-way function is a function f: {0,1}^n -> {0,1}^{p(n)} such that (1) f is computable in polynomial time, and (2) Pr_{x}[f(A(f(x))) = f(x)] is negligible for all polynomial-time algorithms A.

## Statement 73: Claim (CPRG implies OWF)
Any CPRG is also a OWF.

## Statement 74: Theorem (OWF iff CPRG / Hastad-Impagliazzo-Levin-Luby)
One-way functions exist if and only if cryptographic pseudorandom generators exist.

## Statement 75: Claim (Enhanced one-time pad security)
With a CPRG-based one-time pad construction, no polynomial-time adversary can recover the plaintext from the ciphertext.

## Statement 76: Euler's Formula (used in RSA)
For N = pq with p, q prime: x^{(p-1)(q-1)} = 1 mod N, for x relatively prime to N. This is because (p-1)(q-1) is the order of the multiplicative group mod N.

## Statement 77: Definition (BPP)
Language L is in BPP (Bounded-error Probabilistic Polynomial time) if there is a probabilistic polynomial-time TM that decides L with error probability 1/3.

## Statement 78: Definition (RP)
Language L is in RP (Random Polynomial time) if there is a probabilistic polynomial-time TM that decides L, where: w in L implies Pr[M accepts w] >= 1/2, and w not in L implies Pr[M rejects w] = 1.

## Statement 79: Lemma (BPP Amplification Lemma)
Suppose M is a PPT-TM that decides L with error probability epsilon, where 0 <= epsilon < 1/2. Then for any epsilon', 0 <= epsilon' < 1/2, there exists M', another PPT-TM, that decides L with error probability epsilon'.

## Statement 80: Theorem (Characterization of BPP)
L in BPP if and only if, for some epsilon with 0 <= epsilon < 1/2, there is a PPT-TM that decides L with error probability epsilon.

## Statement 81: Lemma (RP Amplification Lemma)
Suppose M is a PPT-TM that decides L with 0 <= epsilon < 1, w in L implies Pr[M accepts w] >= 1 - epsilon, w not in L implies Pr[M rejects w] = 1. Then for any epsilon' with 0 <= epsilon' < 1, there exists M' with the same properties but error epsilon'.

## Statement 82: Theorem (RP is contained in BPP)
RP is a subset of BPP.

## Statement 83: Definition (coRP)
coRP = { L | L^c in RP }.

## Statement 84: Theorem (coRP is contained in BPP)
coRP is a subset of BPP.

## Statement 85: Theorem (Fermat's Little Theorem)
If n is prime and a in Z_n^+ then a^{n-1} = 1 mod n.

## Statement 86: Fact (Non-Carmichael composites fail Fermat test)
Any non-Carmichael composite number fails at least half of all Fermat tests.

## Statement 87: Fact (Carmichael numbers have nontrivial square roots of 1)
For every Carmichael composite n, there is some b != 1, -1 such that b^2 = 1 mod n. No prime has such a nontrivial square root.

## Statement 88: Theorem (Miller-Rabin primality test correctness)
The Miller-Rabin primality testing algorithm satisfies: n in PRIMES implies Pr[accepts n] = 1; n not in PRIMES implies Pr[accepts n] <= 1/2.

## Statement 89: Theorem (PRIMES in coRP)
PRIMES is in coRP.

## Statement 90: Corollary (COMPOSITES in RP)
COMPOSITES is in RP.

## Statement 91: Corollary (PRIMES and COMPOSITES in BPP)
Both PRIMES and COMPOSITES are in BPP.

## Statement 92: Theorem (EQ_BP in coRP)
EQ_BP = { <B1, B2> | B1 and B2 are branching programs computing the same Boolean function } is in coRP (and hence in BPP).

## Statement 93: Theorem (RP contained in NP, coRP contained in coNP)
From the definitions, RP is a subset of NP and coRP is a subset of coNP.

## Statement 94: Theorem (Valiant's PAC Learning Bound)
m >= (1/epsilon) log(|C|/delta) samples suffice for (epsilon, delta)-PAC learning of a finite concept class C.

## Statement 95: Theorem (Blumer et al. VC-dimension Learning Bound)
m = O((1/epsilon) VCdim(C) log(1/(delta * epsilon))) samples suffice for PAC learning when the concept class C has finite VC-dimension.

## Statement 96: Theorem (IP = PSPACE)
IP (the class of languages with interactive proofs) equals PSPACE (the class of languages solvable with polynomial space). Proved by Shamir in 1990.

## Statement 97: Theorem (U is unitary iff UU* = I)
A matrix U is unitary if and only if UU* = I, where U* is the conjugate transpose. Equivalently, U^{-1} = U*.

## Statement 98: Theorem (No-Cloning Theorem)
It is impossible to duplicate an arbitrary quantum state. Cloning is not a unitary (linear) operation: alpha|0> + beta|1> cannot be mapped to (alpha|0> + beta|1>)(alpha|0> + beta|1>).

## Statement 99: Definition (BQP)
BQP (Bounded-Error Quantum Polynomial Time) is the class of decision problems solvable by polynomial-size quantum circuits with error probability at most 1/3.

## Statement 100: Theorem (P contained in BQP)
P is a subset of BQP.

## Statement 101: Theorem (BPP contained in BQP)
BPP is a subset of BQP.

## Statement 102: Theorem (BQP contained in EXP)
BQP is a subset of EXP.

## Statement 103: Theorem (BQP contained in PSPACE)
BQP is a subset of PSPACE (shown by Bernstein and Vazirani).

## Statement 104: Theorem (If A in P and B nontrivial then A <=_p B)
If A in P and B is any nontrivial language (not empty, not Sigma*), then A <=_p B.
