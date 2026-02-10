# Detailed Assessment: Theory of Computation

## Statement 1: Closure under Union (regular languages)
**Assessment: included**
Mathlib formalizes DFA closure under union via the product construction. The theorem `Language.IsRegular.add` proves that if `L1` and `L2` are regular, then `L1 + L2` (their union) is regular. The DFA-level construction is `DFA.union` with correctness given by `DFA.accepts_union`.
**Mathlib references**: `Mathlib/Computability/DFA.lean` -- `def union`, `theorem accepts_union`, `theorem IsRegular.add`

## Statement 2: Closure under Concatenation (regular languages)
**Assessment: non-included**
While the `Language` type supports multiplication (concatenation) and `RegularExpression` supports composition (`comp`), there is no proof in mathlib that the class of regular languages (as recognized by DFAs/NFAs with `IsRegular`) is closed under concatenation. Searched for `IsRegular.*mul`, `IsRegular.*concat`, `concat.*Regular` in `Mathlib/Computability/` with no results. The `DFA.lean` file defines union, intersection, and complement closure but not concatenation closure.
**Searched**: `DFA.lean`, `NFA.lean`, `Language.lean`, `RegularExpressions.lean`

## Statement 3: Closure under Concatenation (restated)
**Assessment: non-included**
Same as Statement 2. Mathlib lacks a proof that regular languages are closed under concatenation. The concatenation operation on `Language` is defined (as `mul` in the monoid structure), but the closure property for regular languages is not established.
**Searched**: `DFA.lean`, `NFA.lean`, `Language.lean`

## Statement 4: NFA to Regular (NFA recognizes A implies A is regular)
**Assessment: included**
The subset construction from NFA to DFA is formalized as `NFA.toDFA`, and correctness is proved in `NFA.toDFA_correct : M.toDFA.accepts = M.accepts`. Since `IsRegular` is defined as existence of a finite-state DFA, this effectively proves that NFA-recognizable implies regular.
**Mathlib references**: `Mathlib/Computability/NFA.lean` -- `def toDFA`, `theorem toDFA_correct`

## Statement 5: Closure under Star (regular languages)
**Assessment: non-included**
Kleene star is defined for languages (`Language.kstar`) and for regular expressions (`RegularExpression.star`), but there is no proof that `IsRegular` is closed under Kleene star. Searched for `IsRegular.*star`, `IsRegular.*kstar`, `star.*IsRegular` in `Mathlib/Computability/` with no results.
**Searched**: `DFA.lean`, `NFA.lean`, `Language.lean`, `RegularExpressions.lean`

## Statement 6: Regular Expressions to NFA (regex implies regular)
**Assessment: non-included**
Mathlib defines `RegularExpression` and its semantics (`matches'`), and proves a computable decision procedure (`rmatch_iff_matches'`). However, there is no explicit construction converting a regular expression to an NFA or DFA, and no proof that `matches'` of a regex is `IsRegular`. The file `RegularExpressions.lean` explicitly states in a comment: "Currently, we don't show that regular expressions and DFA/NFA's are equivalent."
**Searched**: `RegularExpressions.lean` (line 20)

## Statement 7: DFA to Regular Expressions (regular implies regex)
**Assessment: non-included**
There is no construction in mathlib converting a DFA to a regular expression. The equivalence between DFAs/NFAs and regular expressions is not formalized. See the comment in `RegularExpressions.lean` line 20.
**Searched**: `RegularExpressions.lean`, `DFA.lean`, `NFA.lean`

## Statement 8: GNFA to Regular Expressions
**Assessment: non-included**
There is no formalization of GNFAs (Generalized Nondeterministic Finite Automata) in mathlib. Searched for `GNFA`, `gnfa`, `generalized` in `Mathlib/Computability/` with no results.
**Searched**: `Mathlib/Computability/` directory

## Statement 9: Pumping Lemma (regular languages)
**Assessment: included**
The pumping lemma for regular languages is formalized for DFAs, NFAs, and epsilon-NFAs. `DFA.pumping_lemma` states that for a DFA with finitely many states, any accepted word longer than the number of states can be decomposed as `a ++ b ++ c` with `|ab| <= card sigma`, `b` nonempty, and `{a} * {b}* * {c} <= M.accepts`. NFA and epsilon-NFA versions lift this result.
**Mathlib references**: `Mathlib/Computability/DFA.lean` -- `theorem pumping_lemma`; `Mathlib/Computability/NFA.lean` -- `theorem pumping_lemma`; `Mathlib/Computability/EpsilonNFA.lean` -- `theorem pumping_lemma`

## Statement 10: CFG to PDA (CFL implies PDA recognizes)
**Assessment: non-included**
Mathlib defines `ContextFreeGrammar` and `ContextFreeRule` with basic derivation theory, but does not define pushdown automata (PDA) at all. Searched for `PDA`, `pushdown`, `Pushdown` in `Mathlib/Computability/` with no results.
**Searched**: `Mathlib/Computability/` directory

## Statement 11: Equivalence of CFGs and PDAs
**Assessment: non-included**
No PDA definition exists in mathlib. Only CFG definitions and basic properties are available. The equivalence between CFGs and PDAs is not formalized.
**Searched**: `Mathlib/Computability/ContextFreeGrammar.lean`, `Mathlib/Computability/` directory

## Statement 12: Every regular language is CFL; CFL intersect regular is CFL
**Assessment: non-included**
Mathlib defines `Language.IsContextFree` (existence of a CFG generating the language) but does not prove that every regular language is context-free or that the intersection of a CFL with a regular language is context-free. The CFG formalization is basic -- only definitions, derivation properties, and closure under reversal.
**Searched**: `Mathlib/Computability/ContextFreeGrammar.lean`

## Statement 13: Pumping Lemma for CFLs
**Assessment: non-included**
There is no pumping lemma for context-free languages in mathlib. The pumping lemma is only formalized for regular languages (via DFA/NFA). Searched for `pumping` and `Pumping` in `Mathlib/Computability/` -- only found results in DFA.lean, NFA.lean, and EpsilonNFA.lean.
**Searched**: `Mathlib/Computability/` directory

## Statement 14: Multi-tape TMs equivalent to single-tape
**Assessment: non-included**
Mathlib defines TM2 (multi-stack model) and TM1 (single-tape model) and provides a simulation of TM2 in TM1 (`TM2to1.tr` with `tr_respects` and `tr_eval_dom`). However, this proves TM2-computable implies TM1-computable, not the full equivalence statement about recognizability. The simulation does not address time complexity (the quadratic blowup). Furthermore, these are multi-stack rather than multi-tape models. The statement about recognizability equivalence is not explicitly stated in the textbook's form.
**Searched**: `Mathlib/Computability/TuringMachine.lean` -- `TM2to1` section

## Statement 15: Nondeterministic TMs equivalent to deterministic
**Assessment: non-included**
Mathlib does not formalize nondeterministic Turing machines as a separate model. The TM0, TM1, and TM2 models are all deterministic. No NTM definition or NTM-to-DTM simulation is present.
**Searched**: `Mathlib/Computability/TuringMachine.lean`, `Mathlib/Computability/PostTuringMachine.lean`

## Statement 16: Turing Enumerators equivalence
**Assessment: non-included**
No formalization of Turing enumerators exists in mathlib. Searched for `enumerator`, `Enumerator` in `Mathlib/Computability/` with no results.
**Searched**: `Mathlib/Computability/` directory

## Statement 17: A_DFA is decidable
**Assessment: non-included**
While DFA acceptance is clearly computable (the `DFA.eval` function is a `List.foldl` which terminates), mathlib does not formalize the meta-level statement "the problem of deciding whether a given DFA accepts a given string is decidable" in the sense of the textbook (as a decidable language about encoded DFA descriptions). The `DFA.mem_accepts` is a characterization, not a decidability result about encoded DFAs.
**Searched**: `Mathlib/Computability/DFA.lean`

## Statement 18: A_NFA is decidable
**Assessment: non-included**
Same situation as Statement 17. NFA evaluation is computable via the subset construction, but the meta-level decidability of the acceptance problem for encoded NFAs is not formalized.
**Searched**: `Mathlib/Computability/NFA.lean`

## Statement 19: E_DFA is decidable
**Assessment: non-included**
The emptiness problem for DFAs is not formalized in mathlib. No theorem about deciding whether a DFA's language is empty was found.
**Searched**: `Mathlib/Computability/DFA.lean`, `Mathlib/Computability/NFA.lean`

## Statement 20: EQ_DFA is decidable
**Assessment: non-included**
The equivalence problem for DFAs is not formalized in mathlib. No theorem about deciding whether two DFAs accept the same language was found.
**Searched**: `Mathlib/Computability/DFA.lean`

## Statement 21: A_CFG is decidable
**Assessment: non-included**
Mathlib does not prove that the membership problem for context-free grammars is decidable. The CFG formalization is limited to basic definitions and derivation properties.
**Searched**: `Mathlib/Computability/ContextFreeGrammar.lean`

## Statement 22: Chomsky Normal Form conversion
**Assessment: non-included**
No Chomsky Normal Form conversion is formalized in mathlib. Searched for `Chomsky`, `chomsky`, `CNF`, `normal form` in `Mathlib/Computability/` with no results.
**Searched**: `Mathlib/Computability/` directory

## Statement 23: CNF derivation length is 2|w|-1
**Assessment: non-included**
No CNF derivation analysis exists in mathlib.
**Searched**: `Mathlib/Computability/ContextFreeGrammar.lean`

## Statement 24: E_CFG is decidable
**Assessment: non-included**
The emptiness problem for CFGs is not formalized in mathlib.
**Searched**: `Mathlib/Computability/ContextFreeGrammar.lean`

## Statement 25: EQ_CFG is NOT decidable
**Assessment: non-included**
The undecidability of the equivalence problem for CFGs is not formalized in mathlib.
**Searched**: `Mathlib/Computability/ContextFreeGrammar.lean`, `Mathlib/Computability/Halting.lean`

## Statement 26: A_TM is not decidable
**Assessment: included**
Mathlib formalizes this as `Nat.Partrec.Code.halting_problem`, which states that the halting/acceptance problem for partial recursive functions is not computable: for any n, the predicate "does code c halt on input n" is not a `ComputablePred`. This is proved using Rice's theorem. The formalization works with `Nat.Partrec.Code` (a coding of partial recursive functions equivalent to Turing machines via `TMToPartrec`).
**Mathlib references**: `Mathlib/Computability/Halting.lean` -- `theorem halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom`

## Statement 27: A_TM is T-recognizable
**Assessment: included**
Mathlib proves that the halting predicate is recursively enumerable: `halting_problem_re (n) : REPred fun c => (eval c n).Dom`. The `REPred` predicate corresponds to Turing-recognizability (semi-decidability).
**Mathlib references**: `Mathlib/Computability/Halting.lean` -- `theorem halting_problem_re`

## Statement 28: R is uncountable
**Assessment: included**
Mathlib proves `Cardinal.not_countable_real : ¬(Set.univ : Set R).Countable` and the stronger `Cardinal.mk_real : #R = continuum` with `aleph0_lt_continuum`. This establishes that the reals are uncountable.
**Mathlib references**: `Mathlib/Analysis/Real/Cardinality.lean` -- `theorem not_countable_real`, `theorem mk_real`

## Statement 29: Set of all languages is uncountable
**Assessment: non-included**
While mathlib proves the reals are uncountable, the specific statement that the set of all languages over a finite alphabet is uncountable is not formalized. This would require showing that the power set of countably many strings is uncountable, which follows from cardinal arithmetic available in mathlib but is not stated as an explicit theorem about languages.
**Searched**: `Mathlib/Computability/Language.lean`, `Mathlib/Computability/Encoding.lean`

## Statement 30: Some language is not decidable
**Assessment: non-included**
While this follows immediately from the halting problem undecidability (Statement 26), the specific corollary that some language is not decidable (via cardinality argument comparing languages to TMs) is not stated as a separate theorem.
**Searched**: `Mathlib/Computability/Halting.lean`

## Statement 31: A_TM is not decidable (restated)
**Assessment: included**
Same as Statement 26. The `halting_problem` theorem in `Halting.lean` covers this.
**Mathlib references**: `Mathlib/Computability/Halting.lean` -- `theorem halting_problem`

## Statement 32: Recognizable and co-recognizable implies decidable
**Assessment: included**
Mathlib proves `computable_iff_re_compl_re : ComputablePred p <-> REPred p /\ REPred (fun a => not (p a))`, which states that a predicate is computable (decidable) if and only if both it and its complement are RE (recognizable). This is exactly the textbook statement.
**Mathlib references**: `Mathlib/Computability/Halting.lean` -- `theorem computable_iff_re_compl_re`, `theorem computable_iff_re_compl_re'`

## Statement 33: Complement of A_TM is T-unrecognizable
**Assessment: included**
Mathlib proves `halting_problem_not_re (n) : ¬REPred fun c => ¬(eval c n).Dom`, which states that the complement of the halting predicate is not RE (not recognizable). This follows from the halting problem undecidability combined with the fact that the halting problem is RE.
**Mathlib references**: `Mathlib/Computability/Halting.lean` -- `theorem halting_problem_not_re`

## Statement 34: HALT_TM is undecidable
**Assessment: included**
The halting problem undecidability is directly formalized as `halting_problem (n) : ¬ComputablePred fun c => (eval c n).Dom`. This states that for any input n, the predicate "does code c halt on n" is not computable.
**Mathlib references**: `Mathlib/Computability/Halting.lean` -- `theorem halting_problem`

## Statement 35: E_TM is undecidable
**Assessment: non-included**
The undecidability of the emptiness problem for Turing machines (whether a TM's language is empty) is not formalized in mathlib. The halting problem undecidability is proved via Rice's theorem, but the specific E_TM undecidability is not stated.
**Searched**: `Mathlib/Computability/Halting.lean`

## Statement 36: Mapping reducibility and decidability
**Assessment: included**
Mathlib formalizes many-one reducibility (`ManyOneReducible`, notation `<=_0`) and proves that computability is preserved under reduction: `ComputablePred.computable_of_manyOneReducible : p <=_0 q -> ComputablePred q -> ComputablePred p`. This says if A reduces to B and B is decidable, then A is decidable.
**Mathlib references**: `Mathlib/Computability/Reduce.lean` -- `def ManyOneReducible`, `theorem computable_of_manyOneReducible`

## Statement 37: If A reduces to B and A undecidable then B undecidable
**Assessment: included**
This is the contrapositive of Statement 36, which follows directly from `computable_of_manyOneReducible`. If A is many-one reducible to B and A is undecidable, then B must be undecidable.
**Mathlib references**: `Mathlib/Computability/Reduce.lean` -- `theorem computable_of_manyOneReducible` (contrapositive)

## Statement 38: Mapping reducibility and T-recognizability
**Assessment: non-included**
While mathlib defines `ManyOneReducible` and `REPred`, there is no explicit theorem stating that RE-ness is preserved under many-one reduction (i.e., if A <=_0 B and B is RE then A is RE). The file `Reduce.lean` focuses on `ComputablePred` preservation, not `REPred` preservation.
**Searched**: `Mathlib/Computability/Reduce.lean`, `Mathlib/Computability/Halting.lean`

## Statement 39: If A reduces to B and A T-unrecognizable then B T-unrecognizable
**Assessment: non-included**
Same as Statement 38 -- no `REPred` preservation under reduction is formalized.
**Searched**: `Mathlib/Computability/Reduce.lean`

## Statement 40: E_TM is T-unrecognizable
**Assessment: non-included**
The T-unrecognizability of the emptiness problem for Turing machines is not formalized in mathlib.
**Searched**: `Mathlib/Computability/Halting.lean`, `Mathlib/Computability/Reduce.lean`

## Statement 41: EQ_TM and complement are T-unrecognizable
**Assessment: non-included**
The T-unrecognizability of the equivalence problem for Turing machines is not formalized.
**Searched**: `Mathlib/Computability/Halting.lean`, `Mathlib/Computability/Reduce.lean`

## Statement 42: Hilbert's 10th problem (undecidability)
**Assessment: non-included**
Mathlib has extensive work on Diophantine equations via `Mathlib/NumberTheory/Dioph.lean` and `Mathlib/NumberTheory/PellMatiyasevic.lean`, including the definition of Diophantine sets and the proof that the power function is Diophantine (Matiyasevich's theorem). However, the final undecidability result -- that deciding whether a Diophantine equation has a solution is undecidable -- is not proved. The `Dioph.lean` file has a TODO noting "Finish the solution of Hilbert's tenth problem."
**Searched**: `Mathlib/NumberTheory/Dioph.lean`, `Mathlib/NumberTheory/PellMatiyasevic.lean`

## Statement 43: A_LBA is decidable
**Assessment: non-included**
Linear Bounded Automata are not formalized in mathlib. Searched for `LBA`, `linear bounded` in `Mathlib/Computability/` with no results.
**Searched**: `Mathlib/Computability/` directory

## Statement 44: E_LBA is undecidable
**Assessment: non-included**
No LBA formalization exists in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 45: PCP is undecidable
**Assessment: non-included**
The Post Correspondence Problem is not formalized in mathlib. Searched for `PCP`, `post correspondence` in `Mathlib/Computability/` with no results.
**Searched**: `Mathlib/Computability/` directory

## Statement 46: ALL_CFG is undecidable
**Assessment: non-included**
The universality problem for CFGs is not formalized in mathlib. The CFG formalization is limited to basic definitions and derivation properties.
**Searched**: `Mathlib/Computability/ContextFreeGrammar.lean`, `Mathlib/Computability/Halting.lean`

## Statement 47: Self-Reproducing TM
**Assessment: non-included**
No self-reproducing TM (quine) construction is formalized in mathlib. Searched for `self reproducing`, `quine` in `Mathlib/Computability/` with no results.
**Searched**: `Mathlib/Computability/` directory

## Statement 48: Computable function q (prints w and halts)
**Assessment: non-included**
This lemma used in the recursion theorem proof is not separately formalized. While the recursion theorem itself is proved, this specific helper is not isolated.
**Searched**: `Mathlib/Computability/PartrecCode.lean`

## Statement 49: Recursion Theorem
**Assessment: included**
Mathlib proves Kleene's second recursion theorem as `Nat.Partrec.Code.fixed_point2`: for any partial recursive function `f : Code -> N ->. N`, there exists a code `c` such that `eval c = f c`. This is the recursion theorem: the TM R computes the same function as T given the description of R.
**Mathlib references**: `Mathlib/Computability/PartrecCode.lean` -- `theorem fixed_point2`

## Statement 50: A_TM undecidable (new proof via recursion theorem)
**Assessment: included**
The halting problem proof in mathlib (`halting_problem`) uses Rice's theorem, which itself uses the fixed-point theorem (recursion theorem). The chain is: `fixed_point2` -> `rice` -> `halting_problem`. So the recursion-theorem-based proof of undecidability is effectively present in the proof chain.
**Mathlib references**: `Mathlib/Computability/Halting.lean` -- `theorem halting_problem`; `Mathlib/Computability/PartrecCode.lean` -- `theorem fixed_point2`

## Statement 51: Fixed-point Theorem
**Assessment: included**
Roger's fixed-point theorem is formalized as `Nat.Partrec.Code.fixed_point`: for any total computable function `f : Code -> Code`, there exists a code `c` such that `eval (f c) = eval c`. This is the fixed-point version of the recursion theorem.
**Mathlib references**: `Mathlib/Computability/PartrecCode.lean` -- `theorem fixed_point`

## Statement 52: MIN_TM is T-unrecognizable
**Assessment: non-included**
The T-unrecognizability of the set of minimal Turing machines is not formalized in mathlib.
**Searched**: `Mathlib/Computability/Halting.lean`, `Mathlib/Computability/PartrecCode.lean`

## Statement 53: Godel's First Incompleteness Theorem (informal)
**Assessment: non-included**
Godel's incompleteness theorems are not formalized in mathlib. Searched for `Godel`, `godel`, `incompleteness`, `Hilbert` in `Mathlib/Computability/` with no results. (Note: there exist separate Lean projects formalizing Godel's theorems, but they are not part of mathlib.)
**Searched**: `Mathlib/Computability/` directory

## Statement 54: True but unprovable statement
**Assessment: non-included**
Same as Statement 53 -- no formalization of Godel's incompleteness theorems in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 55: A = {a^k b^k} in O(n^2) time
**Assessment: non-included**
Mathlib does not formalize complexity classes TIME(f(n)) or any specific time complexity results. No time bounds on TM computations are proved.
**Searched**: `Mathlib/Computability/TuringMachine.lean`, `Mathlib/Computability/TMComputable.lean`

## Statement 56: A = {a^k b^k} in O(n log n) time
**Assessment: non-included**
No time complexity results are formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 57: Lower bound for {a^k b^k}
**Assessment: non-included**
No time complexity lower bounds are formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 58: A = {a^k b^k} in O(n) on multi-tape
**Assessment: non-included**
No time complexity results for multi-tape machines are formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 59: Multi-tape to 1-tape time simulation (quadratic blowup)
**Assessment: non-included**
While mathlib has a TM2-to-TM1 simulation (`TM2to1.tr` with `tr_respects`), the time complexity analysis showing quadratic blowup is not formalized. The simulation proves functional equivalence only.
**Searched**: `Mathlib/Computability/TuringMachine.lean` -- `TM2to1` section

## Statement 60: PATH in P
**Assessment: non-included**
Mathlib does not formalize the complexity class P or any specific membership results. No graph reachability problems are formalized in the computability framework.
**Searched**: `Mathlib/Computability/` directory

## Statement 61: HAMPATH in NP
**Assessment: non-included**
The complexity class NP is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 62: COMPOSITES in NP
**Assessment: non-included**
NP is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 63: COMPOSITES in P (AKS, 2002)
**Assessment: non-included**
Neither P nor the AKS primality test is formalized in mathlib. Searched for `AKS`, `primality test`, `primes in P` across all of mathlib with no relevant computability results.
**Searched**: `Mathlib/Computability/`, broader mathlib

## Statement 64: A_CFG in NP
**Assessment: non-included**
NP is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 65: A_CFG in P
**Assessment: non-included**
P is not formalized in mathlib. While CYK parsing is an algorithm that runs in polynomial time, the complexity class P and membership results are absent.
**Searched**: `Mathlib/Computability/` directory

## Statement 66: Cook-Levin (SAT in P implies P = NP)
**Assessment: non-included**
Complexity classes P and NP, SAT, and NP-completeness are not formalized in mathlib. Searched for `SAT`, `NP`, `ComplexityClass`, `polynomial time` in `Mathlib/Computability/` with no relevant results (TMComputable.lean mentions polynomial time for TM2 outputs but not complexity classes).
**Searched**: `Mathlib/Computability/` directory

## Statement 67: Polynomial-time reducibility and P
**Assessment: non-included**
Polynomial-time reductions are not formalized in mathlib. Only many-one and one-one (computable) reductions are defined.
**Searched**: `Mathlib/Computability/Reduce.lean`

## Statement 68: 3SAT reduces to CLIQUE
**Assessment: non-included**
No SAT, 3SAT, or CLIQUE problem formalizations exist in the computability context.
**Searched**: `Mathlib/Computability/` directory

## Statement 69: CLIQUE in P implies 3SAT in P
**Assessment: non-included**
No complexity class formalizations exist in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 70: Cook-Levin Theorem (SAT is NP-complete)
**Assessment: non-included**
NP-completeness is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 71: HAMPATH is NP-complete
**Assessment: non-included**
NP-completeness is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 72: 3SAT is NP-complete
**Assessment: non-included**
NP-completeness is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 73: TIME and SPACE relationship
**Assessment: non-included**
Complexity classes TIME(f(n)) and SPACE(f(n)) are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 74: P subset PSPACE
**Assessment: non-included**
Complexity classes P and PSPACE are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 75: NP subset PSPACE
**Assessment: non-included**
Complexity classes NP and PSPACE are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 76: TQBF in PSPACE
**Assessment: non-included**
TQBF and PSPACE are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 77: LADDER_DFA in NPSPACE
**Assessment: non-included**
NPSPACE and the LADDER_DFA problem are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 78: LADDER_DFA in PSPACE
**Assessment: non-included**
No space complexity classes are formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 79: LADDER_DFA in SPACE(n^2)
**Assessment: non-included**
No space complexity analysis is available in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 80: Savitch's Theorem
**Assessment: non-included**
Savitch's theorem (NSPACE(f(n)) subset SPACE(f(n)^2)) is not formalized. No space complexity classes exist in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 81: TQBF is PSPACE-complete
**Assessment: non-included**
PSPACE-completeness is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 82: GG is PSPACE-complete
**Assessment: non-included**
Generalized Geography and PSPACE-completeness are not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 83: L subset P
**Assessment: non-included**
Log-space class L and polynomial time class P are not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 84: NL subset SPACE(log^2 n)
**Assessment: non-included**
NL and space complexity classes are not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 85: NL subset P
**Assessment: non-included**
NL and P complexity classes are not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 86: Log-space reducibility
**Assessment: non-included**
Log-space reductions are not formalized. Only computable many-one and one-one reductions exist.
**Searched**: `Mathlib/Computability/Reduce.lean`

## Statement 87: PATH is NL-complete
**Assessment: non-included**
NL-completeness is not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 88: Complement of 2SAT is NL-complete
**Assessment: non-included**
NL-completeness is not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 89: Immerman-Szelepsenyi (NL = coNL)
**Assessment: non-included**
NL and coNL are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 90: NL-machine computes c implies path
**Assessment: non-included**
No NL machine model is formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 91: NL-machine computes c_d implies path_d
**Assessment: non-included**
No NL machine model is formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 92: NL-machine computes c_d implies path_{d+1}
**Assessment: non-included**
No NL machine model is formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 93: Some NL-machine computes c_{d+1} from c_d
**Assessment: non-included**
No NL machine model is formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 94: Space Hierarchy Theorem
**Assessment: non-included**
The Space Hierarchy Theorem is not formalized. No space complexity classes or hierarchy theorems exist in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 95: Time Hierarchy Theorem
**Assessment: non-included**
The Time Hierarchy Theorem is not formalized. No time complexity classes or hierarchy theorems exist in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 96: NL strictly subset PSPACE
**Assessment: non-included**
No complexity class separations are formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 97: EXPTIME-complete implies not in P
**Assessment: non-included**
EXPTIME is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 98: EXPSPACE-complete implies not in PSPACE
**Assessment: non-included**
EXPSPACE is not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 99: EQ_REX in PSPACE
**Assessment: non-included**
PSPACE and the regular expression equivalence problem are not formalized as complexity-theoretic results.
**Searched**: `Mathlib/Computability/` directory

## Statement 100: EQ_REX with exponentiation is EXPSPACE-complete
**Assessment: non-included**
EXPSPACE and extended regular expressions are not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 101: Oracle with P^A = NP^A
**Assessment: non-included**
Oracle Turing machines in the complexity-theoretic sense (with P^A, NP^A) are not formalized. Mathlib has `TuringDegree.lean` with Turing reducibility for partial recursive functions, but this is about computability not complexity.
**Searched**: `Mathlib/Computability/TuringDegree.lean`

## Statement 102: Amplification Lemma (BPP error reduction)
**Assessment: non-included**
BPP and probabilistic Turing machines are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 103: EQ_BP is coNP-complete
**Assessment: non-included**
coNP-completeness and branching programs are not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 104: EQ_ROBP in BPP
**Assessment: non-included**
BPP and read-once branching programs are not formalized.
**Searched**: `Mathlib/Computability/` directory

## Statement 105: Polynomial Lemma (nonzero poly has at most d roots)
**Assessment: included**
Mathlib proves `Polynomial.card_roots' (p : R[X]) : Multiset.card p.roots <= natDegree p` for integral domains. This states that a nonzero polynomial of degree d has at most d roots (counted with multiplicity).
**Mathlib references**: `Mathlib/Algebra/Polynomial/Roots.lean` -- `theorem card_roots'`

## Statement 106: Corollary 1 of Polynomial Lemma (two distinct polys agree on at most d values)
**Assessment: included**
This corollary follows directly from Statement 105 applied to the difference polynomial p1 - p2. Mathlib provides `Polynomial.card_roots' (p : R[X]) : Multiset.card p.roots <= natDegree p`, and since p1 - p2 has degree at most d, it has at most d roots. This is a direct consequence available in mathlib.
**Mathlib references**: `Mathlib/Algebra/Polynomial/Roots.lean` -- `theorem card_roots'` (applied to `p1 - p2`)

## Statement 107: Corollary 2 of Polynomial Lemma (root probability bound over finite field)
**Assessment: non-included**
While the root count bound is in mathlib (Statement 105), the probabilistic statement about random evaluation over a finite field is not explicitly formalized as a probability bound. Mathlib does not combine the polynomial root bound with probability theory in this way.
**Searched**: `Mathlib/Algebra/Polynomial/Roots.lean`, `Mathlib/Probability/`

## Statement 108: Schwartz-Zippel Lemma
**Assessment: included**
Mathlib has a full proof of the Schwartz-Zippel lemma in `Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean`. The main results include `MvPolynomial.schwartz_zippel_totalDegree` and related sharper versions. The lemma bounds the probability that a nonzero multivariate polynomial evaluates to zero at a random point.
**Mathlib references**: `Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean` -- `schwartz_zippel_totalDegree`, `schwartz_zippel_sup_sum`, `schwartz_zippel_sum_degreeOf`

## Statement 109: Graph Non-Isomorphism in IP
**Assessment: non-included**
Interactive proofs (IP) are not formalized in mathlib. No formalization of the IP protocol for graph non-isomorphism exists.
**Searched**: `Mathlib/Computability/` directory

## Statement 110: IP = PSPACE
**Assessment: non-included**
Neither IP nor PSPACE (as complexity classes) are formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 111: #SAT is coNP-hard
**Assessment: non-included**
Counting problems (#SAT), coNP, and hardness are not formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory

## Statement 112: #SAT in IP
**Assessment: non-included**
Neither #SAT nor IP is formalized in mathlib.
**Searched**: `Mathlib/Computability/` directory
