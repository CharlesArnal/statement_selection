# 18.404/6.840 Intro to the Theory of Computation

**Instructor:** Mike Sipser

#### TAs:

- Fadi Atieh, Damian Barabonkov,
- Alex Dimitrakakis, Thomas Xiong,
- Abbas Zeitoun, and Emily Liu

### 18.404 Course Outline

### **Computability Theory 1930s – 1950s**

- What is computable... or not?
- Examples:
  program verification, mathematical truth
- Models of Computation:
  Finite automata, Turing machines, ...

### Complexity Theory 1960s – present

- What is computable in practice?
- Example: factoring problem
- P versus NP problem
- Measures of complexity: Time and Space
- Models: Probabilistic and Interactive computation

### Course Mechanics

#### **Zoom Lectures**

- Live and Interactive via Chat
- Live lectures are recorded for later viewing

#### **Zoom Recitations**

- Not recorded
- Two convert to in-person
- Review concepts and more examples
- Optional unless you are having difficulty
  <u>Participation</u> can raise low grades
- Attend any recitation

#### **Text**

- Introduction to the Theory of Computation Sipser, 3<sup>rd</sup> Edition US. (Other editions ok but are missing some Exercises and Problems).

#### Homework bi-weekly – 35%

- More information to follow

### Midterm (15%) and Final exam (25%)

Open book and notes

#### Check-in quizzes for credit – 25%

- Distinct Live and Recorded versions
- Complete either one for credit within 48 hours
- Initially ungraded; full credit for participation

## **Course Expectations**

### **Prerequisites**

Prior substantial experience and comfort with mathematical concepts, theorems, and proofs. Creativity will be needed for psets and exams.

### **Collaboration policy on homework**

- Allowed. But try problems yourself first.
- Write up your own solutions.
- No bibles or online materials.

# Role of Theory in Computer Science

- 1. Applications
- 2. Basic Research
- 3. Connections to other fields
- 4. What is the nature of computation?

# Let's begin: Finite Automata

States:  $q_1 q_2 q_3$ 

Transitions:  $\frac{1}{1}$ 

Start state: →

Accept states:

**Input:** finite string

**Output:** Accept or Reject

Computation process: Begin at start state,

read input symbols, follow corresponding transitions,

Accept if end with accept state, Reject if not.

**Examples:**  $01101 \rightarrow Accept$ 

 $00101 \rightarrow Reject$ 

 $M_1$  accepts exactly those strings in A where  $A = \{w \mid w \text{ contains substring } 11\}.$ 

Say that A is the language of  $M_1$  and that  $M_1$  recognizes A and that  $A = L(M_1)$ .

### Finite Automata – Formal Definition

 $\delta(q, a) = r \text{ means } (q)$ 

**Defn:** A finite automaton M is a 5-tuple  $(Q, \Sigma, \delta, q_0, F)$ 

- Q finite set of states
- $\Sigma$  finite set of alphabet symbols
- $\delta$  transition function  $\delta \colon Q \times \Sigma \to Q$
- $q_0$  start state

F set of accept states

### Example:

$$M_1 = (Q, \Sigma, \delta, q_1, F)$$
  $\delta = \begin{bmatrix} 0 & 1 \\ q_1 & q_1 & q_2 \\ p_2 & q_1 & q_3 \\ p_3 & q_3 & q_3 \end{bmatrix}$   $\delta = \begin{bmatrix} 0 & 1 \\ q_1 & q_1 & q_2 \\ q_2 & q_1 & q_3 \\ q_3 & q_3 & q_3 \end{bmatrix}$ 

## Finite Automata – Computation

#### **Strings and languages**

- A string is a finite sequence of symbols in  $\Sigma$
- A <u>language</u> is a set of strings (finite or infinite)
- The empty string ε is the string of length 0
- The empty language ø is the set with no strings

**Defn:** M accepts string  $w = w_1w_2 \dots w_n$  each  $w_i \in \Sigma$  if there is a sequence of states  $r_0, r_1, r_2, \dots, r_n \in Q$  where:

 $\begin{array}{ll} \text{-} \ r_0 \ = \ q_0 \\ \text{-} \ r_i \ = \ \delta(r_{i-1}, w_i) \ \text{for} \ 1 \leq i \leq n \\ \text{-} \ r_n \in F \end{array}$ 

#### **Recognizing languages**

- $L(M) = \{w \mid M \text{ accepts } w\}$
- L(M) is the language of M
- M recognizes L(M)

**Defn:** A language is <u>regular</u> if some finite automaton recognizes it.

# Regular Languages – Examples

 $L(M_1) = \{w \mid w \text{ contains substring } 11\} = A$ 

Therefore *A* is regular

### More examples:

Let  $B = \{w \mid w \text{ has an even number of 1s}\}$  B is regular (make automaton for practice).

Let  $C = \{w \mid w \text{ has equal numbers of 0s and 1s}\}$  C is <u>not</u> regular (we will prove).

**Goal:** Understand the regular languages

# Regular Expressions

#### **Regular operations.** Let *A*, *B* be languages:

```
- Union: A \cup B = \{w \mid w \in A \text{ or } w \in B\}
```

- Concatenation:  $A \circ B = \{xy \mid x \in A \text{ and } y \in B\} = AB$
- Star:  $A^* = \{x_1 \dots x_k | \text{ each } x_i \in A \text{ for } k \ge 0\}$ Note:  $\varepsilon \in A^*$  always

### **Example.** Let $A = \{good, bad\}$ and $B = \{boy, girl\}$ .

- $A \cup B = \{good, bad, boy, girl\}$
- $A \circ B = AB = \{\text{goodboy, goodgirl, badboy, badgirl}\}$
- $A^* = \{\epsilon, \text{good}, \text{bad}, \text{goodgood}, \text{goodbad}, \text{badgood}, \text{badbad}, \text{goodgoodgood}, \text{goodgoodbad}, \dots \}$

### Regular expressions

- Built from  $\Sigma$ , members  $\Sigma$ ,  $\emptyset$ ,  $\varepsilon$  [Atomic]
- By using U,o,\* [Composite]

#### Examples:

- $(0 \cup 1)^* = \Sigma^*$  gives all strings over  $\Sigma$
- $\Sigma^*1$  gives all strings that end with 1
- $\Sigma^* 11\Sigma^*$  = all strings that contain  $11 = L(M_1)$

Goal: Show finite automata equivalent to regular expressions

# Closure Properties for Regular Languages

**Theorem:** If  $A_1$ ,  $A_2$  are regular languages, so is  $A_1 \cup A_2$  (closure under U)

**Proof:** Let  $M_1 = (Q_1, \Sigma, \delta_1, q_1, F_1)$  recognize  $A_1$   $M_2 = (Q_2, \Sigma, \delta_2, q_2, F_2)$  recognize  $A_2$ 

Construct  $M = (Q, \Sigma, \delta, q_0, F)$  recognizing  $A_1 \cup A_2$ 

M should accept input w if either  $M_1$  or  $M_2$  accept w.

#### Check-in 1.1

In the proof, if  $M_1$  and  $M_2$  are finite automata where  $M_1$  has  $k_1$  states and  $M_2$  has  $k_2$  states Then how many states does M have?

- (a)  $k_1 + k_2$
- (b)  $(k_1)^2 + (k_2)^2$
- (c)  $k_1 \times k_2$

#### Components of *M*:

$$\begin{split} Q &= Q_1 \times Q_2 \\ &= \{ (q_1, q_2) | q_1 \in Q_1 \text{ and } q_2 \in Q_2 \} \end{split}$$

$$q_0 = (q_1, q_2)$$

$$\delta\big((q,r),a\big)=\big(\delta_1(q,a),\delta_2(r,a)\big)$$

$$F = F_1 \times F_2$$
 **NO!** [gives intersection]

$$F = (F_1 \times Q_2) \cup (Q_1 \times F_2)$$

Check-in 1.1

# Closure Properties continued

**Theorem:** If  $A_1$ ,  $A_2$  are regular languages, so is  $A_1A_2$  (closure under  $\circ$ )

**Proof:** Let  $M_1 = (Q_1, \Sigma, \delta_1, q_1, F_1)$  recognize  $A_1$ 

 $M_2 = (Q_2, \Sigma, \delta_2, q_2, F_2)$  recognize  $A_2$ 

Construct  $M = (Q, \Sigma, \delta, q_0, F)$  recognizing  $A_1A_2$ 

M should accept input w if w = xy where  $M_1$  accepts x and  $M_2$  accepts y.

$$w \xrightarrow{x} y$$

Doesn't work: Where to split w?

# Quick review of today

- 1. Introduction, outline, mechanics, expectations
- 2. Finite Automata, formal definition, regular languages
- 3. Regular Operations and Regular Expressions
- 4. Proved: Class of regular languages is closed under U
- 5. Started: Closure under , to be continued...

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 2

Last time: (Sipser §1.1)

- Finite automata, regular languages
- Regular operations U,o,\*
- Regular expressions
- Closure under U

**Today:** (Sipser §1.2 – §1.3)

- Nondeterminism
- Closure under o and \*
- Regular expressions → finite automata

**Goal:** Show finite automata equivalent to regular expressions

### **Problem Sets**

- 35% of overall grade
- Problems are hard! Leave time to think about them.
- Writeups need to be clear and understandable, handwritten ok.
   Level of detail in proofs comparable to lecture: focus on main ideas.
   Don't need to include minor details.
- Submit via gradescope (see Canvas) by 2:30pm Cambridge time.
   Late submission accepted (on gradescope) until 11:59pm following day:
   1 point (out of 10 points) per late problem penalty.
   After that solutions are posted so not accepted without S3 excuse.
- Optional problems:

Don't count towards grade except for A+.

Value to you (besides the challenge):

Recommendations, employment (future grading, TA, UROP)

- Problem Set 1 is due in one week.

## Closure Properties for Regular Languages

**Theorem:** If  $A_1$ ,  $A_2$  are regular languages, so is  $A_1A_2$  (closure under  $\circ$ )

Recall proof attempt: Let  $M_1 = (Q_1, \Sigma, \delta_1, q_1, \overline{F_1})$  recognize  $A_1$ 

 $M_2=(Q_2,\Sigma,\,\delta_2,\,q_2,\,F_2)$  recognize  $A_2$ 

Construct  $M = (Q, \Sigma, \delta, q_0, F)$  recognizing  $A_1A_2$ 

M should accept input w if w = xy where  $M_1$  accepts x and  $M_2$  accepts y.

Doesn't work: Where to split w?

Hold off. Need new concept.

### Nondeterministic Finite Automata

#### **New features of nondeterminism:**

- multiple paths possible (0, 1 or many at each step)
- ε-transition is a "free" move without reading input
- Accept input if <u>some</u> path leads to **accept**

#### **Example inputs:**

- ab
- aa
- aba
- abb

#### Check-in 2.1

What does  $N_1$  do on input aab?

- (a) Accept
- (b) Reject
- (c) Both Accept and Reject

Check-in 2.1

### NFA – Formal Definition

**Defn:** A <u>nondeterministic finite automaton (NFA)</u>

N is a 5-tuple  $(Q, \Sigma, \delta, q_0, F)$ 

States phabet state states

- all same as before except  $\delta$
- $\delta: Q \times \Sigma_{\varepsilon} \to \mathcal{P}(Q) = \{R | R \subseteq Q\}$ power set  $\Sigma \cup \{\varepsilon\}$
- In the  $N_1$  example:  $\delta(q_1, \mathbf{a}\,) = \{q_1, q_2\}$   $\delta(q_1, \mathbf{b}\,) = \emptyset$

### Ways to think about nondeterminism:

<u>Computational:</u> Fork new parallel thread and accept if any thread leads to an accept state.

Mathematical: Tree with branches.

Accept if any branch leads to an accept state.

Magical: Guess at each nondeterministic step which way to go. Machine always makes the right guess that leads to accepting, if possible.

## Converting NFAs to DFAs

**Theorem:** If an NFA recognizes A then A is regular

**Proof:** Let NFA  $M = (Q, \Sigma, \delta, q_0, F)$  recognize A

Construct DFA  $M' = (Q', \Sigma, \delta', q'_0, F')$  recognizing A

(Ignore the ε-transitions, can easily modify to handle them)

**IDEA:** DFA M' keeps track of the <u>subset of possible states</u> in NFA M.

### Check-in 2.2

If M has n states, how many states does M' have by this construction?

- (a) 2n
- (b)  $n^2$
- (c)  $2^n$

#### Construction of *M*′:

$$Q' = \mathcal{P}(Q)$$

$$\delta'(R,a) = \overline{R \in O'}$$

$$q_0' = \{q_0\}$$

$$F' = \{R \in Q' | R \text{ intersects } F\}$$

## Return to Closure Properties

**Recall Theorem:** If  $A_1, A_2$  are regular languages, so is  $A_1 \cup A_2$  (The class of regular languages is closed under union)

New Proof (sketch): Given DFAs  $M_1$  and  $M_2$  recognizing  $A_1$  and  $A_2$  Construct NFA M recognizing  $A_1 \cup A_2$ 

#### Nondeterminism

parallelism vs guessing

# Closure under • (concatenation)

**Theorem:** If  $A_1, A_2$  are regular languages, so is  $A_1A_2$ 

**Proof sketch:** Given DFAs  $M_1$  and  $M_1$  recognizing  $A_1$  and  $A_2$ 

Construct NFA M recognizing  $A_1A_2$ 

M should accept input w if w = xy where  $M_1$  accepts x and  $M_2$  accepts y.

$$w = \frac{\phantom{a}}{x}$$

Nondeterministic M' has the option to jump to  $M_2$  when  $M_1$  accepts.

# Closure under \* (star)

**Theorem:** If A is a regular language, so is  $A^*$ 

**Proof sketch:** Given DFA M recognizing A Construct NFA M' recognizing  $A^*$ 

Make sure M' accepts  $\epsilon$ 

### Check-in 2.3

If M has n states, how many states does M' have by this construction?

- (a) n
- (b) n + 1
- (c) 2n

Check-in 2.3

## Regular Expressions → NFA

**Theorem:** If R is a regular expr and A = L(R) then A is regular

**Proof:** Convert R to equivalent NFA M:

If R is atomic:

Equivalent *M* is:

$$R = a \text{ for } a \in \Sigma \longrightarrow 0$$

$$R = \varepsilon$$

$$R = \emptyset$$

If *R* is composite:

$$R = R_1 \cup R_2$$

$$R = R_1 \circ R_2$$

$$R = R_1^*$$

Use closure constructions

### Example:

Convert  $(a \cup ab)^*$  to equivalent NFA

ab: 
$$\rightarrow \bigcirc$$
  $\xrightarrow{a} \bigcirc$   $\xrightarrow{\varepsilon}$   $\xrightarrow{b}$   $\bigcirc$ 

## Quick review of today

- 1. Nondeterministic finite automata (NFA)
- 2. Proved: NFA and DFA are equivalent in power
- 3. Proved: Class of regular languages is closed under o,\*
- 4. Conversion of regular expressions to NFA

#### Check-in 2.4

Recitations start tomorrow online (same link as for lectures).

They are optional, unless you need more help.

You may attend any recitation(s).

Which do you think you'll attend? (you may check several)

- (a) 10:00 (b) 11:00 (c) 12:00
- (d) 1:00 (e) 2:00 (f) I prefer a different time (please post on piazza, but no promises)

Check-in 2.4

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 3

#### Last time:

- Nondeterminism
- NFA  $\rightarrow$  DFA
- Closure under and \*
- Regular expressions → finite automata

#### **Today:** (Sipser §1.4 – §2.1)

- Finite automata → regular expressions
- Proving languages aren't regular
- Context free grammars

We start counting Check-ins today. Review your email from Canvas.

Homework due Thursday.

### DFAs → Regular Expressions

**Recall Theorem:** If R is a regular expressipn and A = L(R) then A is regular

**Proof:** Conversion  $R \to NFA M \to DFA M'$ 

Recall: we did  $(a \cup ab)^*$  as an example

**Today's Theorem:** If A is regular then A = L(R) for some regular expr R

**Proof:** Give conversion DFA  $M \rightarrow R$ 

WAIT! Need new concept first.

### **Generalized NFA**

**Defn:** A <u>Generalized Nondeterministic Finite Automaton</u> (GNFA) is similar to an NFA, but allows regular expressions as transition labels

#### For convenience we will assume:

- One accept state, separate from the start state
- One arrow from each state to each state, except
  - a) only exiting the start state
  - b) only entering the accept state

We can easily modify a GNFA to have this special form.

### GNFA → Regular Expressions

**Lemma:** Every GNFA G has an equivalent regular expression R

**Proof:** By induction on the number of states k of G

Basis (k = 2):

$$G = \longrightarrow \bigcirc \xrightarrow{r} \bigcirc$$

Remember: G is in special form

Let R = r

Induction step (k > 2): Assume Lemma true for k - 1 states and prove for k states

IDEA: Convert k-state GNFA to equivalent (k-1) -state GNFA

GNFA
$$k \text{ states}$$

$$k - 1 \text{ states}$$

### k-state GNFA $\rightarrow (k-1)$ -state GNFA

#### Check-in 3.1

We just showed how to convert <u>GNFAs</u> to regular expressions but our goal was to show that how to convert <u>DFAs</u> to regular expressions. How do we finish our goal?

- (a) Show how to convert DFAs to GNFAs
- (b) Show how to convert GNFAs to DFAs
- (c) We are already done. DFAs are a type of GNFAs.

Thus DFAs and regular expressions are equivalent.

- 1. Pick any state x except the start and accept states.
- 2. Remove x.
- 3. Repair the damage by recovering all paths that went through x.
- 4. Make the indicated change for each pair of states  $q_i$ ,  $q_j$ .

Check-in 3.1

### Non-Regular Languages

#### How do we show a language is not regular?

- Remember, to show a language is regular, we give a DFA.
- To show a language is *not* regular, we must give a proof.
- It is not enough to say that you couldn't find a DFA for it, therefore the language isn't regular.

### Two examples: Here $\Sigma = \{0,1\}$ .

- 1. Let  $B = \{w \mid w \text{ has equal numbers of 0s and 1s} \}$ Intuition: B is not regular because DFAs cannot count unboundedly.
- 2. Let  $C = \{w \mid w \text{ has equal numbers of 01 and 10 substrings}\}$

Intuition: C is not regular because DFAs cannot count unboundedly. However C is regular!

Moral: You need to give a proof.

# Method for Proving Non-regularity

**Pumping Lemma:** For every regular language A, there is a number p (the "pumping length") such that if  $s \in A$  and  $|s| \ge p$  then s = xyz where

1) 
$$xy^iz \in A$$
 for all  $i \ge 0$   $y^i = yy \cdots y$ 

$$y^i = yy \cdots y$$

- 2)  $y \neq \epsilon$
- 3)  $|xy| \leq p$

Informally: A is regular  $\rightarrow$  every long  $\stackrel{\triangleleft}{\cdot}$  Check-in 3.2

**Proof:** Let DFA M recognize A. Let p

$$s = \begin{array}{c|cccc} x & y & z \\ \hline & q_j & q_j \end{array}$$

M will repeat a state  $q_i$  when reading because *s* is so long.

$$\begin{array}{c|ccccccccccccccccccccccccccccccccccc$$

The Pumping Lemma depends on the fact that if M has p states and it runs for more than p steps then M will enter some state at least twice.

We call that fact:

- (a) The Pigeonhole Principle
- (b) Burnside's Counting Theorem
- is als (c) The Coronavirus Calculation

Check-in 3.2

# Example 1 of Proving Non-regularity

**Pumping Lemma:** For every regular language A, there is a p

such that if  $s \in A$  and  $|s| \ge p$  then s = xyz where

1) 
$$xy^iz \in A$$
 for all  $i \ge 0$   $y^i = yy \cdots y$ 

- 2)  $y \neq \epsilon$
- 3)  $|xy| \leq p$

Let  $D = \{0^k 1^k | k \ge 0\}$ 

**Show:** *D* is not regular

#### **Proof by Contradiction:**

Assume (to get a contradiction) that D is regular.

The pumping lemma gives p as above. Let  $s = 0^p 1^p \in D$ .

Pumping lemma says that can divide s = xyz satisfying the 3 conditions.

$$s = \underbrace{\begin{array}{c} 000 \cdots 000111 \cdots 111 \\ x \mid y \mid z \end{array}}_{ \begin{array}{c} x \mid y \mid z \end{array}$$

But xyyz has excess 0s and thus  $xyyz \notin D$  contradicting the pumping lemma. Therefore our assumption (D is regular) is false. We conclude that D is not regular.

# Example 2 of Proving Non-regularity

**Pumping Lemma:** For every regular language A, there is a p

such that if  $s \in A$  and  $|s| \ge p$  then s = xyz where

- 1)  $xy^iz \in A$  for all  $i \ge 0$   $y^i = yy \cdots y$
- 2)  $y \neq \varepsilon$
- 3)  $|xy| \leq p$

Let  $F = \{ww | w \in \Sigma^*\}$ . Say  $\Sigma^* = \{0,1\}$ .

**Show:** *F* is not regular

#### **Proof by Contradiction:**

Assume (for contradiction) that F is regular.

The pumping lemma gives p as above. Need to choose  $s \in F$ . Which s?

Try 
$$s = 0^p 0^p \in F$$
.

Try  $s = 0^p 10^p 1 \in F$ . Show cannot be pumped s = xyz satisfying the 3 conditions.  $xyyz \notin F$  Contradiction! Therefore F is not regular.

$$s = \underbrace{\begin{array}{c} 000 \cdots 000000 \cdots 000 \\ \hline x & y & z \\ \leftarrow \leq p & \rightarrow \end{array}}_{V = 00}$$

$$s = \underbrace{\begin{array}{ccc} 000 \cdots 001000 \cdots 001 \\ \hline x & y & z \\ \bullet & \leq p \end{array}}$$

# Example 3 of Proving Non-regularity

**Variant:** Combine closure properties with the Pumping Lemma.

Let  $B = \{w \mid w \text{ has equal numbers of 0s and 1s}\}$ 

**Show:** *B* is not regular

#### **Proof by Contradiction:**

Assume (for contradiction) that B is regular.

We know that  $0^*1^*$  is regular so  $B \cap 0^*1^*$  is regular (closure under intersection).

But  $D = B \cap 0^*1^*$  and we already showed D is not regular. Contradiction!

Therefore our assumption is false, so B is not regular.

### **Context Free Grammars**

$$G_1$$
 $S \to 0S1$ 
 $S \to R$ 
 $R \to \epsilon$ 
(Substitution) Rules

**Rule:** Variable → string of variables and terminals

Variables: Symbols appearing on left-hand side of rule

**Terminals:** Symbols appearing only on right-hand side

Start Variable: Top left symbol

#### **Grammars generate strings**

- 1. Write down start variable
- Replace any variable according to a rule Repeat until only terminals remain
- 3. Result is the generated string
- 4. L(G) is the language of all generated strings.

Check-in 3.3

$$G_2$$
  $S \rightarrow RR$   $R \rightarrow 0R1$   $R \rightarrow \epsilon$ 

Check <u>all</u> of the strings that are in  $L(G_2)$ :

- (a) 001101
- (b) 000111
- (c) 1010
- (d) ε

### Quick review of today

- 1. Conversion of DFAs to regular expressions Summary: DFAs, NFAs, regular expressions are all equivalent
- 2. Proving languages not regular by using the pumping lemma and closure properties
- 3. Context Free Grammars

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 4

#### Last time:

- Finite automata → regular expressions
- Proving languages aren't regular
- Context free grammars

#### Today: (Sipser §2.2)

- Context free grammars (CFGs) definition
- Context free languages (CFLs)
- Pushdown automata (PDA)
- Converting CFGs to PDAs

## Context Free Grammars (CFGs)

$$G_1$$
 S  $\rightarrow$  0S1 Shorthand: S  $\rightarrow$  R S  $\rightarrow$  0S1 | R R  $\rightarrow$   $\epsilon$  R  $\rightarrow$   $\epsilon$ 

Recall that a CFG has terminals, variables, and rules.

#### **Grammars generate strings**

- 1. Write down start variable
- 2. Replace any variable according to a rule Repeat until only terminals remain
- 3. Result is the generated string
- 4. L(G) is the language of all generated strings
- 5. We call L(G) a Context Free Language.

Example of  $G_1$  generating a string

Tree of S S Resulting substitutions string "parse tree"

$$E(G_1) = \{0^k 1^k \mid k \ge 0\}$$

#### CFG – Formal Definition

Defn: A Context Free Grammar (CFG) G is a 4-tuple  $(V, \Sigma, R, S)$ 

- V finite set of variables
- $\Sigma$  finite set of terminal symbols
- R finite set of rules (rule form:  $V \to (V \cup \Sigma)^*$ )
- S start variable

For  $u, v \in (V \cup \Sigma)^*$  write

- 1)  $u \Rightarrow v$  if can go from u to v with one substitution step in
- 2)  $u \stackrel{*}{\Rightarrow} v$  if can go from u to v with some number of substit  $u \Rightarrow u_1 \Rightarrow u_2 \Rightarrow \cdots \Rightarrow u_k = v$  is called a derivation of v.

$$L(G) = \{ w \mid w \in \Sigma^* \text{ and } S \stackrel{*}{\Rightarrow} w \}$$

Defn: A is a Context Free Language (CFL) if A = L(G) for so

#### Check-in 4.1

Which of these are valid CFGs?

$$C_1$$
:  $B \rightarrow OB1 \mid \epsilon$   $C_2$ :  $S \rightarrow OS \mid S1$   
 $B1 \rightarrow 1B$   $R \rightarrow RR$   
 $OB \rightarrow OB$ 

- a)  $C_1$  only
- b)  $C_2$  only
- c) Both  $C_1$  and  $C_2$
- d) Neither

Check-in 4.1

## CFG – Example

$$G_2$$
 $E \rightarrow E+T \mid T$ 
 $T \rightarrow T \times F \mid F$ 
 $F \rightarrow (E) \mid a$ 

Parse E tree

E Resulting string

$$V = \{E, T, F\}$$
  
 $\Sigma = \{+, \times, (, ), a\}$   
 $R = \text{the 6 rules above}$   
 $S = E$ 

Generates a+a×a

Observe that the parse tree contains additional information such as the precedence of  $\times$  over +.

If a string has two different parse trees then it is derived a and we say that the grammar is ambiguous.

#### Check-in 4.2

How many reasonable distinct meanings does the following English sentence have?

The boy saw the girl with the mirror.

- (a) 1
- (b) 2
- (c) 3 or more

## Ambiguity

$$G_2 \\ E \to E+T \mid T \\ T \to T\times F \mid F \\ F \to (E) \mid a$$
 
$$G_3 \\ E \to E+E \mid E\times E \mid (E) \mid a$$

Both  $G_2$  and  $G_3$  recognize the same language, i.e.,  $L(G_2) = L(G_3)$ . However  $G_2$  is an unambiguous CFG and  $G_3$  is ambiguous.

## Pushdown Automata (PDA)

Operates like an NFA except can <u>write-add</u> or <u>read-remove</u> symbols from the top of stack.

| Pop | Pop |

#### **Example:** PDA for $D = \{0^k 1^k | k \ge 0\}$

- 1) Read 0s from input, push onto stack until read 1.
- 2) Read 1s from input, while popping 0s from stack.
- 3) Enter accept state if stack is empty. (note: acceptance only at end of input)

#### PDA – Formal Definition

Defn: A <u>Pushdown Automaton</u> (PDA) is a 6-tuple  $(Q, \Sigma, \Gamma, \delta, q_0, F)$ 

- $\Sigma$  input alphabet
- Γ stack alphabet
- δ:  $Q \times \Sigma_{\varepsilon} \times \Gamma_{\varepsilon} \to \overline{\mathcal{P}(Q \times \Gamma_{\varepsilon})}$  $\delta(q, a, c) = \{(r_1, d), (r_2, e)\}$

Accept if some thread is in the accept state at the end of the input string.

**Example:** PDA for  $B = \{ww^{\mathcal{R}} | w \in \{0,1\}^*\}$  Sample input:

- Read and push input symbols.
   Nondeterministically either repeat or go to (2).
- 2) Read input symbols and pop stack symbols, compare. If ever ≠ then thread rejects.
- 3) Enter accept state if stack is empty. (do in "software")

The nondeterministic forks replicate the stack.

This language requires nondeterminism.

Our PDA model is nondeterministic.

### Converting CFGs to PDAs

**Theorem:** If A is a CFL then some PDA recognizes A

Proof: Convert A's CFG to a PDA

**IDEA:** PDA begins with starting variable and guesses substitutions.

It keeps intermediate generated strings on stack. When done, compare with input.

Input:

 $G_2$   $E \rightarrow E+T \mid T$   $T \rightarrow T \times F \mid F$   $F \rightarrow (E) \mid a$ 

#### Problem! Access below the top of stack is cheating!

Instead, only substitute variables when on the top of stack.

If a terminal is on the top of stack, pop it and compare with input. Reject if  $\neq$ .

# Converting CFGs to PDAs (contd)

**Theorem:** If A is a CFL then some PDA recognizes A

**Proof construction:** Convert the CFG for *A* to the following PDA.

- Push the start symbol on the stack.
- 2) If the top of stack is

Variable: replace with right hand side of rule (nondet choice).

**Terminal:** pop it and match with next input symbol.

If the stack is empty, accept. 3)

Example:

$$G_2$$
  $E \rightarrow E+T \mid T$   
 $T \rightarrow T \times F \mid F$   
 $F \rightarrow (E) \mid a$ 

## Equivalence of CFGs and PDAs

**Theorem:** A is a CFL iff\* some PDA recognizes A

**→** Done.

In book. You are responsible for knowing it is true, but not for knowing the proof.

\* "iff" = "if an only if" means the implication goes both ways. So we need to prove both directions: forward  $(\rightarrow)$  and reverse  $(\leftarrow)$ .

#### Check-in 4.3

Is every Regular Language also a Context Free Language?

- (a) Yes
- (b) No
- (c) Not sure

Check-in 4.3

## Recap

Regular DFA or NFA Regular expression

Context Free language PDA Context Free Grammar

## Quick review of today

- 1. Defined Context Free Grammars (CFGs) and Context Free Languages (CFLs)
- 2. Defined Pushdown Automata(PDAs)
- 3. Gave conversion of CFGs to PDAs.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 5

### Last time:

- Context free grammars (CFGs)
- Context free languages (CFLs)
- Pushdown automata (PDA)
- Converting CFGs to PDAs

### **Today:** (Sipser §2.3, §3.1)

- Proving languages not Context Free
- Turing machines
- T-recognizable and T-decidable languages

### Equivalence of CFGs and PDAs

**Recall Theorem:** A is a CFL iff some PDA recognizes A

→ Done.

✓ Need to know the fact, not the proof

#### **Corollaries:**

- 1) Every regular language is a CFL.
- 2) If A is a CFL and B is regular then  $A \cap B$  is a CFL.

#### Proof sketch of (2):

While reading the input, the finite control of the PDA for A simulates the DFA for B.

**Note 1:** If A and B are CFLs then  $A \cap B$  may not be a CFL (will show today).

Therefore the class of CFLs is not closed under  $\Omega$ .

**Note 2:** The class of CFLs is closed under  $U, \circ, *$  (see Pset 2).

### Proving languages not Context Free

Let  $B = \{0^k 1^k 2^k | k \ge 0\}$ . We will show that B isn't a CFL.

**Pumping Lemma for CFLs:** For every CFL A, there is a p such that if  $s \in A$  and  $|s| \ge p$  then s = uvxyz where

- 1)  $uv^i xy^i z \in A$  for all  $i \ge 0$
- 2)  $vy \neq \varepsilon$
- 3)  $|vxy| \le p$

Informally: All long strings in A are pumpable and stay in A.

# Pumping Lemma – Proof

**Pumping Lemma for CFLs:** For every CFL A, there is a p such that if  $s \in A$  and  $|s| \ge p$  then s = uvxyz where

- 1)  $uv^i xy^i z \in A$  for all  $i \ge 0$
- 2)  $vy \neq \varepsilon$
- 3)  $|vxy| \le p$


### Pumping Lemma – Proof details

For  $s \in A$  where  $|s| \ge p$ , we have s = uvxyz where:

- 1)  $uv^i xy^i z \in A$  for all  $i \ge 0$
- 2)  $vy \neq \varepsilon$
- 3)  $|vxy| \le p$

Let b = the length of the longest right hand side of a rule (E  $\rightarrow$  E+T)

= the max branching of the parse tree

Let h = the height of the parse tree for s. E +

A tree of height h and max branching b has at most  $b^h$  leaves. So  $|s| \le b^h$ .

Let  $p = b^{|V|} + 1$  where |V| = # variables in the grammar.

So if  $|s| \ge p > b^{|V|}$  then  $|s| > b^{|V|}$  and so h > |V|.

Thus at least |V| + 1 variables occur in the longest path. So some variable R must repeat on a path.

### Example 1 of Proving Non-CF

**Pumping Lemma for CFLs:** For every CFL A, there is a p such that if  $s \in A$  and  $|s| \ge p$  then s = uvxyz where

- 1)  $uv^i x y^i z \in A$  for all  $i \ge 0$
- 2)  $vy \neq \varepsilon$
- 3)  $|vxy| \le p$

Let 
$$B = \{0^k 1^k 2^k | k \ge 0\}$$

**Show:** *B* is not a CFL

#### Check-in 5.1

Let  $A_1 = \{0^k 1^k 2^l \mid k, l \ge 0\}$  (equal #s of 0s and 1s) Let  $A_2 = \{0^l 1^k 2^k \mid k, l \ge 0\}$  (equal #s of 1s and 2s)

Observe that PDAs can recognize  $A_1$  and  $A_2$ . What can we now conclude?

- a) The class of CFLs is not closed under intersection.
- b) The Pumping Lemma shows that  $A_1 \cup A_2$  is not a CFL .
- c) The class of CFLs is closed under complement.

$$S = 00 \cdots 0011 \cdots 1122 \cdots 22$$

$$u \mid v \mid x \mid y \mid z$$

$$\bullet \leq p \Rightarrow$$

### Example 2 of Proving Non-CF

**Pumping Lemma for CFLs:** For every CFL A, there is a p such that if  $s \in A$  and  $|s| \ge p$  then s = uvxyz where

- 1)  $uv^i x y^i z \in A$  for all  $i \ge 0$
- 2)  $vy \neq \varepsilon$
- 3)  $|vxy| \le p$

Let 
$$F = \{ww | w \in \Sigma^*\}$$
.  $\Sigma = \{0,1\}$ .

**Show:** F is not a CFL.

Assume (for contradiction) that F is a CFL.

The CFL pumping lemma gives p as above. Need to choose  $s \in F$ . Which s?

Try 
$$s_1 = 0^p 10^p 1 \in F$$
.

Try 
$$s_2 = 0^p 1^p 0^p 1^p \in F$$
.

Show  $s_2$  cannot be pumped  $s_2 = uvxyz$  satisfying the 3 conditions.

Condition 3 implies that vxy does not overlap two runs of 0s or two runs of 1s.

Therefore, in  $uv^2xy^2z$ , two runs of 0s or two runs of 1s have unequal length.

So  $uv^2xy^2z \notin F$  violating Condition 1. Contradiction! Thus F is not a CFL.

$$s_1 = \frac{000 \cdots 001000 \cdots 001}{u \quad |v| x| y| \quad z}$$

$$\bullet \leq v \bullet$$

$$s_2 = \underbrace{0 \cdots 01 \cdots 10 \cdots 01 \cdots 1}_{u \quad v \mid x \mid y \mid z}$$

$$\bullet < v \bullet$$

# Turing Machines (TMs)

- 1) Head can read and write
- 2) Head is two way (can move left or right)
- 3) Tape is infinite (to the right)
- 4) Infinitely many blanks "—" follow input
- 5) Can accept or reject any time (not only at end of input)

### TM – example

TM recognizing  $B = \{a^k b^k c^k | k \ge 0\}$ 

- 1) Scan right until while checking if input is in a\*b\*c\*, reject if not.
- 2) Return head to left end.
- 3) Scan right, crossing off single a, b, and c.
- 4) If the last one of each symbol, accept.
- 5) If the last one of some symbol but not others, reject.
- 6) If all symbols remain, return to left end and repeat from (3).

#### Check-in 5.2

How do we get the effect of "crossing off" with a Turing machine?

- a) We add that feature to the model.
- b) We use a tape alphabet  $\Gamma = \{a, b, c, \not a, \not a, \not c, \neg \}$ .
- c) All Turing machines come with an eraser.

### TM – Formal Definition

Defn: A <u>Turing Machine</u> (TM) is a 7-tuple  $(Q, \Sigma, \Gamma, \delta, q_0, q_{acc}, q_{rej})$ 

- $\Sigma$  input alphabet
- $\Gamma$  tape alphabet  $(\Sigma \subseteq \Gamma)$
- δ: Q×Γ → Q×Γ× {L, R} (L = Left, R = Right) δ(q, a) = (r, b, R)

On input w a TM M may halt (enter  $q_{\rm acc}$  or  $q_{\rm rej}$ ) or M may run forever ("loop").

So *M* has 3 possible outcomes for each input *w*:

- 1. Accept w (enter  $q_{acc}$ )
- 2. Reject w by halting (enter  $q_{rej}$ )
- 3. Reject w by looping (running forever)

### Check-in 5.3

This Turing machine model is deterministic. How would we change it to be nondeterministic?

- a) Add a second transition function.
- b) Change  $\delta$  to be  $\delta$ : Q× $\Gamma$   $\rightarrow$   $\mathcal{P}(Q \times \Gamma \times \{L, R\})$
- c) Change the tape alphabet  $\Gamma$  to be infinite.

# TM Recognizers and Deciders

Let M be a TM. Then  $L(M) = \{w \mid M \text{ accepts } w\}$ .

Say that M recognizes A if A = L(M).

**Defn:** A is <u>Turing-recognizable</u> if A = L(M) for some TM M.

**Defn:** TM *M* is a <u>decider</u> if *M* halts on all inputs.

Say that M decides A if A = L(M) and M is a decider.

**Defn:** A is <u>Turing-decidable</u> if A = L(M) for some TM decider M.

### Quick review of today

- 1. Proved the CFL Pumping Lemma as a tool for showing that languages are not context free.
- 2. Defined Turing machines (TMs).
- 3. Defined TM deciders (halt on all inputs).
- 4. T-recognizable and T-decidable languages.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.404/6.840 Lecture 6

#### Last time:

- Proving languages not Context Free
- Turing machines
- Recognizers and deciders
- T-recognizable and T-decidable languages

#### **Today:** (Sipser §3.2 – §3.3)

- Equivalence of variants of the Turing machine model
  - a. Multi-tape TMs
  - b. Nondeterministic TMs
  - c. Enumerators
- Church-Turing Thesis
- Notation for encodings and TMs

## Turing machine model – review

On input w a TM M may halt (enter  $q_{\rm acc}$  or  $q_{\rm rej}$ ) or loop (run forever).

So *M* has 3 possible outcomes for each input *w*:

- 1. Accept w (enter  $q_{acc}$ )
- 2. Reject w by halting (enter  $q_{rej}$ )
- 3. <u>Reject</u> w by looping (running forever)

A is <u>T-recognizable</u> if A = L(M) for some TM M.

A is <u>T-decidable</u> if A = L(M) for some TM decider M.

halts on all inputs

Turing machines model general-purpose computation.

Q: Why pick this model?

A: Choice of model doesn't matter.
All reasonable models are equivalent in power.

Virtues of TMs: simplicity, familiarity.

## Multi-tape Turing machines

**Theorem:** A is T-recognizable iff some multi-tape TM recognizes A

**Proof:**  $(\rightarrow)$  immediate.  $(\leftarrow)$  convert multi-tape to single tape:

S simulates M by storing the contents of multiple tapes on a single tape in "blocks". Record head positions with dotted symbols.

#### Some details of S:

- 1) To simulate each of M's steps
  - a. Scan entire tape to find dotted symbols.
  - b. Scan again to update according to M's  $\delta$ .
  - c. Shift to add room as needed.
- 2) Accept/reject if *M* does.

## Nondeterministic Turing machines

A <u>Nondeterministic TM</u> (NTM) is similar to a Deterministic TM except for its transition function  $\delta \colon \mathbb{Q} \times \Gamma \to \mathcal{P}(\mathbb{Q} \times \Gamma \times \{L, R\})$ .

**Theorem:** A is T-recognizable iff some NTM recognizes A

**Proof:**  $(\rightarrow)$  immediate.  $(\leftarrow)$  convert NTM to Deterministic TM.

Nondeterministic computation tree for N on input w.

*M* simulates *N* by storing each thread's tape in a separate "block" on its tape.

Also need to store the head location, and the state for each thread, in the block.

If a thread forks, then M copies the block.

If a thread accepts then M accepts.

## **Turing Enumerators**

**Defn:** A <u>Turing Enumerator</u> is a deterministic TM with a printer.

It starts on a blank tape and it can print strings  $w_1$ ,  $w_2$ ,  $w_3$ , ... possibly going forever.

Its language is the set of all strings it prints. It is a generator, not a recognizer.

For enumerator E we say  $L(E) = \{w \mid E \text{ prints } w\}$ .

**Theorem:** A is T-recognizable iff A = L(E) for some T-enumerator E.

#### Check-in 6.1

E

When converting TM M to enumerator E, does E always print the strings in **string order**?

- a) Yes.
- b) No.

**Proof:** ( $\rightarrow$ ) Convert TM M to equivalent enumerator E.

 $E= \mbox{Simulate } M \mbox{ on each } w_i \mbox{ in } \Sigma^* = \{\varepsilon, 0, 1, 00, 01, 10, \dots\}$ 

If M accepts  $w_i$  then print  $w_i$ .

Continue with next  $w_i$ .

*Problem:* What if M on  $w_i$  loops?

Fix: Simulate M on  $w_1$ ,  $w_2$ , ...,  $w_i$  for i steps, for i = 1,2,...Print those  $w_i$  which are accepted.

Image of the printer © Source unknown. All rights reserved. This content is excluded from our Creative Commons license. For more information, see <a href="https://ocw.mit.edu/fairuse">https://ocw.mit.edu/fairuse</a>.

Check-in 6.1

## Church-Turing Thesis ~1936

Alonzo Church 1903–1995

Algorithm

Intuitive

= | |

Turing machine

**Formal** 

Instead of Turing machines, can use any other "reasonable" model

#### Check-in 6.2

Which is the following is true about Alan Turing? Check all that apply.

- a) Broke codes for England during WW2.
- b) Worked in AI.
- c) Worked in Biology.
- d) Was imprisoned for being gay.
- e) Appears on a British banknote.

Alan Turing 1912–1954

Will appear in 2021

Check-in 6.2

## Hilbert's 10<sup>th</sup> Problem

#### In 1900 David Hilbert posed 23 problems

- #1) Problem of the continuum (Does set A exist where  $|\mathbb{N}| < |A| < |\mathbb{R}|$ ?).
- #2) Prove that the axioms of mathematics are consistent.
- #10) Give an algorithm for solving Diophantine equations.

#### **Diophantine equations:**

Equations of polynomials where solutions must be integers.

Example:  $3x^2 - 2xy - y^2z = 7$  solution: x = 1, y = 2, z = -2

Let  $D = \{p \mid \text{polynomial } p(x_1, x_2, ..., x_k) = 0 \text{ has a solution in integers} \}$ 

Hilbert's  $10^{th}$  problem: Give an algorithm to decide D.

Matiyasevich proved in 1970: *D* is not decidable.

David Hilbert 1862—1943

Note: *D* is T-recognizable.

© Source unknown. All rights reserved. This content is excluded from our Creative Commons license. For more information, see <a href="https://ocw.mit.edu/fairuse">https://ocw.mit.edu/fairuse</a>.

## Notation for encodings and TMs

#### **Notation for encoding objects into strings**

- If O is some object (e.g., polynomial, automaton, graph, etc.), we write  $\langle O \rangle$  to be an encoding of that object into a string.
- If  $O_1, O_2, ..., O_k$  is a list of objects then we write  $\langle O_1, O_2, ..., O_k \rangle$ to be an encoding of them together into a single string.

### Notation for writing Check-in 6.3

# transition function, et a)

M = "On input w

We will use high-level If x and y are strings, would xy be a good choice knowing that we could for their encoding  $\langle x, y \rangle$  into a single string?

- Yes.
- No.

[English description of the algorithm]"

## TM – example revisited

TM M recognizing  $B = \{a^k b^k c^k | k \ge 0\}$ 

M = "On input w

- 1. Check if  $w \in a^*b^*c^*$ , reject if not.
- 2. Count the number of a's, b's, and c's in w.
- 3. Accept if all counts are equal; reject if not."

High-level description is ok.

You do not need to manage tapes, states, etc...

## Problem Set 2

#5) Show  ${\it C}$  is T-recognizable iff there is a decidable  ${\it D}$  where

$$C = \{ x | \exists y \langle x, y \rangle \in D \} \quad x, y \in \Sigma^*$$

 $\langle x, y \rangle$  is an encoding of the pair of strings x and y into a single string. Think of D as a collection of pairs of strings.

## Quick review of today

- 1. We showed that various TM variants (multi-tape, nondeterministic, enumerator) are all equivalent to the single-tape model.
- 2. Concluded that all "reasonable" models with unrestricted memory access are equivalent.
- 3. Discussed the Church-Turing Thesis: Turing machines are equivalent to "algorithms".
- 4. Notation for encoding objects and describing TMs.
- 5. Discussed Pset 2 Problem 5.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 7

### Last time:

- Equivalence of variants of the Turing machine model
  - a. Multi-tape TMs
  - b. Nondeterministic TMs
  - c. Enumerators
- Church-Turing Thesis
- Notation for encodings and TMs

### Today: (Sipser §4.1)

- Decision procedures for automata and grammars

# TMs and Encodings – review

A TM has 3 possible outcomes for each input w:

- 1.  $\underline{Accept}$  w (enter  $q_{acc}$ )
- 2. Reject w by halting (enter  $q_{\rm rej}$ )
- 3. <u>Reject</u> w by looping (running forever)

```
A is <u>T-recognizable</u> if A = L(M) for some TM M.
A is <u>T-decidable</u> if A = L(M) for some TM decider M.
halts on all inputs
```

 $\langle O_1, O_2, \dots, O_k \rangle$  encodes objects  $O_1, O_2, \dots, O_k$  as a single string.

Notation for writing a TM M is

M = "On input w [English description of the algorithm]"

## Acceptance Problem for DFAs

Let  $A_{DFA} = \{\langle B, w \rangle | B \text{ is a DFA and } B \text{ accepts } w\}$ 

Theorem:  $A_{DFA}$  is decidable

Proof: Give TM  $D_{A-DFA}$  that decides  $A_{DFA}$ .

 $D_{A-DFA}$  = "On input s

1. Check that s has the form  $\langle B, w \rangle$  where B is a DFA and w is a string; reject if not.

Shorthand: On input  $\langle B, w \rangle$ 

- 2. Simulate the computation of B on w.
- 3. If *B* ends in an accept state then *accept*. If not then *reject*."

work tape with current state and input head location

## Acceptance Problem for NFAs

Let  $A_{NFA} = \{\langle B, w \rangle | B \text{ is a NFA and } B \text{ accepts } w\}$ 

Theorem:  $A_{NFA}$  is decidable

Proof: Give TM  $D_{A-NFA}$  that decides  $A_{NFA}$ .

 $D_{A-NFA}$  = "On input  $\langle B, w \rangle$ 

- 1. Convert NFA B to equivalent DFA B'.
- 2. Run TM  $D_{A-DFA}$  on input  $\langle B', w \rangle$ . [Recall that  $D_{A-DFA}$  decides  $A_{DFA}$ ]
- 3. Accept if  $D_{A-DFA}$  accepts. Reject if not."

**New element:** Use conversion construction and previously constructed TM as a subroutine.

# **Emptiness Problem for DFAs**

Let  $E_{DFA} = \{\langle B \rangle | B \text{ is a DFA and } L(B) = \emptyset \}$ 

Theorem:  $E_{DFA}$  is decidable

Proof: Give TM  $D_{\mathrm{E-DFA}}$  that decides  $E_{\mathrm{DFA}}$  .

 $D_{\text{E-DFA}}$  = "On input  $\langle B \rangle$  [IDEA: Check for a path from start to accept.]

- 1. Mark start state.
- Repeat until no new state is marked:
   Mark every state that has an incoming arrow from a previously marked state.
- Accept if no accept state is marked.
   Reject if some accept state is marked."

## Equivalence problem for DFAs

Let  $EQ_{DFA} = \{\langle A, B \rangle | A \text{ and } B \text{ are DFAs and } L(A) = L(B) \}$ 

Theorem:  $EQ_{DEA}$  is decidable

Proof: Give TM  $D_{\mathrm{EQ-DFA}}$  that decides  $EQ_{\mathrm{DFA}}$  .

### Check-in 7.1

Let  $EQ_{REX} = \{\langle R_1, R_2 \rangle | R_1 \text{ and } R_2 \text{ are regular expressions and } L(R_1) = L(R_2) \}$ 

Can we now conclude that  $EQ_{REX}$  is decidable?

- a) Yes, it follows immediately from things we've already shown.
- b) Yes, but it would take significant additional work.
- c) No, intersection is not a regular operation.

## Acceptance Problem for CFGs

Let  $A_{CFG} = \{\langle G, w \rangle | G \text{ is a CFG and } w \in L(G)\}$ 

**Theorem:**  $A_{\text{CFG}}$  is decidable

**Proof:** Give TM  $D_{A-CFG}$  that decides  $A_{CFG}$ .

 $D_{A-CFG}$  = "On input  $\langle G, w \rangle$ 

- 1. Convert G into CNF.
- 2. Try all derivations of length 2|w| 1.
- 3. Accept if any generate w. Reject if not.

#### Check-in 7.2

Can we conclude that  $A_{PDA}$  is decidable?

- a) Yes.
- b) No, PDAs may be nondeterministic.
- c) No, PDAs may not halt.

Recall Chomsky Normal Form (CNF) only allows rules:

 $A \rightarrow BC$ 

 $B \rightarrow b$ 

**Lemma 1:** Can convert every CFG into CNF. Proof and construction in book.

**Lemma 2:** If H is in CNF and  $w \in L(H)$  then every derivation of w has 2|w|-1 steps. Proof: exercise.

# **Emptiness Problem for CFGs**

```
Let E_{\text{CFG}} = \{\langle G \rangle | G \text{ is a CFG and } L(G) = \emptyset \}
```

Theorem:  $E_{CFG}$  is decidable

Proof:

 $D_{E-CFG}$  = "On input  $\langle G \rangle$  [IDEA: work backwards from terminals]

- 1. Mark all occurrences of terminals in *G*.
- 2. Repeat until no new variables are marked Mark all occurrences of variable A if  $A \to B_1 B_2 \cdots B_k \text{ is a rule and all } B_i \text{ were already marked.}$
- 3. *Reject* if the start variable is marked. *Accept* if not."

 $S \rightarrow RTa$ 

 $R \rightarrow Tb$ 

 $T \rightarrow a$ 

## Equivalence Problem for CFGs

Let  $EQ_{CFG} = \{\langle G, H \rangle | G, H \text{ are CFGs and } L(G) = L(H) \}$ 

Theorem:  $EQ_{CFG}$  is NOT decidable

Proof: Next week.

Let  $AMBIG_{CFG} = \{\langle G \rangle | G \text{ is an ambiguous CFG } \}$ 

### Check-in 7.3

Why can't we use the same technique we used to show  $EQ_{\mathrm{DFA}}$  is decidable to show that  $EQ_{\mathrm{CFG}}$  is decidable?

- a) Because CFGs are generators and DFAs are recognizers.
- b) Because CFLs are closed under union.
- c) Because CFLs are not closed under complementation and intersection.

## Acceptance Problem for TMs

Let  $A_{\text{TM}} = \{\langle M, w \rangle | M \text{ is a TM and } M \text{ accepts } w\}$ 

Theorem:  $A_{TM}$  is not decidable

Proof: Thursday.

Theorem:  $A_{TM}$  is T-recognizable

Proof: The following TM U recognizes  $A_{\rm TM}$ 

U = "On input  $\langle M, w \rangle$ 

- 1. Simulate M on input w.
- 2. *Accept* if *M* halts and accepts.
- 3. *Reject* if *M* halts and rejects.
- 4. Reject if M never halts." Not a legal TM action.

Turing's original "Universal Computing Machine"

Von Neumann said U inspired the concept of a stored program computer.

# Quick review of today

1. We showed the decidability of various problems about automata and grammars:

$$A_{\rm DFA}$$
 ,  $A_{\rm NFA}$  ,  $E_{\rm DFA}$  ,  $EQ_{\rm DFA}$  ,  $A_{\rm CFG}$  ,  $E_{\rm DFA}$ 

2. We showed that  $A_{\rm TM}$  is T-recognizable.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.404/6.840 Lecture 8

#### Last time:

- Decision procedures for automata and grammars  $A_{\rm DFA}$  ,  $A_{\rm NFA}$  ,  $E_{\rm DFA}$  ,  $EQ_{\rm DFA}$  ,  $A_{\rm CFG}$  ,  $E_{\rm CFG}$  are decidable  $A_{\rm TM}$  is T-recognizable

#### Today: (Sipser §4.2)

- $A_{\mathrm{TM}}$  is undecidable
- The diagonalization method
- $\overline{A_{\rm TM}}$  is T-unrecognizable
- The reducibility method
- Other undecidable languages

## Recall: Acceptance Problem for TMs

Let  $A_{TM} = \{\langle M, w \rangle | M \text{ is a TM and } M \text{ accepts } w\}$ 

**Today's Theorem:**  $A_{\text{TM}}$  is not decidable

Proof uses the diagonalization method, so we will introduce that first.

### The Size of Infinity

How to compare the relative sizes of infinite sets?

Cantor (~1890s) had the following idea.

**Defn:** Say that set A and B have the same size if there is a one-to-one and onto function  $f: A \to B$ 

$$x \neq y \rightarrow$$
 Range  $(f) = B$   $f(x) \neq f(y)$  "surjective" We call such an  $f$  a 1-1 correspondence

Informally, two sets have the same size if we can pair up their members.

This definition works for finite sets.

Apply it to infinite sets too.

© Source unknown. All rights reserved. This content is excluded from our Creative Commons license. For more information, see https://ocw.mit.edu/fairuse.

### **Countable Sets**

Let 
$$\mathbb{N} = \{1,2,3,...\}$$
 and let  $\mathbb{Z} = \{..., -2, -1,0,1,2,...\}$ 

Show  $\mathbb N$  and  $\mathbb Z$  have the same size

$$\begin{array}{c|c}
n & f(n) \\
\mathbb{N} & \mathbb{Z}
\end{array}$$

Let 
$$\mathbb{Q}^+ = \{ m/n \mid m, n \in \mathbb{N} \}$$

Show  $\mathbb N$  and  $\mathbb Q^+$  have the same size

| $\mathbb{Q}^+$ | 1   | 2   | 3   | 4   |  |
|----------------|-----|-----|-----|-----|--|
| 1              | 1/1 | 1/2 | 1/3 | 1/4 |  |
| 2              | 2/1 | 2/2 | 2/3 | 2/4 |  |
| 3              | 3/1 | 3/2 | 3/3 | 3/4 |  |
| 4              | 4/1 | 4/2 | 4/3 | 4/4 |  |
| :              |     | :   |     |     |  |

**Defn:** A set is <u>countable</u> if it is finite or it has the same size as  $\mathbb{N}$ .

Both  $\mathbb{Z}$  and  $\mathbb{Q}^+$  are countable.

## ℝ is Uncountable – Diagonalization

Let  $\mathbb{R} = \text{all real numbers (expressible by infinite decimal expansion)}$ 

Theorem: R is uncountable

Proof by contradiction via diagonalization: Assume  $\mathbb R$  is countable

So there is a 1-1 correspondence  $f: \mathbb{N} \to \mathbb{R}$ 

| n | f(n)            |
|---|-----------------|
| 1 |                 |
| 2 |                 |
| 3 |                 |
| 4 |                 |
| 5 |                 |
| 6 |                 |
| 7 |                 |
| : | Diagonalization |

Demonstrate a number  $x \in \mathbb{R}$  that is missing from the list.

$$x = 0$$
.

differs from the  $n^{\rm th}$  number in the  $n^{\rm th}$  digit so cannot be the  $n^{\rm th}$  number for any n.

Hence x is not paired with any n. It is missing from the list.

Therefore f is not a 1-1 correspondence.

### R is Uncountable – Corollaries

#### Let $\mathcal{L} = \text{all languages}$

**Corollary 1:**  $\mathcal{L}$  is uncountable

Proof: There's a 1-1 correspondence from  $\mathcal{L}$  to  $\mathbb{R}$  so they are the same size.

**Observation:**  $\Sigma^* = \{\varepsilon, 0, 1, 00, 01, 10, 11, 000, ...\}$  is countable.

Let  $\mathcal{M}=$  all Turing machines **Observation:**  $\mathcal{M}$  is countable. Because  $\{\langle M \rangle | M \text{ is a TM}\} \subseteq \Sigma^*$ .

**Corollary 2:** Some language is not decidable. Because there are more languages than TMs.

We will show some specific language  $A_{\rm TM}$  is not decidable.

#### Check-in 8.1

Hilbert's  $1^{st}$  question asked if there is a set of intermediate size between  $\mathbb{N}$  and  $\mathbb{R}$ . Gödel and Cohen showed that we cannot answer this question by using the standard axioms of mathematics. How can we interpret their conclusion?

- (a) We need better axioms to describe reality.
- (b) Infinite sets have no mathematical reality so Hilbert's 1<sup>st</sup> question has no answer.

Check-in 8.1

### $A_{\rm TM}$ is undecidable

Recall  $A_{TM} = \{\langle M, w \rangle | M \text{ is a TM and } M \text{ accepts } w\}$ 

Theorem:  $A_{TM}$  is not decidable

Proof by contradiction: Assume some TM H decides  $A_{\rm TM}$ .

So 
$$H$$
 on  $\langle M, w \rangle = \begin{cases} Accept & \text{if } M \text{ accepts } w \\ Reject & \text{if not} \end{cases}$ 

Use *H* to construct TM *D* 

$$D = \text{"On input } \langle M \rangle$$

- 1. Simulate H on input  $\langle M, \langle M \rangle \rangle$
- 2. Accept if H rejects. Reject if H accepts."

 $\overline{D}$  accepts  $\langle M \rangle$  iff M doesn't accept  $\langle M \rangle$ . D accepts  $\langle D \rangle$  iff D doesn't accept  $\langle D \rangle$ . Contradiction.

#### Why is this proof a diagonalization?

All All TM descriptions:

TMs  $\langle M_1 \rangle \langle M_2 \rangle \langle M_3 \rangle \langle M_4 \rangle \dots \langle D \rangle$   $M_1$   $M_2$   $M_3$   $M_4$   $\vdots$  D

#### Check-in 8.2

Recall the Queue Automaton (QA) defined in Pset 2. It is similar to a PDA except that it is deterministic and it has a queue instead of a stack.

Let  $A_{QA} = \{\langle B, w \rangle | B \text{ is a QA and } B \text{ accepts } w\}$ 

Is  $A_{OA}$  decidable?

- (a) Yes, because QA are similar to PDA and  $A_{\rm PDA}$  is decidable.
- (b) No, because "yes" would contradict results we now know.
- (c) We don't have enough information to answer this question.

# $A_{\rm TM}$ is T-unrecognizable

Theorem: If A and  $\overline{A}$  are T-recognizable then A is decidable

Proof: Let TM  $M_1$  and  $M_2$  recognize A and  $\overline{A}$ .

Construct TM T deciding A.

T = "On input w

- 1. Run  $M_1$  and  $M_2$  on w in parallel until one accepts.
- 2. If  $M_1$  accepts then accept. If  $M_2$  accepts then reject."

Corollary:  $A_{TM}$  is T-unrecognizable

Proof:  $A_{\text{TM}}$  is T-recognizable but also undecidable

#### Check-in 8.3

From what we've learned, which closure properties can we prove for the class of T-recognizable languages? Choose all that apply.

- (a) Closed under union.
- (b) Closed under intersection.
- (c) Closed under complement.
- (d) Closed under concatenation.
- (e) Closed under star.

Check-in 8.3

### The Reducibility Method

Use our knowledge that  $A_{\rm TM}$  is undecidable to show other problems are undecidable.

Defn:  $HALT_{TM} = \{\langle M, w \rangle | M \text{ halts on input } w \}$ 

Theorem:  $HALT_{TM}$  is undecidable

Proof by contradiction, showing that  $A_{TM}$  is reducible to  $HALT_{TM}$ :

Assume that  $HALT_{TM}$  is decidable and show that  $A_{TM}$  is decidable (false!).

Let TM R decide  $HALT_{TM}$ .

Construct TM S deciding  $A_{TM}$ .

S = "On input  $\langle M, w \rangle$ 

- 1. Use *R* to test if *M* on *w* halts. If not, reject.
- 2. Simulate M on w until it halts (as guaranteed by R).
- 3. If *M* has accepted then *accept*. If *M* has rejected then *reject*.

TM S decides  $A_{\rm TM}$ , a contradiction. Therefore  $HALT_{\rm TM}$  is undecidable.

### Quick review of today

- 1. Showed that  $\mathbb{N}$  and  $\mathbb{R}$  are not the same size to introduce the Diagonalization Method.
- 2.  $A_{\text{TM}}$  is undecidable.
- 3. If  $\overline{A}$  and  $\overline{A}$  are T-recognizable then A is decidable.
- 4.  $A_{\text{TM}}$  is T-unrecognizable.
- 5. Introduced the Reducibility Method to show that  $HALT_{\rm TM}$  is undecidable.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 9

#### Last time:

- $A_{\mathrm{TM}}$  is undecidable
- The diagonalization method
- $\overline{A_{\mathrm{TM}}}$  is T-unrecognizable
- The Reducibility Method, preview

### **Today:** (Sipser §5.1, §5.3)

- The Reducibility Method for proving undecidability and T-unrecognizability.
- General reducibility
- Mapping reducibility

## The Reducibility Method

If we know that some problem (say  $A_{\rm TM}$ ) is undecidable, we can use that to show other problems are undecidable.

**Defn**:  $HALT_{TM} = \{\langle M, w \rangle | M \text{ halts on input } w\}$ 

**Recall Theorem**:  $HALT_{TM}$  is undecidable

Proof by contradiction, showing that  $A_{TM}$  is reducible to  $HALT_{TM}$ :

Assume that  $HALT_{TM}$  is decidable and show that  $A_{TM}$  is decidable (false!).

Let TM R decide  $HALT_{TM}$ .

Construct TM S deciding  $A_{TM}$ .

- S = "On input  $\langle M, w \rangle$ 
  - 1. Use R to test if M on w halts. If not, reject.
  - 2. Simulate *M* on *w* until it halts (as guaranteed by *R*).
  - 3. If *M* has accepted then *accept*. If *M* has rejected then *reject*.

TM S decides  $A_{\rm TM}$ , a contradiction. Therefore  $HALT_{\rm TM}$  is undecidable.

### Reducibility – Concept

If we have two languages (or problems) A and B, then A is reducible to B means that we can use B to solve A.

**Example 1:** Measuring the area of a rectangle is reducible to measuring the lengths of its sides.

**Example 2:** We showed that  $A_{\rm NFA}$  is reducible to  $A_{\rm DFA}$ .

**Example 3:** From Pset 2, *PUSHER* is reducible to  $E_{\rm CFG}$ . (Idea- Convert push states to accept states.)

If A is reducible to B then solving B gives a solution to A.

- then B is easy  $\rightarrow A$  is easy.
- then A is hard  $\rightarrow B$  is hard.

this is the form we will use

#### Check-in 9.1

Is Biology reducible to Physics?

- (a) Yes, all aspects of the physical world may be explained in terms of Physics, at least in principle.
- (b) No, some things in the world, maybe life, the brain, or consciousness, are beyond the realm pf Physics.
- (c) I'm on the fence on this question!

## $E_{\rm TM}$ is undecidable

Let  $E_{\text{TM}} = \{ \langle M \rangle | M \text{ is a TM and } L(M) = \emptyset \}$ 

### **Theorem:** $E_{TM}$ is undecidable

Proof by contradiction. Show that  $A_{\rm TM}$  is reducible to  $E_{\rm TM}$ .

Assume that  $E_{\rm TM}$  is decidable and show that  $A_{\rm TM}$  is decidable (false!).

Let TM R decide  $E_{\rm TM}$ .

Construct TM S deciding  $A_{TM}$ .

$$S =$$
 "On input  $\langle M, w \rangle$ 

- 1. Transform M to new TM  $M_w =$  "On input x
  - 1. If  $x \neq w$ , reject.
  - 2. else run *M* on *w*
  - 3. *Accept* if *M* accepts."
- 2. Use *R* to test whether  $L(M_w) = \emptyset$
- 3. If YES [so *M* rejects *w*] then *reject*. If NO [so *M* accepts *w*] then *accept*.

 $M_w$  works like M except that it always rejects strings x where  $x \neq w$ .

So 
$$L(M_w) = \begin{cases} \{w\} & \text{if } M \text{ accepts } w \\ \emptyset & \text{if } M \text{ rejects } w \end{cases}$$

### Mapping Reducibility

**Defn:** Function  $f: \Sigma^* \to \Sigma^*$  is <u>computable</u> if there is a TM F where F on input W halts with f(W) on its tape, for all strings W.

**Defn:** <u>A</u> is mapping-reducible to <u>B</u>  $(A \leq_m B)$  if there is a computable function f where  $w \in A$  iff  $f(w) \in B$ .

Example:  $A_{\text{TM}} \leq_{\text{m}} \overline{E_{\text{TM}}}$ 

The computable reduction function f is  $f(\langle M, w \rangle) = \langle M_w \rangle$  Recall TN

Because  $\langle M, w \rangle \in A_{\mathrm{TM}}$  iff  $\langle M_w \rangle \in \overline{E_{\mathrm{TM}}}$ 

( M accepts w iff  $L(\langle M_w \rangle) \neq \emptyset$  )

Recall TM  $M_w$  = "On input x

- 1. If  $x \neq w$ , reject.
- 2. else run *M* on *w*
- 3. *Accept* if *M* accepts."

### Mapping Reductions - properties

**Theorem:** If  $A \leq_{\mathbf{m}} B$  and B is decidable then so is A

Proof: Say TM R decides B.

Construct TM *S* deciding *A*:

- 1. Compute f(w)
- 2. Run R on f(w) to test if  $f(w) \in B$
- 3. If R halts then output same result."

**Corollary:** If  $A \leq_{\mathbf{m}} B$  and A is undecidable then so is B

**Theorem:** If  $A \leq_{\mathbf{m}} B$  and B is T-recognizable then so is A

Proof: Same as above.

**Corollary:** If  $A \leq_{\mathbf{m}} B$  and A is T-unrecognizable then so is B

#### Check-in 9.2

• B

Suppose  $A \leq_{\mathrm{m}} B$ .

What can we conclude?

Check all that apply.

- (a)  $B \leq_{\mathbf{m}} A$
- (b)  $A \leq_{\mathsf{m}} B$
- (c) None of the above

Check-in 9.2

## Mapping vs General Reducibility

Mapping Reducibility of A to B: Translate A-questions to B-questions.

- A special type of reducibility
- Useful to prove T-unrecognizability

(General) Reducibility of A to B: Use B solver to solve A.

- May be conceptually simpler
- Useful to prove undecidability

### Noteworthy difference:

- A is reducible to  $\overline{A}$
- A may not be mapping reducible to A. For example  $\overline{A}_{TM} \not \leq_m A_{TM}$

#### Check-in 9.3

We showed that if  $A \leq_m B$  and B is T-recognizable then so is A.

Is the same true if we use general reducibility instead of mapping reducibility?

- (a) Yes
- (b) No

Check-in 9.3

### Reducibility – Templates

### To prove *B* is undecidable:

- Show undecidable A is reducible to B. (often A is  $A_{\rm TM}$ )
- Template: Assume TM R decides B.

  Construct TM S deciding A. Contradiction.

### To prove B is T-unrecognizable:

- Show T-unrecognizable A is mapping reducible to B. (often A is  $A_{TM}$ )
- Template: give reduction function f.

# $E_{\rm TM}$ is T-unrecognizable

Recall  $E_{TM} = \{\langle M \rangle | M \text{ is a TM and } L(M) = \emptyset \}$ 

**Theorem:**  $E_{\text{TM}}$  is T-unrecognizable

Proof: Show  $\overline{A_{\rm TM}} \leq_{\rm m} E_{\rm TM}$ 

Reduction function:  $f(\langle M, w \rangle) = \langle M_w \rangle$  Recall TM  $M_w =$  "On input x

Explanation:  $\langle M, w \rangle \in \overline{A_{\text{TM}}}$  iff  $\langle M_w \rangle \in E_{\text{TM}}$ 

M rejects w iff  $L(\langle M_w \rangle) = \emptyset$ 

1 If  $x \neq w$  rois

1. If  $x \neq w$ , reject.

2. else run *M* on *w* 

3. Accept if M accepts."

# $EQ_{\mathrm{TM}}$ and $\overline{EQ_{\mathrm{TM}}}$ are T-unrecognizable

 $EQ_{\mathrm{TM}} = \{\langle M_1, M_2 \rangle | \ M_1 \ \mathrm{and} \ M_2 \ \mathrm{are} \ \mathrm{TMs} \ \mathrm{and} \ L(M_1) = L(M_2) \ \}$ 

**Theorem:** Both  $EQ_{\mathrm{TM}}$  and  $EQ_{\mathrm{TM}}$  are T-unrecognizable

Proof: (1)  $A_{TM} \leq_m EQ_{TM}$ 

(2)  $A_{\text{TM}} \leq_{\text{m}} EQ_{\text{TM}}$ 

For any w let  $T_w =$  "On input x  $T_w$  acts on all inputs the way M acts on w.

- 1. Ignore x.
- 2. Simulate *M* on *w*."
- (1) Here we give f which maps  $\overline{A_{\rm TM}}$  problems (of the form  $\langle M, w \rangle$ ) to  $EQ_{\rm TM}$  problems (of the form  $\langle T_1, T_2 \rangle$ ).

 $f(\langle M, w \rangle) = \langle T_w, T_{\text{reject}} \rangle$   $T_{\text{reject}}$  is a TM that always rejects.

(2) Similarly  $f(\langle M, w \rangle) = \langle T_w, T_{\text{accept}} \rangle$   $T_{\text{accept}}$  always accepts.

### Reducibility terminology

### Why do we use the term "reduce"?

When we reduce A to B, we show how to solve A by using B and conclude that A is no harder than B. (suggests the  $\leq_m$  notation)

Possibility 1: We bring A's difficulty down to B's difficulty.

Possibility 2: We bring B's difficulty up to A's difficulty.

## Quick review of today

- 1. Introduced The Reducibility Method to prove undecidability and T-unrecognizability.
- 2. Defined mapping reducibility as a type of reducibility.
- 3.  $E_{TM}$  is undecidable.
- 4.  $E_{\text{TM}}$  is T-unrecognizable.
- 5.  $EQ_{\rm TM}$  and  $\overline{EQ_{\rm TM}}$  are T-unrecognizable.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.404/6.840 Lecture 10

#### Last time:

- The Reducibility Method for proving undecidability and T-unrecognizability
- General reducibility
- Mapping reducibility

#### Today: (Sipser §5.2)

- The Computation History Method for proving undecidability
- The Post Correspondence Problem is undecidable
- Linearly bounded automata
- Undecidable problems about LBAs and CFGs

## Remember

To prove some language B is undecidable, show that  $A_{\rm TM}$  (or any known undecidable language) is reducible to B.

#### Revisit Hilbert's 10th Problem

Recall  $D = \{\langle p \rangle | \text{ polynomial } p(x_1, x_2, \dots, x_k) = 0 \text{ has integer solution} \}$ 

Hilbert's  $10^{th}$  problem (1900): Is D decidable?

Theorem (1971): No

Proof: Show  $A_{TM}$  is reducible to D. [would take entire semester]

Do toy problem instead which has a similar proof method.

Toy problem: The Post Correspondence Problem.

Method: The Computation History Method.

#### Post Correspondence Problem

Given a collection of pairs of strings as dominoes:

$$P = \left\{ \begin{bmatrix} t_1 \\ b_1 \end{bmatrix}, \begin{bmatrix} t_2 \\ b_2 \end{bmatrix}, \dots, \begin{bmatrix} t_k \\ b_k \end{bmatrix} \right\}$$

a  $\underline{\mathsf{match}}$  is a finite sequence of dominos in P (repeats allowed)

where the concatenation of the t's = the concatenation of the b's.

Match = 
$$\begin{bmatrix} t_{i_1} \\ b_{i_1} \end{bmatrix} \begin{bmatrix} t_{i_2} \\ b_{i_2} \end{bmatrix}$$
 ...  $\begin{bmatrix} t_{i_l} \\ b_{i_l} \end{bmatrix}$  where  $t_{i_1}t_{i_2}\cdots t_{i_l} = b_{i_1}b_{i_2}\cdots b_{i_l}$ 

Example: 
$$P = \left\{ \begin{bmatrix} ab \\ aba \end{bmatrix}, \begin{bmatrix} aa \\ aba \end{bmatrix}, \begin{bmatrix} ba \\ aa \end{bmatrix}, \begin{bmatrix} abab \\ b \end{bmatrix} \right\}$$

Match:

#### Check-in 10.1

$$\mathsf{Let}\,P_1 = \Big\{ \Big[ \begin{array}{c} \mathsf{aa} \\ \mathsf{aaba} \end{array} \Big], \, \Big[ \begin{array}{c} \mathsf{ba} \\ \mathsf{ab} \end{array} \Big], \, \Big[ \begin{array}{c} \mathsf{ab} \\ \mathsf{ba} \end{array} \Big] \Big\}$$

Does  $P_1$  have a match?

- (a) Yes.
- (b) No.

Check-in 10.1

### TM Configurations

**Defn:** A configuration of a TM is a triple (q, p, t) where

q =the state,

p =the head position,

t =tape contents

representing a snapshot of the TM at a point in time.

Configuration:  $(q_3, 6, aaaaaabbbbbb)$ 

Encoding as a string: aaaaa $q_3$ abbbbb

Encode configuration (q, p, t) as the string  $t_1qt_2$  where  $t = t_1t_2$  and the head position is on the first symbol of  $t_2$ .

### **TM Computation Histories**

**Defn:** An (accepting) computation history for TM M on input w is a sequence of configurations  $C_1, C_2, ..., C_{\text{accept}}$  that M enters until it accepts.

Encode a computation history  $C_1, C_2, ..., C_{\text{accept}}$  as the string  $C_1 \# C_2 \# \cdots \# C_{\text{accept}}$  where each configuration  $C_i$  is encoded as a string.

A computation history for M on  $w=w_1w_2\cdots w_n$ . Here say  $\delta(q_0,w_1)=(q_7,\mathsf{a},\mathsf{R})$  and  $\delta(q_7,w_2)=(q_8,\mathsf{c},R)$ .

$$C_1$$
  $C_2$   $C_3$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accept}}$   $C_{\text{accep$ 

### **Linearly Bounded Automata**

**Defn:** A linearly bounded automaton (LBA) is a 1-tape TM that cannot move its head off the input portion of the tape.

Tape size adjusts to length of input.

Let  $A_{LBA} = \{\langle B, w \rangle | LBA B \text{ accepts } w \}$ 

**Theorem:**  $A_{LBA}$  is decidable

Proof: (idea) If B on w runs for long, it must be cycling.

Claim: For inputs of length n, an LBA can have

only  $|Q| \times n \times |\Gamma|^n$  different configurations.

Therefore, if an LBA runs for longer, it must repeat some configuration and thus will never halt.

Decider for  $A_{LBA}$ :

 $D_{A-LBA}$  = "On input  $\langle B, w \rangle$ 

- 1. Let n = |w|.
- 2. Run B on w for  $|Q| \times n \times |\Gamma|^n$  steps.
- 3. If has accepted, accept.
- 4. If it has rejected or is still running, reject." must be looping

### $E_{\rm LBA}$ is undecidable

Let  $E_{LBA} = \{\langle B \rangle | B \text{ is an LBA and } L(B) = \emptyset \}$ 

Theorem:  $E_{LBA}$  is undecidable

Proof: Show  $A_{\rm TM}$  is reducible to  $E_{\rm LBA}$ . Uses the computation history method.

Assume that TM R decides  $E_{\rm LBA}$  Construct TM S deciding  $A_{\rm TM}$ 

S = "on input  $\langle M, w \rangle$ 

- 1. Construct LBA  $B_{M,w}$  which tests whether its input x is an accepting computation history for M on w, and only accepts x if it is.
- 2. Use R to determine whether  $L(B_{M,w}) = \emptyset$ .
- 3. Accept if no. Reject if yes."

#### Check-in 10.2

What do you think of the Computation History Method? Check all that apply.

- (a) Cool!
- (b) Just another theorem.
- (c) I'm baffled.
- (d) I wish I was in 6.046.

Check-in 10.2

#### PCP is undecidable

Recall  $PCP = \{\langle P \rangle | P \text{ has a match } \}$ 

$$P = \left\{ \begin{bmatrix} ab \\ aba \end{bmatrix}, \begin{bmatrix} aa \\ aba \end{bmatrix}, \begin{bmatrix} ba \\ aa \end{bmatrix}, \begin{bmatrix} abab \\ b \end{bmatrix} \right\}$$

$$\downarrow \qquad \qquad \downarrow \qquad \qquad \downarrow$$

$$Ab \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} \begin{vmatrix} ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix} | ab \end{vmatrix}$$

Theorem: *PCP* is undecidable

Proof: Show  $A_{TM}$  is reducible to PCP. Uses the computation history method.

Technical assumption: Match must start with  $\begin{bmatrix} t_1 \\ b_1 \end{bmatrix}$ . Can fix this assumption.

Assume that TM R decides PCP Construct TM S deciding  $A_{TM}$ 

 $S = \text{"on in put } \langle M, w \rangle$ 

- 1. Construct PCP instance  $P_{M,w}$  where a match corresponds to a computation history for M on w.
- 2. Use R to determine whether  $P_{M,w}$  has a match.
- 3. Accept if yes. Reject if no."

# Constructing $P_{M,w}$

Make  $P_{M,w}$  where a match is a computation history for M on w.

$$\begin{bmatrix} u_1 \\ v_1 \end{bmatrix} = \begin{bmatrix} \# \\ \#q_0w_1\cdots w_n\# \end{bmatrix} \quad \text{(starting domino)}$$

For each  $a, b \in \Gamma$  and  $q, r \in Q$  where  $\delta(q, a) = (r, b, R)$ 

$$\operatorname{put} \begin{bmatrix} q & a \\ b & r \end{bmatrix} \operatorname{in} P_{M,w}$$

(Handles right moves. Similar for left moves.)

Ending dominos to allow a match if M accepts:

$$\left[\begin{array}{c} a & q_{\rm accept} \ q_{\rm accept} \end{array}\right] \quad \left[\begin{array}{c} q_{\rm accept} & a \ q_{\rm accept} \end{array}\right]$$

Illustration:

$$w = 223$$
  
 $\delta(q_0, 2) = (q_7, 4, R)$ 

#### Check-in 10.3

What else can we now conclude? Choose all that apply.

- (a) PCP is T-unrecognizable.
- (b)  $\overline{PCP}$  is T-unrecognizable.
- (c) Neither of the above.

Match completed! ... one detail needed.

## $ALL_{CFG}$ is undecidable

Let  $\overline{ALL}_{CFG} = \{\langle G \rangle | G \text{ is a CFG and } \underline{L(G)} = \underline{\Sigma}^* \}$ 

Theorem:  $ALL_{CFG}$  is undecidable

Proof: Show  $A_{\rm TM}$  is reducible to  $ALL_{\rm PDA}$  via the computation history method.

Assume TM R decides  $ALL_{\rm PDA}$  and construct TM S deciding  $A_{\rm TM}$ .

S ="On input  $\langle M, w \rangle$ 

- 1. Construct PDA  $B_{M,w}$  which tests whether its input x is an accepting computation history for M on w, and only accepts x if it is NOT.
- 2. Use R to determine whether  $L(B_{M,w}) = \Sigma^*$ .
- 3. Accept if no. Reject if yes."

 $B_{M,w}$  operation: Accept if invalid step of M, or if start wrong, or if end isn't accepting.  $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$   $B_{M,w}$ 

Reverse even-numbered  $C_i$  to allow comparing with  $C_{i+1}$  via stack.

Nondeterministically push some  $C_i$  and pop to compare with  $C_{i+1}$ .

### Computation History Method - recap

Computation History Method is useful for showing the undecidability of problems involving testing for the existence of some object.

D Is there an integral solution (to the polynomial equation)?

 $E_{\rm LBA}$  Is there some accepted string (for the LBA)?

*PCP* Is there a match (for the given dominos)?

 $ALL_{CFG}$  Is there some rejected string (for the CFG)?

In each case, the object is the computation history in some form.

### Quick review of today

- 1. Defined configurations and computation histories.
- 2. Gave The Computation History Method to prove undecidability.
- 3.  $A_{LBA}$  is decidable.
- 4.  $E_{LBA}$  is undecidable.
- 5. *PCP* is undecidable.
- 6.  $ALL_{CFG}$  is undecidable.

## Eliminating the technical assumption

Technical assumption: Match must start with  $\begin{bmatrix} t_1 \\ b_1 \end{bmatrix}$ .

Fix this assumption as follows.

Let 
$$P = \left\{ \begin{bmatrix} t_1 \\ b_1 \end{bmatrix}, \begin{bmatrix} t_2 \\ b_2 \end{bmatrix}, \dots, \begin{bmatrix} t_k \\ b_k \end{bmatrix} \right\}$$
 where we require match to start with  $\begin{bmatrix} t_1 \\ b_1 \end{bmatrix}$ .

Create new 
$$P' = \left\{ \begin{bmatrix} t_1 \\ \overline{b}_1 \end{bmatrix}, \begin{bmatrix} \hat{t}_1 \\ \hat{b}_1 \end{bmatrix}, \begin{bmatrix} \hat{t}_2 \\ \hat{b}_2 \end{bmatrix}, \dots, \begin{bmatrix} \hat{t}_k \\ \hat{b}_k \end{bmatrix} \right\}$$

For any string  $u = u_1, \dots, u_k$ , let

$$\star u = * u_1 * u_2 * \cdots * u_k$$

$$u \star = u_1 * u_2 * \cdots * u_k *$$

$$\star u \star = \ast u_1 \ast u_2 \ast \cdots \ast u_k \ast$$

Then let 
$$P' = \left\{ \begin{bmatrix} \star t_1 \\ \star b_1 \star \end{bmatrix}, \begin{bmatrix} \star t_1 \\ b_1 \star \end{bmatrix}, \begin{bmatrix} \star t_2 \\ b_2 \star \end{bmatrix}, \dots, \begin{bmatrix} \star t_k \\ b_k \star \end{bmatrix}, \begin{bmatrix} *\$ \\ \$ \end{bmatrix} \right\}$$

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.404/6.840 Lecture 11

#### Last time:

- The Computation History Method for proving undecidability
- The Post Correspondence Problem is undecidable
- Linearly bounded automata,  $A_{\rm LBA}$  is decidable
- Configurations, Computation histories
- $E_{\rm LBA}$  and  $ALL_{\rm CFG}$  are undecidable

#### **Today:** (Sipser §6.1 – §6.2)

- Self-reproducing machines and The Recursion theorem
- Short introduction to mathematical logic

### Midterm exam

90 minutes length + 20 minutes for printing/scanning/uploading.

Open book, postings, piazza, notes, and lecture videos, from this year.

Covers through Recursion Theorem presented today.

Will <u>not</u> include section on mathematical logic.

**Not permitted:** Communication with anyone except course staff, other materials, internet searching.

**Not permitted:** Providing information about the exam to anyone who hasn't completed it.

Please respect our honor system.

## Self-reproduction Paradox

#### Suppose a Factory makes Cars

Complexity of Factory > Complexity of Car
(because Factory needs instructions for Car + robots, tools, ...)

#### Can a Factory make Factories?

- Complexity of Factory > Complexity of Factory?
- Seems impossible to have a self-reproducing machine

But, living things self-reproduce

How to resolve this paradox?

Self-reproducing machines are possible!

© Source unknown. All rights reserved. This content is excluded from our Creative Commons license. For more information, see <a href="https://ocw.mit.edu/fairuse">https://ocw.mit.edu/fairuse</a>.

# A Self-Reproducing TM

**Theorem:** There is a TM SELF which (on any input) halts with  $\langle SELF \rangle$  on the tape.

**Lemma:** There is a computable function  $q: \Sigma^* \to \Sigma^*$  such that  $q(w) = \langle P_w \rangle$  for every w, where  $P_w$  is the TM  $P_w =$  "Print w on the tape and halt". Proof: Straightforward.

**Proof of Theorem:** *SELF* has two parts, *A* and *B*.

$$A = P_{\langle B \rangle}$$
$$B = P_{\langle A \rangle} ?$$

B = "1. Compute q(tape contents) to get A.

- 2. Combine with B to get AB = SELF.
- 3. Halt with  $\langle SELF \rangle$  on tape."

Can implement in any programming language.

## **English Implementation**

#### Check-in 11.1

Implementations of the Recursion Theorem have two parts, a <u>Template</u> and an <u>Action</u>. In the TM and English implementations, which is the <u>Action</u> part?

- (a) A and the upper phrase
- (b) A and the lower phrase
- (c) B and the upper phrase
- (d) B and the lower phrase.

Write the following twice, the second time in quotes "Write the following twice, the second time in quotes" Write the following twice, the second time in quotes "Write the following twice, the second time in quotes"

Note on Pset Problem 6: Don't need to worry about quoting.

### The Recursion Theorem

A compiler which implements "compute your own description" for a TM.

**Theorem:** For any TM T there is a TM R where for all w R on input w operates in the same way as T on input  $\langle w, R \rangle$ .

**Proof of Theorem:** R has three parts: A, B, and T.

T is given

$$A = P_{\langle BT \rangle}$$

B = "1. Compute q(tape contents after w) to get A.

- 2. Combine with BT to get ABT = R.
- 3. Pass control to T on input  $\langle w, R \rangle$ ."

**Moral:** You can use "compute your own description" in describing TMs.

#### Check-in 11.2

Can we use the Recursion Theorem to design a TM T where  $L(T) = \{\langle T \rangle\}$ ?

- (a) Yes.
- (b) No.

# Ex 1: $A_{TM}$ is undecidable - new proof

**Theorem:**  $A_{TM}$  is not decidable

Proof by contradiction: Assume some TM H decides  $A_{\rm TM}$ .

Consider the following TM R:

R = "On input w

- 1. Get own description  $\langle R \rangle$ .
- 2. Use H on input  $\langle R, w \rangle$  to determine whether R accepts w.
- 3. Do the opposite of what *H* says."

### Ex 2: Fixed-point Theorem

```
Theorem: For any computable function f: \Sigma^* \to \Sigma^*, there is a TM R such that L(R) = L(S) where f(\langle R \rangle) = \langle S \rangle.
```

In other words, consider f to be a program transformation function. Then for some program R, its behavior is unchanged by f.

Proof: Let *R* be the following TM.

R = "On input w

- 1. Get own description  $\langle R \rangle$ .
- 2. Compute  $f(\langle R \rangle)$  and call the result  $\langle S \rangle$ .
- 3. Simulate S on w."

# Ex 3: $MIN_{TM}$ is T-unrecognizable

**Defn:** M is a minimal TM if  $|\langle M' \rangle| < |\langle M \rangle| \rightarrow L(M') \neq L(M)$ .

Thus, a minimal TM has the shortest description among all equivalent TMs.

Let  $MIN_{TM} = \{\langle M \rangle | M \text{ is a minimal TM } \}$ .

**Theorem:**  $MIN_{TM}$  is T-unrecognizable.

Proof by contradiction: Assume some TM E enumerates

Consider the following TM R:

R = "On input w

- 1. Get own description  $\langle R \rangle$ .
- 2. Run enumerator E until some TM B appears, where  $|\langle R \rangle| < |\langle B \rangle|$ .
- 3. Simulate B on w."

Thus L(R) = L(B) and  $|\langle R \rangle| < |\langle B \rangle|$  so B isn't minimal, but  $\langle B \rangle \in L(E)$ , contradiction.

#### Check-in 11.3

Let A be an infinite subset of  $MIN_{\rm TM}$ . Is it possible that A is T-recognizable?

- (a) Yes.
- (b) No.

# Other applications

- 1. Computer viruses.
- 2. A true but unprovable mathematical statement due to Kurt Gödel: "This statement is unprovable."

## Intro to Mathematical Logic

**Goal:** A mathematical study of mathematical reasoning itself.

Formally defines the language of mathematics, mathematical truth, and provability.

#### Gödel's First Incompleteness Theorem:

In any reasonable formal system, some true statements are not provable.

Proof: We use two properties of formal proofs:

- 1) Soundness: If  $\phi$  has a proof  $\pi$  then  $\phi$  is true.
- 2) Checkability: The language  $\{\langle \pi, \phi \rangle | \pi \text{ is a proof of statement } \phi \}$  is decidable.

Checkability implies the set of provable statements  $\{\langle \phi \rangle | \phi \text{ has a proof} \}$  is T-recognizable.

Similarly, if we can always prove  $\langle M, w \rangle \in \overline{A_{TM}}$  when it is true, then  $\overline{A_{TM}}$  is T-recognizable (false!).

Therefore, some true statements of the form  $\langle M, w \rangle \in \overline{A_{\text{TM}}}$  are unprovable.

Next, we use the Recursion Theorem to give a specific example of a true but unprovable statement.

## A True but Unprovable Statement

Implement Gödel statement "This statement is unprovable."

Let  $\phi_U$  be the statement  $\langle R, 0 \rangle \in \overline{A_{\text{TM}}}$  where R is the following TM:

R = "On any input

- 1. Obtain  $\langle R \rangle$  and use it to obtain  $\phi_U$ .
- 2. For each possible proof  $\pi = \pi_1, \pi_2, ...$

Test if  $\pi$  is a proof that  $\phi_U$  is true.

If yes, then accept. Otherwise, continue."

**Theorem:** (1)  $\phi_U$  has no proof

(2)  $\phi_U$  is true

 $(2) \psi_U$  is true

- (1) If  $\phi_{II}$  has a proof
- (2) If  $\phi_U$  is false

Proof:

 $\phi_{II}$ 

# Quick review of today

- 1. Self-reference and The Recursion Theorem
- 2. Various applications.
- 3. Sketch of Gödel's First Incompleteness Theorem in mathematical logic.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.404/6.840 Lecture 12

#### Last time:

- Self-reproducing machines and The Recursion Theorem
- Applications:
  - a) New proof that  $A_{TM}$  is undecidable
  - b)  $MIN_{\rm TM}$  is T-unrecognizable (and so is any infinite subset of  $MIN_{\rm TM}$ )
  - c) True but unprovable statements

### Today: (Sipser §7.1)

- Introduction to Complexity Theory
- Complexity classes; the Class P

## Intro to Complexity Theory

#### Computability theory (1930s - 1950s):

Is A decidable?

#### **Complexity theory (1960s - present):**

Is A decidable with restricted resources? (time/memory/...)

**Example:** Let  $A = \{a^k b^k | k \ge 0\}$ .

**Q:** How many steps are needed to decide A?

Depends on the input.

We give an <u>upper bound</u> for all inputs of length n.

Called "worst-case complexity".

# # steps to decide $A = \{a^k b^k | k \ge 0\}$

**Theorem:** A 1-tape TM M can decide A where, on inputs of length n, M uses at most  $cn^2$  steps, for some fixed constant c.

**Terminology:** M uses  $O(n^2)$  steps.

Proof: M = "On input w

- 1. Scan input to check if  $w \in a^*b^*$ , reject if not.
- Repeat until all crossed off.
  Scan tape, crossing off one a and one b.
  Reject if only a's or only b's remain.
- 3. Accept if all crossed off. "

**Analysis:** 

O(n) steps +O(n) iterations  $\times O(n)$  steps

$$O(n) + O(n^2)$$
 steps  
=  $O(n^2)$  steps

Check-in 12.1

How much improvement is possible in the bound for this theorem about 1-tape TMs deciding A?

- (a)  $O(n^2)$  is best possible.
- (b)  $O(n \log n)$  is possible.
- (c) O(n) is possible.

# Deciding $A = \{a^k b^k | k \ge 0\}$ faster

**Theorem:** A 1-tape TM M can decide A by using  $O(n \log n)$  steps.

Proof:

M = "On input w

- 1. Scan tape to check if  $w \in a^*b^*$ . Reject if not.
- Repeat until all crossed off.
  Scan tape, crossing off every other a and b.
  Reject if even/odd parities disagree.
- 3. Accept if all crossed off. "

#### **Analysis:**

O(n) steps + $O(\log n)$  iterations  $\times O(n)$  steps

$$O(n) + O(n \log n)$$
 steps  
=  $O(n \log n)$  steps

|     | Parities |
|-----|----------|
| a's |          |
| b's |          |

Further improvement? Not possible.

**Theorem:** A 1-tape TM M cannot decide A by using  $o(n \log n)$  steps.

You are not responsible for knowing the proof.

# Deciding $A = \{a^k b^k | k \ge 0\}$ even faster

**Theorem:** A multi-tape TM M can decide A using O(n) steps.

M = "On input w

- 1. Scan input to check if  $w \in a^*b^*$ , reject if not.
- 2. Copy a's to second tape.
- 3. Match b's with a's on second tape.
- 4. Accept if match, else reject."

#### **Analysis:**

O(n) steps

+O(n) steps

+O(n) steps

-----

= O(n) steps

### **Model Dependence**

Number of steps to decide  $A = \{a^k b^k | k \ge 0\}$  depends on the model.

• 1-tape TM:  $O(n \log n)$ 

• Multi-tape TM: O(n)

**Computability theory:** model independence (Church-Turing Thesis)

Therefore model choice doesn't matter. Mathematically nice.

**Complexity Theory:** model dependence

But dependence is low (polynomial) for reasonable deterministic models.

We will focus on questions that do not depend on the model choice.

So... we will continue to use the 1-tape TM as the basic model for complexity.

## TIME Complexity Classes

**Defn:** Let  $t: \mathbb{N} \to \mathbb{N}$ . Say TM M runs in time t(n) if M always halts within t(n) steps on all inputs of length n.

**Defn:** TIME $(t(n)) = \{B \mid \text{ some deterministic 1-tape TM } M \text{ decides } B \text{ and } M \text{ runs in time } O(t(n))\}$ 

#### **Example:**

 $A = \{ \mathsf{a}^k \mathsf{b}^k \middle| k \ge 0 \} \in \mathsf{TIME}(n \log n)$ 

### Check-in 12.2

Let  $B = \{ww^{\mathcal{R}} \mid w \in \{a, b\}^*\}.$ 

What is the smallest function t such that  $B \in TIME(t(n))$ ?

- (a) O(n)
- (b)  $O(n \log n)$
- $(c) O(n^2)$
- (d)  $O(n^3)$

Check-in 12.2

### Multi-tape vs 1-tape time

**Theorem:** Let  $t(n) \ge n$ .

If a multi-tape TM decides B in time t(n), then  $B \in TIME(t^2(n))$ .

Proof: Analyze conversion of multi-tape to 1-tape TMs.

To simulate 1 step of M's computation, S uses O(t(n)) steps.

So total simulation time is  $O(t(n) \times t(n)) = O(t^2(n))$ .

Similar results can be shown for other reasonable deterministic models.

## Relationships among models

**Informal Defn:** Two models of computation are polynomially related if each can simulate the other with a polynomial overhead: So t(n) time  $\to t^k(n)$  time on the other model, for some k.

All reasonable deterministic models are polynomially related.

- 1-tape TMs
- multi-tape TMs
- multi-dimensional TMs
- random access machine (RAM)
- cellular automata

### The Class P

**Defn:**  $P = \bigcup_k TIME(n^k)$ = polynomial time decidable languages

- Invariant for all reasonable deterministic models
- Corresponds roughly to realistically solvable problems

**Example:**  $PATH = \{\langle G, s, t \rangle | G \text{ is a directed graph with a path from } s \text{ to } t \}$ 

Theorem:  $PATH \in P$ 

Proof:  $M = \text{"On input } \langle G, s, t \rangle$ 

1. Mark s

2. Repeat until nothing new is marked:

For each marked node *x*:

Scan G to mark all y where (x, y) is an edge

3. *Accept* if *t* is marked. *Reject* if not.

 $\leq n$  iterations  $\times \leq n$  iterations  $\times O(n^2)$  steps  $O(n^4)$  steps

### To show polynomial time:

Each stage should be clearly polynomial and the total number of steps polynomial.

### PATH and HAMPATH

**Example:**  $HAMPATH = \{\langle G, s, t \rangle | G \text{ is a directed graph with a path from } s \text{ to } t$  and the path goes through every node of  $G \}$ 

**Recall Theorem:**  $PATH \in P$  Called a Hamiltonian path

Question:  $HAMPATH \in P$ ?

"On input  $\langle G, s, t \rangle$ 

- 1. Let m be the number of nodes in G.
- 2. For each path of length m in G: test if m is a Hamiltonian path from s to t. Accept if yes.
- 3. Reject if all paths fail."

May be  $m! > 2^m$  paths of length m so algorithm is exponential time not polynomial time.

#### Check-in 12.3

Is  $HAMPATH \in P$ ?

- (a) Definitely Yes. You have a polynomial-time algorithm.
- (b) Probably Yes. It should be similar to showing  $PATH \in P$ .
- (c) Toss up.
- (d) Probably No. Hard to beat the exponential algorithm.
- (e) Definitely No. You can prove it!

Check-in 12.3

## Quick review of today

- 1. Introduction to Complexity Theory
- 2. Which model to use? 1-tape-TMs
- 3. TIME(t(n)) complexity classes
- 4. The class P
- 5.  $PATH \in P$

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 14 (midterm replaced lecture 13)

#### Last time:

- TIME(t(n))
- $P = \bigcup_k \mathsf{TIME}(n^k)$
- $-PATH \in P$

**Today:** (Sipser §7.2 – §7.3)

- $\mathsf{NTIME} \big( t(n) \big)$
- NP
- P vs NP problem
- Dynamic Programming
- Polynomial-time reducibility

#### **Quick Review**

```
Defn: TIME(t(n)) = \{B \mid \text{ some deterministic 1-tape TM } M \text{ decides } B  and M runs in time O(t(n))\}

Defn: P = \bigcup_k \text{TIME}(n^k) = polynomial time decidable languages

PATH = \{\langle G, s, t \rangle | G \text{ is a directed graph with a path from } s \text{ to } t \}

Theorem: PATH \in P

HAMPATH = \{\langle G, s, t \rangle | G \text{ is a directed graph with a path from } s \text{ to } t \text{ that goes through every node of } G \}

HAMPATH \in P?
```

[connection to factoring]

### Nondeterministic Complexity

In a nondeterministic TM (NTM) decider, all branches halt on all inputs.

**Defn:** An NTM runs in time t(n) if all branches halt within t(n) steps on all inputs of length n.

**Defn:** NTIME $(t(n)) = \{B \mid \text{ some 1-tape NTM decides } B \text{ and runs in time } O(t(n)) \}$ 

**Defn:**  $NP = \bigcup_k NTIME(n^k)$ = nondeterministic polynomial time decidable languages

- Invariant for all reasonable nondeterministic models
- Corresponds roughly to easily verifiable problems

Computation tree for NTM on input w.

all branches halt within t(n) steps

#### $HAMPATH \in NP$

**Theorem:**  $HAMPATH \in NP$ 

Proof:

"On input  $\langle G, s, t \rangle$  (Say G has m nodes.)

- 1. Nondeterministically write a sequence  $(v_1)(v_2)...,(v_m)$  of m nodes.
- 2. Accept if  $v_1 = s$   $v_m = t$ \neach  $(v_i, v_{i+1})$  is an edge and no  $v_i$  repeats.
- 3. Reject if any condition fails."

#### *COMPOSITES* ∈ NP

```
Defn: COMPOSITES = \{x \mid x \text{ is not prime and } x \text{ is written in binary}\}
= \{x \mid x = yz \text{ for integers } y, z > 1, x \text{ in binary}\}
```

**Theorem:**  $COMPOSITES \in NP$ 

**Proof:** "On input x

- 1. Nondeterministically write y where 1 < y < x.
- 2. Accept if y divides x with remainder 0. Reject if not."

**Note:** Using base 10 instead of base 2 wouldn't matter because can convert in polynomial time.  $\frac{k}{\sqrt{k}}$ 

Bad encoding: write number k in unary:  $1^k = \overbrace{111 \cdots 1}^k$  , exponentially longer.

**Theorem** (2002):  $COMPOSITES \in P$ 

We won't cover this proof.

#### Intuition for P and NP

NP = All languages where can verify membership quickly

P = All languages where can test membership quickly

Examples of quickly verifying membership:

- HAMPATH: Give the Hamiltonian path.
- COMPOSITES: Give the factor.

The <u>Hamiltonian path</u> and the <u>factor</u> are called **short certificates** of membership.

#### Check-in 14.1

Let  $\overline{HAMPATH}$  be the complement of HAMPATH.

So  $\langle G, s, t \rangle \in \overline{HAMPATH}$  if G does <u>not</u> have a Hamiltonian path from s to t.

Is  $\overline{HAMPATH} \in NP$ ?

- (a) Yes, we can invert the accept/reject output of the NTM for HAMPATH.
- (b) No, we cannot give a short certificate for a graph not to have a Hamiltonian path.
- (c) I don't know.

# Recall $A_{\rm CFG}$

**Recall:**  $A_{CFG} = \{\langle G, w \rangle | G \text{ is a CFG and } w \in L(G) \}$ 

**Theorem:**  $A_{CFG}$  is decidable

Proof:  $D_{A-CFG}$  = "On input  $\langle G, w \rangle$  Chomsky Normal Form (CNF):

1. Convert G into Chomsky Normal Form.  $A \rightarrow BC$ 

2. Try all derivations of length 2|w|-1.  $B \rightarrow b$ 

3. Accept if any generate w. Reject if not. Let's always assume G is in CNF.

Theorem:  $A_{CFG} \in NP$ 

Proof: "On input  $\langle G, w \rangle$ 

- 1. Nondeterministically pick some derivation of length 2|w|-1.
- 2. Accept if it generates w. Reject if not.

# Attempt to show $A_{CFG} \in P$

Theorem:  $A_{CFG} \in P$ 

Proof attempt:

Recursive algorithm C tests if G generates W, starting at any specified variable R.

 $C = \text{"On input } \langle G, w, R \rangle$ 

- 1. For each way to divide w = xy and for each rule  $R \rightarrow ST$
- 2. Use C to test  $\langle G, x, S \rangle$  and  $\langle G, y, T \rangle$
- 3. Accept if both accept
- 4. Reject if none of the above accepted."

Then decide  $A_{CFG}$  by starting from G's start variable.

C is a correct algorithm, but it takes non-polynomial time. (Each recursion makes O(n) calls and depth is roughly  $\log n$ .)

**Fix:** Use recursion + memory called *Dynamic Programming* (DP)

**Observation:** String w of length n has  $O(n^2)$  substrings  $w_i \cdots w_j$  therefore there are only  $O(n^2)$  possible sub-problems  $\langle G, x, S \rangle$  to solve.

### DP shows $A_{CFG} \in P$

Theorem:  $A_{CFG} \in P$ 

Proof: Use DP (Dynamic Programming) = recursion + memory.

 $D = \text{"On input } \langle G, w, R \rangle$ 

- 1. For each way to divide w = xy and for each rule R  $\rightarrow$  ST
- 2. Use D to test (G, x, S) and (G, y, T)
- 3. *Accept* if both accept
- 4. Reject if none of the above accepted."

Then decide  $A_{CFG}$  by starting from G's start variable.

same as before

Total number of calls is  $O(n^2)$  so time used is polynomial.

Alternately, solve all smaller sub-problems first: "bottom up"

#### Check-in 14.2

Suppose B is a CFL. Does that imply that  $B \in P$ ?

- (a) Yes
- (b) No.

# $A_{\text{CFG}} \in P \& Bottom-up DP$

Theorem:  $A_{CFG} \in P$ 

Proof: Use bottom-up DP.

 $D = \text{"On input } \langle G, w \rangle$ 

- 1. For each  $w_i$  and variable R Solve  $(G, w_i, R)$  by checking if  $R \to w_i$  is a rule. Solve for substrings
- 2. For k=2,...,n and each substring u of w where |u|=k and variable R Solve  $\langle G,u,R\rangle$  by checking for each R  $\rightarrow$  ST and each division u=xy if both  $\langle G,x,S\rangle$  and  $\langle G,y,T\rangle$  were positive.

Solve for substrings of length k by using previous answers for substrings of length < k.

- 3. Accept if (G, w, S) is positive where S is the original start variable.
- 4. Reject if not."

Total number of calls is  $O(n^2)$  so time used is polynomial.

Often, bottom-up DP is shown as filling out a table.

## Satisfiability Problem

**Defn:** A *Boolean formula*  $\phi$  has Boolean variables (True/False values) and Boolean operations AND  $(\Lambda)$ , Or (V), and Not  $(\neg)$ .

**Defn:**  $\phi$  is *satisfiable* if  $\phi$  evaluates to True for some assignment to its variables. Sometimes we use 1 for True and 0 for False.

**Example:** Let  $\phi = (x \lor y) \land (\overline{x} \lor \overline{y})$  (Notation:  $\overline{x}$  means  $\neg x$ ) Then  $\phi$  is satisfiable (x=1, y=0)

**Defn:**  $SAT = \{\langle \phi \rangle | \phi \text{ is a satisfiable Boolean formula} \}$ 

Theorem (Cook, Levin 1971):  $SAT \in P \rightarrow P = NP$ Proof method: polynomial time (mapping) reducibility

#### Check-in 14.3

Is  $SAT \in NP$ ?

- (a) Yes.
- (b) No.
- (c) I don't know.
- (d) No one knows.

### Polynomial Time Reducibility

**Defn:** A is polynomial time reducible to B  $(A \leq_P B)$  if  $A \leq_m B$ by a reduction function that is computable in polynomial time.

**Theorem:** If  $A \leq_{\mathbf{P}} B$  and  $B \in \mathbf{P}$  then  $A \in \mathbf{P}$ .

f is computable in polynomial time

Idea to show  $SAT \in P \rightarrow P = NP$ 

## Quick review of today

- 1. NTIME(t(n)) and NP
- 2. HAMPATH and  $COMPOSITES \in NP$
- 3. P versus NP question
- 4.  $A_{CFG} \in P$  via Dynamic Programming
- 5. The Satisfiability Problem SAT
- 6. Polynomial time reducibility

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 15

#### Last time:

- $\mathsf{NTIME}\big(t(n)\big)$ ,  $\mathsf{NP}$
- P vs NP problem
- Dynamic Programming,  $A_{\mathrm{CFG}} \in \mathsf{P}$
- Polynomial-time reducibility

**Today:** (Sipser §7.5) - NP-completeness

### **Quick Review**

**Defn:** A is polynomial time reducible to B  $(A \leq_P B)$  if  $A \leq_m B$  by a reduction function that is computable in polynomial time.

**Theorem:** If  $A \leq_{P} B$  and  $B \in P$  then  $A \in P$ .

f is computable in polynomial time

NP = All languages where can verify membership quickly

P = All languages where can <u>test</u> membership quickly

P versus NP question: Does P = NP?

 $SAT = \{\langle \phi \rangle | \phi \text{ is a satisfiable Boolean formula} \}$ 

**Cook-Levin Theorem:**  $SAT \in P \rightarrow P = NP$ 

**Proof plan:** Show that every  $A \in NP$  is polynomial time reducible to SAT.

# $\leq_{\mathbf{P}}$ Example: 3SAT and CLIQUE

**Defn:** A Boolean formula  $\phi$  is in Conjunctive Normal Form (CNF) if it

has the form 
$$\phi = (x \lor \overline{y} \lor z) \land (\overline{x} \lor \overline{s} \lor z \lor u) \land \cdots \land (\overline{z} \lor \overline{u})$$

literals

**Literal:** a variable or a negated variable

Clause: an OR (V) of literals. **CNF**: an AND  $(\Lambda)$  of clauses.

**3CNF**: a CNF with exactly 3 literals in each clause.

 $3SAT = \{\langle \phi \rangle | \phi \text{ is a satisfiable 3CNF formula}\}$ 

**Defn:** A k-clique in a graph is a subset of k nodes all directly connected by edges.

 $CLIQUE = \{\langle G, k \rangle | \text{ graph } G \text{ contains a } k\text{-clique} \}$ 

Will show:  $3SAT \leq_{\mathbf{P}} CLIQUE$ 

3-clique

4-clique

5-clique

# $3SAT \leq_{P} CLIQUE$

Theorem:  $3SAT \leq_{\mathbf{P}} CLIQUE$ 

Proof: Give polynomial-time reduction f that maps  $\phi$  to G, k

where  $\phi$  is satisfiable iff G has a k-clique.

A satisfying assignment to a CNF formula has  $\geq 1$  true literal in each clause.

# $3SAT \leq_{\mathbf{P}} CLIQUE$ conclusion

$$\phi \ = \ (a \vee b \vee \overline{c}) \ \wedge \ (\overline{a} \vee b \vee d) \ \wedge \ (a \vee c \vee \overline{e}) \ \wedge \ \cdots \ \wedge \ (\overline{x} \vee y \vee \overline{z})$$

Claim:  $\phi$  is satisfiable iff G has a k-clique

- ( $\rightarrow$ ) Take any satisfying assignment to  $\phi$ . Pick 1 true literal in each clause. The corresponding nodes in G are a k-clique because they don't have forbidden edges.
- ( $\leftarrow$ ) Take any k-clique in G. It must have 1 node in each clause. Set each corresponding literal True. That gives a satisfying assignment to  $\phi$ .

The reduction f is computable in polynomial time.

Corollary:  $CLIQUE \in P \rightarrow 3SAT \in P$ 

### Check-in 15.1

Does this proof require 3 literals per clause?

- (a) Yes, to prove the claim.
- (b) Yes, to show it is in poly time.
- (c) No, it works for any size clauses.

Check-in 15.1

### NP-completeness

**Defn:** *B* is <u>NP-complete</u> if

1)  $B \in NP$ 

2) For all  $A \in NP$ ,  $A \leq_P B$ 

If B is NP-complete and  $B \in P$  then P = NP.

**Cook-Levin Theorem:** *SAT* is NP-complete

Proof: Next lecture; assume true

### Check-in 15.2

What language that we've previously seen is most analogous to SAT?

- (a)  $A_{\mathsf{TM}}$
- (b)  $E_{\mathsf{TM}}$
- (c)  $\{0^k 1^k | k \ge 0\}$

To show some language C is NP-complete, show  $3SAT \leq_P C$ .

or some other previously shown NP-complete language

## HAMPATH is NP-complete

**Theorem:** *HAMPATH* is NP-complete

Proof: Show  $3SAT \leq_P HAMPATH$  (assumes 3SAT is NP-complete)

Idea: "Simulate" variables and clauses with "gadgets"

### Construction of *G*

 $x_m$ 

The reduction f is computable in polynomial time.

### Check-in 15.3

Would this construction still work if we made G undirected by changing all the arrows to lines? In other words, would this construction show that the undirected Hamiltonian path problem is NP-complete?

- (a) Yes, the construction would still work.
- (b) No, the construction depends on G being directed.

## Quick review of today

- 1. NP-completeness
- SAT and SAT
- 3.  $3SAT \leq_P HAMPATH$
- 4.  $3SAT \leq_P CLIQUE$
- 5. Strategy for proving NP-completeness: Reduce from 3SAT by constructing gadgets that simulate variables and clauses.

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 16

#### Last time:

- NP-completeness
- $3SAT ≤_P CLIQUE$
- $-3SAT ≤_P HAMPATH$

**Today:** (Sipser §7.4)

- Cook-Levin Theorem: SAT is NP-complete

- 3*SAT* is NP-complete

### **Quick Review**

**Defn:** *B* is <u>NP-complete</u> if

- 1)  $B \in NP$
- 2) For all  $A \in NP$ ,  $A \leq_P B$

If B is NP-complete and  $B \in P$  then P = NP.

#### **Importance of NP-completeness**

- 1) Evidence of computational intractability.
- 2) Gives a good candidate for proving  $P \neq NP$ .

To show some language C is NP-complete, show  $3SAT \leq_{P} C$ .

or some other previously shown NP-complete language

#### Check-in 16.1

The big sigma notation means summing over some set.

$$\sum_{1 \le i \le n} i = 1 + 2 + \dots + n$$

The big AND (or OR) notation has a similar meaning.

For example, if  $x = x_1 \cdots x_n$  and  $y = y_1 \cdots y_n$  are two strings of length n, when does the following hold?

$$\left(\bigwedge_{1 \le i \le n} x_i = y_i\right) = \text{TRUB}$$

- (a) Whenever x and y agree on some symbol.
- (b) Whenever x = y.

### Cook-Levin Theorem (idea)

```
Theorem: SAT is NP-complete Proof: 1) SAT \in NP (done)
2) Show that for each A \in NP we have A \leq_P SAT:
Let A \in NP be decided by NTM M in time n^k.
Give a polynomial-time reduction f mapping A to SAT.
f \colon \Sigma^* \to \text{ formulas}
f(w) = \langle \phi_{M,w} \rangle
w \in A \text{ iff } \phi_{M,w} \text{ is satisfiable}
Idea: \phi_{M,w} simulates M on w. Design \phi_{M,w} to "say" M accepts w.
```

Satisfying assignment to  $\overline{\phi_{M,w}}$  is a computation history for M on w.

### Tableau for *M* on *w*

Defn: An <u>(accepting) tableau</u> for NTM M on w is an  $n^k \times n^k$  table representing an computation history for M on w on an accepting branch of the nondeterministic computation.

# Constructing $\phi_{M,w}$ : $\phi_{\mathrm{cell}}$

The variables of  $\phi_{M,w}$  are  $x_{i,j,\sigma}$  for  $1 \leq i, j \leq n^k$  and  $\sigma \in \Gamma \cup Q$ .

 $x_{i,j,\sigma} = \text{TRUE}$  means cell i,j contains  $\sigma$ .

#### Check-in 16.2

How many variables does  $\phi_{M,w}$  have? Recall that n = |w|.

- (a) O(n)
- (b)  $O(n^2)$
- (c)  $O(n^k)$
- (d)  $O(n^{2k})$

# Constructing $\phi_{M,w}$ : $\phi_{\text{start}}$ and $\phi_{\text{accept}}$

$$\phi_{M,w}$$
 "says" a tableau for  $M$  on  $w$  exists.  $\phi_{M,w} = \phi_{\text{cell}} \wedge \phi_{\text{start}} \wedge \phi_{\text{move}} \wedge \phi_{\text{accept}}$   $\phi_{\text{cell}}$  done  $\checkmark$   $\phi_{\text{start}} = \phi_{\text{accept}} = \bigvee_{1 \leq j \leq n^k} x_{n^k,j,q_{\text{accept}}}$ 

# Constructing $\phi_{M,w}$ : $\phi_{\text{move}}$

2×3 neighborhood

 $\phi_{M,w}$  "says" a tableau for M on w exists.

$$\phi_{M,w} = \phi_{\text{cell}} \wedge \phi_{\text{start}} \wedge \phi_{\text{move}} \wedge \phi_{\text{accept}}$$

Legal neighborhoods: consistent with M's transition function

| ootential | а     | $q_7$ |  |
|-----------|-------|-------|--|
| xamples:  | $q_3$ | а     |  |

a b c a b 
$$q_5$$

Illegal neighborhoods: not consistent with M's transition function

examples:

$$\begin{array}{c|ccc} a & b & c \\ \hline a & q_2 & c \end{array}$$

$$\begin{array}{c|c} a & q_7 & c \ \hline q_3 & d & q_4 \ \hline \end{array}$$

Claim: If every  $2\times3$  neighborhood is legal then tableau corresponds to a computation history.

$$\phi_{\text{move}} = \bigwedge_{1 < i,j < n^k} \left( \bigvee_{\text{Legal}} \left( x_{i,j-1,r} \land x_{i,j,S} \land x_{i,j+1,t} \land x_{i+1,j-1,V} \land x_{i+1,j,V} \land x_{i+1,j+1,Z} \right) \right)$$
Says that the neighborhood at  $i,j$  is legal

## Conclusion: *SAT* is NP-complete

#### **Summary:**

For  $A \in NP$ , decided by NTM M, we gave a reduction f from A to SAT:

$$f \colon \Sigma^* \to \text{ formulas}$$
  
 $f(w) = \langle \phi_{M,w} \rangle$   
 $w \in A \text{ iff } \phi_{M,w} \text{ is satisfiable.}$ 

$$\phi_{M,W} = \phi_{\text{cell}} \wedge \phi_{\text{start}} \wedge \phi_{\text{move}} \wedge \phi_{\text{accept}}$$

The size of  $\phi_{M,w}$  is roughly the size of the tableau for M on w, so size is  $O(n^k \times n^k) = O(n^{2k})$ .

Therefore f is computable in polynomial time.

## 3SAT is NP-complete

$$\begin{array}{c|cccc} \underline{a & b & a \lor b = c} \\ \hline 1 & 1 & 1 & (a \land b) \to c \\ 0 & 1 & 1 & (\overline{a} \land b) \to c \\ 1 & 0 & 1 & (a \land \overline{b}) \to \overline{c} \\ 0 & 0 & 0 & (\overline{a} \land \overline{b}) \to \overline{c} \end{array}$$

**Theorem:** 3SAT is NP-complete

Proof: Show  $SAT \leq_P 3SAT$ 

Give reduction f converting formula  $\phi$  to 3CNF formula  $\phi'$ , preserving satisfiability.

(Note:  $\phi$  and  $\phi'$  are not logically equivalent)

Example: Say  $\phi = ((a \land b) \lor c) \land (\overline{a} \lor b)$ 

Tree structure for  $\phi$ :

Logical equivalence:  $(A \to B)$  and  $(\overline{A} \lor B)$   $(\overline{A} \land B)$  and  $(\overline{A} \lor \overline{B})$ 

$$\phi' = \left( (\mathsf{a} \land \mathsf{b}) \to z_1 \right) \, \land \, \left( (\overline{\mathsf{a}} \land \mathsf{b}) \to \overline{\mathsf{z}_1} \right) \, \land \, \left( \left( \mathsf{a} \land \overline{\mathsf{b}} \right) \to \overline{\mathsf{z}_1} \right) \, \land \, \left( \left( \overline{\mathsf{a}} \land \overline{\mathsf{b}} \right) \to \overline{\mathsf{z}_1} \right)$$

$$\wedge \ \left( (z_1 \wedge \mathsf{c}) \to z_2 \right) \wedge \left( (\overline{\mathsf{z}_1} \wedge \mathsf{c}) \to z_2 \right) \wedge \left( (z_1 \wedge \overline{\mathsf{c}}) \to z_2 \right) \wedge \left( (\overline{\mathsf{z}_1} \wedge \overline{\mathsf{c}}) \to \overline{\mathsf{z}_2} \right)$$

: repeat for each  $z_i$ 

#### $\land$ ( $z_4$ ) Check-in 16.3

If  $\phi$  has k operations ( $\wedge$  and  $\vee$ ), how many clauses has  $\phi$ ?

(a) k + 1

(c)  $k^2$ 

(b) 4k + 1

(d)  $2k^2$ 

# Quick review of today

- 1. *SAT* is NP-complete
- 2. 3*SAT* is NP-complete

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.404/6.840 Lecture 17

#### Last time:

- Cook-Levin Theorem: *SAT* is NP-complete
- 3*SAT* is NP-complete

#### **Today:** (Sipser §8.1 – §8.2)

- Space complexity
- SPACE(f(n)), NSPACE(f(n))
- PSPACE, NPSPACE
- Relationship with TIME classes
- Examples

## **SPACE Complexity**

**Defn:** Let  $f: \mathbb{N} \to \mathbb{N}$  where  $f(n) \ge n$ . Say TM M runs in space f(n) if M always halts and uses at most f(n) tape cells on all inputs of length n.

#### Check-in 17.1

We define space complexity for multi-tape TMs by taking the sum of the cells used on all tapes.

Do we get the same class PSPACE for multi-tape TMs?

- (a) No.
- (b) Yes, converting a multi-tape TM to single-tape only squares the amount of space used.
- (c) Yes, converting a multi-tape TM to single-tape only increases the amount of space used by a constant factor.

# Relationships between Time and SPACE Complexity

**Theorem:** For  $t(n) \ge n$ 

- 1)  $\mathsf{TIME}(t(n)) \subseteq \mathsf{SPACE}(t(n))$
- 2) SPACE $(t(n)) \subseteq TIME(2^{O(t(n))})$ =  $\bigcup_{c} TIME(c^{t(n)})$

#### Proof:

- 1) A TM that runs in t(n) steps cannot use more than t(n) tape cells.
- 2) A TM that uses t(n) tape cells cannot use more than  $c^{t(n)}$  time without repeating a configuration and looping (for some c).

Corollary:  $P \subseteq PSPACE$ 

Theorem:  $NP \subseteq PSPACE$  [next slide]

### $NP \subseteq PSPACE$

**Theorem:** NP ⊆ PSPACE

Proof:

1.  $SAT \in PSPACE$ 

2. If  $A \leq_{\mathbf{P}} B$  and  $B \in \mathsf{PSPACE}$  then  $A \in \mathsf{PSPACE}$ 

**Defn:**  $coNP = \{\overline{A} \mid A \in NP\}$ 

 $HAMPATH \in coNP$ 

 $TAUTOLOGY = \{\langle \phi \rangle | \text{ all assignments satisfy } \phi \} \in coNP$ 

 $conP \subseteq PSPACE$  (because PSPACE = copspace)

P = PSPACE ? Not known.

Or possibly:

$$P = NP = coNP = PSPACE$$

## Example: TQBF

**Defn:** A <u>quantified Boolean formula</u> (QBF) is a Boolean formula with leading exists  $(\exists x)$  and for all  $(\forall x)$  quantifiers. All variables must lie within the scope of a quantifier.

A QBF is True or False.

**Examples:** 
$$\phi_1 = \forall x \exists y [(x \lor y) \land (\overline{x} \lor \overline{y})]$$
  
 $\phi_2 = \exists y \forall x [(x \lor y) \land (\overline{x} \lor \overline{y})]$ 

Defn:  $TQBF = \{\langle \phi \rangle | \phi \text{ is a QBF that is TRUE} \}$ 

Thus  $\phi_1 \in TQBF$  and  $\phi_2 \notin TQBF$ .

**Theorem:**  $TQBF \in PSPACE$ 

#### Check-in 17.2

How is *SAT* a special case of *TQBF*?

- (a) Remove all quantifiers.
- (b) Add  $\exists$  and  $\forall$  quantifiers.
- (c) Add only ∃ quantifiers.
- (d) Add only ∀ quantifiers.

## $TQBF \in PSPACE$

**Theorem:**  $TQBF \in PSPACE$ 

Proof: "On input  $\langle \phi \rangle$ 

- 1. If  $\phi$  has no quantifiers, then  $\phi$  has no variables so either  $\phi$  = True or  $\phi$  = False. Output accordingly.
- 2. If  $\phi = \exists x \ \psi$  then evaluate  $\psi$  with x = True and x = False recursively. Accept if either accepts. Reject if not.
- 3. If  $\phi = \forall x \ \psi$  then evaluate  $\psi$  with x = True and x = False recursively. Accept if both accept. Reject if not."

#### Space analysis:

Each recursive level uses constant space (to record the x value). The recursion depth is the number of quantifiers, at most  $n = |\langle \phi \rangle|$ .

So  $TQBF \in SPACE(n)$ 

## Example: Ladder Problem

A <u>ladder</u> is a sequence of strings of a common length where consecutive strings differ in a single symbol.

A <u>word ladder for English</u> is a ladder of English words.

Let A be a language. A ladder in A is a ladder of strings in A.

**Defn:**  $LADDER_{DFA} = \{\langle B, u, v \rangle | B \text{ is a DFA and } L(B) \text{ contains a ladder } y_1, y_2, \dots, y_k \text{ where } y_1 = u \text{ and } y_k = v \}.$ 

**Theorem:**  $LADDER_{DFA} \in NPSPACE$ 

WORK
PORT
SORT
SOOT
SLOT
PLOT
PLOY
PLAY

## $LADDER_{DFA} \in NPSPACE$

Theorem:  $LADDER_{DFA} \in NPSPACE$ 

Proof idea: Nondeterministically guess the sequence from u to v.

Careful- (a) cannot store sequence, (b) must terminate.

Proof: "On input  $\langle B, u, v \rangle$ 

- 1. Let y = u and let m = |u|.
- 2. Repeat at most t times where  $t = |\Sigma|^m$ .
- 3. Nondeterministically change one symbol in y.
- 4. Reject if  $y \notin L(B)$ .
- 5. Accept if y = v.
- 6. *Reject* [exceeded *t* steps].

Space used is for storing y and t.

 $LADDER_{DFA} \in NSPACE(n)$ .

Theorem:  $LADDER_{DFA} \in PSPACE$  (!)

## $LADDER_{DFA} \in PSPACE$

Theorem:  $LADDER_{DFA} \in SPACE(n^2)$ 

Proof: Write  $u \stackrel{v}{\rightarrow} v$  if there's a ladder from u to v of length  $\leq b$ .

Here's a recursive procedure to solve the bounded DFA ladder problem:

 $BOUNDED-LADDER_{DFA} = \{\langle B, u, v, b \rangle | B \text{ a DFA and } u \xrightarrow{b} v \text{ by a ladder in } L(B) \}$ 

B-L = "On input  $\langle B, u, v, b \rangle$  Let m = |u| = |v|.

- 1. For b=1, accept if  $u,v\in L(B)$  and differ in  $\leq 1$  place, else reject.
- 2. For b > 1, repeat for each w of length |u|
- 3. Recursively test  $u \xrightarrow{b/2} w$  and  $w \xrightarrow{b/2} v$  [division rounds up]
- 4. *Accept* both accept.
- 5. Reject [if all fail]."

Test  $\langle B, u, v \rangle \in LADDER_{DFA}$  with B-L procedure on input  $\langle B, u, v, t \rangle$  for  $t = |\Sigma|^m$ 

#### Space analysis:

Each recursive level uses space O(n) (to record w).

Recursion depth is  $\log t = O(m) = O(n)$ .

Total space used is  $O(n^2)$ .

#### Check-in 17.3

Find an English word ladder connecting MUST and VOTE.

- (a) Already did it.
- (b) I will.

## Quick review of today

- 1. Space complexity
- 2. SPACE(f(n)), NSPACE(f(n))
- 3. PSPACE, NPSPACE
- 4. Relationship with TIME classes
- 5.  $TQBF \in PSPACE$
- 6.  $LADDER_{DFA} \in NSPACE(n)$
- 7.  $LADDER_{DFA} \in SPACE(n^2)$

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

### 18.404/6.840 Lecture 18

#### Last time:

- Space complexity
- SPACE(f(n)), NSPACE(f(n)), PSPACE, NPSPACE
- Relationship with TIME classes

### Today: (Sipser §8.3)

- Review  $LADDER_{DFA} \in PSPACE$
- Savitch's Theorem:  $NSPACE(f(n)) \subseteq SPACE(f^2(n))$
- PSPACE-completeness
- TQBF is PSPACE-complete

### Review: SPACE Complexity

**Defn:** Let  $f: \mathbb{N} \to \mathbb{N}$  where  $f(n) \ge n$ . Say TM M runs in space f(n) if M always halts and uses at most f(n) tape cells on all inputs of length n.

An NTM M runs in space f(n) if all branches halt and each branch uses at most f(n) tape cells on all inputs of length n.

 $\begin{aligned} & \mathsf{SPACE}\big(f(n)\big) = \{B \mid \mathsf{some} \ 1\text{-tape} \ \mathsf{TM} \ \mathsf{decides} \ B \ \mathsf{in} \ \mathsf{space} \ \mathcal{O}\big(f(n)\big) \} \\ & \mathsf{NSPACE}\big(f(n)\big) = \{B \mid \mathsf{some} \ 1\text{-tape} \ \mathsf{NTM} \ \mathsf{decides} \ B \ \mathsf{in} \ \mathsf{space} \ \mathcal{O}\big(f(n)\big) \} \end{aligned}$ 

 $\begin{aligned} \mathsf{PSPACE} &= \ \bigcup_k \mathsf{SPACE}(n^k) \quad \text{``polynomial space''} \\ \mathsf{NPSPACE} &= \ \bigcup_k \mathsf{NSPACE}(n^k) \quad \text{``nondeterministic polynomial space''} \end{aligned}$ 

Today: PSPACE = NPSPACE

Or possibly: (P = NP = coNP = PSPACE)

## Review: $LADDER_{DFA} \in PSPACE$

Theorem:  $LADDER_{DFA} \in SPACE(n^2)$ 

Proof: Write  $u \stackrel{v}{\rightarrow} v$  if there's a ladder from u to v of length  $\leq b$ .

Here's a recursive procedure to solve the bounded DFA ladder problem:

 $BOUNDED-LADDER_{DFA} = \{\langle B, u, v, b \rangle | B \text{ a DFA and } u \xrightarrow{b} v \text{ by a ladder in } L(B) \}$ 

 $B-L = \text{"On input } \langle B, u, v, b \rangle$  Let m = |u| = |v|.

- 1. For b=1, accept if  $u,v\in L(B)$  and differ in  $\leq 1$  place, else reject.
- 2. For b > 1, repeat for each  $w \in L(B)$  of length |u|
- 3. Recursively test  $u \xrightarrow{b/2} w$  and  $w \xrightarrow{b/2} v$  [division rounds up]
- 4. *Accept* both accept.
- 5. Reject [if all fail]."

Test  $\langle B, u, v \rangle \in LADDER_{DFA}$  with B-L procedure on input  $\langle B, u, v, t \rangle$  for  $t = |\Sigma|^m$ 

#### Space analysis:

Each recursive level uses space O(n) (to record w). Recursion depth is  $\log t = O(m) = O(n)$ .

Total space used is  $O(n^2)$ .

recurse

recurse

**WORK** 

BOAR

ARRE

**BAAA** 

**PLAY** 

### PSPACE = NPSPACE

Savitch's Theorem: For  $f(n) \ge n$ ,  $\mathsf{NSPACE}(f(n)) \subseteq \mathsf{SPACE}(f^2(n))$ 

Proof: Convert NTM N to equivalent TM M, only squaring the space used.

For configurations  $c_i$  and  $c_j$  of N, write  $c_i \stackrel{b}{\rightarrow} c_j$  if can get from  $c_i$  to  $c_j$  in  $\leq b$  steps.

Give recursive algorithm to test  $c_i \stackrel{b}{\rightarrow} c_j$ :

M ="On input  $c_i, c_j, b$  [goal is to check  $c_i \xrightarrow{b} c_j$ ]

- 1. If b = 1, check directly by using N's program and answer accordingly.
- 2. If b > 1, repeat for all configurations  $c_{\text{mid}}$  that use f(n) space.
- 3. Recursively test  $c_i \xrightarrow{b/2} c_{\mathrm{mid}}$  and  $c_{\mathrm{mid}} \xrightarrow{b/2} c_j$
- 4. If both are true, *accept*. If not, continue.
- 5. Reject if haven't yet accepted."

Test if N accepts w by testing  $c_{\text{start}} \xrightarrow{\iota} c_{\text{accept}}$  where t = number of configurations

 $= |Q| \times f(n) \times d^{f(n)}$ 

Each recursion level stores 1 config = O(f(n)) space.

Number of levels =  $\log t = O(f(n))$ . Total  $O(f^2(n))$  space.

### **PSPACE-completeness**

**Defn:** *B* is <u>PSPACE-complete</u> if

- 1)  $B \in PSPACE$
- 2) For all  $A \in PSPACE$ ,  $A \leq_P B$

If B is PSPACE-complete and  $B \in P$  then P = PSPACE.

#### Check-in 18.1

Knowing that TQBF is PSPACE-complete, what can we conclude if  $TQBF \in NP$ ? Check all that apply.

- (a) P = PSPACE
- (b) NP = PSPACE
- (c) P = NP
- (d) NP = coNP

Think of complete problems as the "hardest" in their associated class.

Check-in 18.1

## TQBF is PSPACE-complete

```
Recall: TQBF = \{\langle \phi \rangle | \phi \text{ is a QBF that is True} \}

Examples: \phi_1 = \forall x \exists y \left[ (x \lor y) \land (\overline{x} \lor \overline{y}) \right] \in TQBF [True] \phi_2 = \exists y \forall x \left[ (x \lor y) \land (\overline{x} \lor \overline{y}) \right] \notin TQBF [FALSE]

Theorem: TQBF is PSPACE-complete

Proof: 1) TQBF \in PSPACE \checkmark
2) For all A \in PSPACE, A \leq_P TQBF

Let A \in PSPACE be decided by TM M in space n^k.

Give a polynomial-time reduction f mapping f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f to f
```

# Constructing $\phi_{M,w}$ : 1st try

#### Tableau for *M* on *w*

Recall: A tableau for M on w represents a computation history for M on w when M accepts w.

Rows of that tableau are configurations.

M runs in space  $n^k$ , its tableau has:

- $n^k$  columns (max size of a configuration)
- $d^{(n^k)}$  rows (max number of steps)

Constructing  $\phi_{M,w}$ . Try Cook-Levin method.

Then  $\phi_{M,w}$  will be as big as tableau.

But that is exponential:  $n^k \times d^{(n^k)}$ .

Too big! 😊

# Constructing $\phi_{M,w}$ : 2<sup>nd</sup> try

For configs  $c_i$  and  $c_j$  construct  $\phi_{c_i, c_j, b}$  which "says"  $c_i \xrightarrow{\varepsilon} c_j$  recursively.

$$\phi_{c_i, c_j, b} = \exists c_{\text{mid}} \left[ \phi_{c_i, c_{\text{mid}}, b/2} \land \phi_{c_{\text{mid}}, c_j, b/2} \right]$$

$$\exists x_1, x_2, \cdots, c_l$$
  
as in Cook-Levin

$$\exists c_{\mathrm{mid}} [\phi_{\text{,,b/4}} \land \phi_{\text{,,b/4}}] \quad \exists c_{\mathrm{mid}} [\phi_{\text{,,b/4}} \land \phi_{\text{,,b/4}}]$$

### Check-in 18.2

Why shouldn't we be surprised that this construction fails?

- (a) We can't define a QBF by using recursion.
- It doesn't use ∀ anywhere.
- We know that  $TQBF \notin P$ .

 $\phi_{...1}$  defined as in Cook-Levin

$$\vdots \exists c_{\text{mid}} [\phi_{,,b/8} \cdots]$$

$$\phi_{M,w} = \phi_{c_{\text{start}}, c_{\text{accept}}, t}$$
 $t = d^{(n^k)}$ 

#### Size analysis:

Each recursive level doubles number of QBFs. Number of levels is  $\log d^{(n^k)} = O(n^k)$ .

 $\rightarrow$  Size is exponential.  $\odot$ 

Check-in 18.2

# Constructing $\phi_{M,w}$ : 3<sup>rd</sup> try

$$\phi_{c_i, c_j, b} = \exists c_{\text{mid}} \left[ \phi_{c_i, c_{\text{mid}}, b/2} \land \phi_{c_{\text{mid}}, c_j, b/2} \right]$$

$$\forall (c_g, c_h) \in \left\{ \left( c_i, c_{\text{mid}} \right), \left( c_{\text{mid}}, c_j \right) \right\} \left[ \phi_{c_g, c_h, b/2} \right] \quad \forall (x \in S) \left[ \psi \right]$$
 is equivalent to

$$\forall (x \in S) [ \psi ]$$
\nis equivalent to
$$\forall x [(x \in S) \rightarrow \psi]$$

$$\phi_{M,w} = \phi_{c_{\text{start}}, c_{\text{accept}}, t}$$

$$t = d^{(n^k)}$$

Check-in 18.3

#### Size analysis:

Each recursive level <u>adds</u>  $O(n^k)$  to the QBF. Number of levels is  $\log d^{(n^k)} = O(n^k)$ .

$$\Rightarrow$$
 Size is  $O(n^k \times n^k) = O(n^{2k})$   $\odot$ 

Would this construction still work if M were nondeterministic?

 $\phi_{...1}$  defined as in Cook-Levin

- (a) Yes.
- (b) No.

Check-in 18.3

## Quick review of today

- 1.  $LADDER_{DFA} \in PSPACE$
- 2. Savitch's Theorem:  $NSPACE(f(n)) \subseteq SPACE(f^2(n))$
- 3. TQBF is PSPACE-complete

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

### 18.404/6.840 Lecture 19

### Last time:

- Review  $LADDER_{DFA} \in PSPACE$
- Savitch's Theorem:  $NSPACE(f(n)) \subseteq SPACE(f^2(n))$
- TQBF is PSPACE-complete

**Today:** (Sipser §8.3 – §8.4)

- Games and Quantifiers
- The Formula Game
- Generalized Geography is PSPACE-complete
- Logspace: Land NL

# Games and Complexity

**Generalized Geography Game** 

Played on any directed graph.
Players take turns picking nodes that form a simple path.
The first player stuck loses.

**Defn:**  $GG = \{\langle G, a \rangle | \text{ Player I has a } \underline{\text{forced win}} \text{ in } Generalized Geography on graph } G \text{ starting at node } a \}.$ 

"forced win" also called a "winning strategy" means that the player will win if both players play optimally.

**Theorem:** GG is PSPACE-complete

Oregon

### **Games and Quantifiers**

### The Formula Game

 $\psi$   $(\cdots) \wedge \cdots \wedge (\cdots) 1$ 

Given QBF  $\phi = \exists x_1 \ \forall x_2 \ \exists x_3 \ \cdots (\exists / \forall) x_k \ [\ (\cdots) \land \cdots \land (\cdots) \ ]$ There are two Players "∃" and "∀".

Player ∃ assigns values to the ∃-quantified variables.

Player ∀ assigns values to the ∀-quantified variables.

The players choose the values according to the order of the quantifiers in  $\phi$ .

After all variables have been assigned values, we determine the winner: Player  $\exists$  wins if the assignment satisfies  $\psi$ .

Player ∀ wins if not.

**Claim:** Player  $\exists$  has a forced win in the formula game on  $\phi$  iff  $\phi$  is TRUE. Therefore  $\{\langle \phi \rangle | \text{ Player } \exists \text{ has a forced win on } \phi\} = TQBF$ .

Next: show  $TQBF \leq_P GG$ .

### Check-in 19.2

Which player has a winning strategy in the formula game on

$$\phi = \exists x \, \forall y \, [(x \vee y) \wedge (\overline{x} \vee \overline{y})]$$

- (a) ∃-player
- (b) ∀-player
- (c) Neither player

## GG is PSPACE-complete

**Theorem:** *GG* is PSPACE-complete

Proof: 1)  $GG \in PSPACE$  (recursive algorithm, exercise)

2)  $TQBF \leq_{P} GG$ 

Give reduction f from TQBF to GG.  $f(\langle \phi \rangle) = \langle G, a \rangle$ 

Construct G to mimic the formula game on  $\phi$ .

G has Players I and II

Player I plays role of  $\exists$ -Player in  $\phi$ . Ditto for Player II and the  $\forall$ -Player.

$$\phi = \exists x_1 \ \forall x_2 \ \exists x_3 \ \cdots (\exists/\forall) x_k \ [\ (\cdots) \land \cdots \land (\cdots) \ ]$$

$$G = \bigcirc$$
assume in cnf

# Constructing the GG graph G

### Illustrate construction by example

#### **Endgame**

∃ should win if assignment satisfied all clauses ∀ should win if some unsatisfied clause

### **Implementation**

∀ picks clause node claimed unsatisfied ∃ picks literal node claimed to satisfy the clause liar will be stuck

### Log space

To define sublinear space computation, do not count input as part of space used. Use 2-tape TM model with read-only input tape.

**Defn:** L = SPACE( $\log n$ )  $NL = NSPACE(\log n)$ 

Log space can represent a constant number of pointers into the input.

Examples

- $\{ww^{\mathcal{R}} \mid w \in \Sigma^*\} \in \mathsf{L}$
- $PATH \in NL$

Nondeterministically select the nodes of a path connecting s to t.

NL

## Log space properties

**Theorem:**  $L \subseteq P$ 

Proof: Say M decides A in space  $O(\log n)$ .

**Defn:** A configuration for M on w is  $(q, p_1, p_2, t)$  where q is a state,  $p_1$  and  $p_2$  are the tape head positions, and t is the tape contents. The number of such configurations is  $|Q| \times n \times O(\log n) \times d^{O(\log n)} = O(n^k)$  for some k.

Therefore M runs in polynomial time.

Conclusion:  $A \in P$ 

Theorem:  $NL \subseteq SPACE(\log^2 n)$ 

Proof: Savitch's theorem works for log space

### NL properties

Theorem:  $NL \subseteq P$ 

Proof: Say NTM M decides A in space  $O(\log n)$ .

**Defn:** The <u>configuration graph</u>  $G_{M,w}$  for M on w has

**nodes:** all configurations for *M* on *w* 

**edges:** edge from  $c_i \rightarrow c_j$  if  $c_i$  can yield  $c_j$  in 1 step.

Claim: M accepts w iff the configuration graph  $G_{M,w}$ 

has a path from  $c_{\rm start}$  to  $c_{\rm accept}$ 

Polynomial time algorithm *T* for *A*:

T = "On input w

- 1. Construct the  $G_{M,w}$ .
- 2. Accept if there is a path from  $c_{\rm start}$  to  $c_{\rm accept}$ . Reject if not."

# Quick review of today

- 1. The Formula Game
- 2. Generalized Geography is PSPACE-complete
- 3. Log space: L and NL
- 4. Configuration graph
- 5. NL ⊆ P

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

### 18.404/6.840 Lecture 20

#### Last time:

- Games and Quantifiers
- Generalized Geography is PSPACE-complete
- Logspace: Land NL

Today: (Sipser §8.4)

- Review NL ⊆ P
- Review NL  $\subseteq$  SPACE( $\log^2 n$ )
- NL-completeness
- -NL = coNL

#### Review: log space

**Model:** 2-tape TM with read-only input tape for defining sublinear space computation.

**Defn:** L = SPACE( $\log n$ )

 $NL = NSPACE(\log n)$ 

Log space can represent a constant number of pointers into the input.

#### **Examples**

- 1.  $\{ww^{\mathcal{R}} \mid w \in \Sigma^*\} \in \mathsf{L}$
- 2.  $PATH \in NL$

Nondeterministically select the nodes of a path connecting s to t.

#### Review: L⊆P

**Theorem:**  $L \subseteq P$ 

Proof: Say M decides A in space  $O(\log n)$ .

**Defn:** A configuration for M on w is  $(q, p_1, p_2, t)$  where q is a state,  $p_1$  and  $p_2$  are the tape head positions, and t is the work tape contents.

The number of such configurations is  $|Q| \times n \times O(\log n) \times d^{O(\log n)} = O(n^k)$  for some k.

Therefore M runs in polynomial time.

Conclusion:  $A \in P$ 

# Review: $NL \subseteq SPACE(\log^2 n)$

Theorem:  $NL \subseteq SPACE(\log^2 n)$ 

Proof: Savitch's theorem works for log space

Each recursion level stores 1 config =  $O(\log n)$  space.

Number of levels =  $\log t = O(\log n)$ .

Total  $O(\log^2 n)$  space.

#### Review: NL ⊆ P

Theorem:  $NL \subseteq P$ 

Proof: Say NTM M decides A in space  $O(\log n)$ .

**Defn:** The <u>configuration graph</u>  $G_{M,W}$  for M on W has

**nodes:** all configurations for M on w

**edges:** edge from  $c_i \rightarrow c_j$  if  $c_i$  can yield  $c_j$  in 1 step.

**Claim:** M accepts w iff the configuration graph  $G_{M,w}$ 

has a path from  $c_{\rm start}$  to  $c_{\rm accept}$ 

Polynomial time algorithm *T* for *A*:

T = "On input w

- 1. Construct  $G_{M,W}$ . [polynomial size]
- 2. Accept if there is a path from  $c_{\rm start}$  to  $c_{\rm accept}$ . Reject if not."

#### **NL-completeness**

#### Check-in 20.1

If T is a log-space transducer that computes f, then for inputs w of length n, how long can f(w) be?

(a) at most  $O(\log n)$ 

(d) at most  $2^{O(n)}$ 

(b) at most O(n)

(e) any length

(c) at most polynomial in n

**Defn:** A <u>log-space transducer</u> is a TM with three tapes:

- 1. read-only input tape of size n
- 2. read/write work tape of size  $O(\log n)$
- 3. write-only output tape

A log-space transducer T computes a function  $f: \Sigma^* \to \Sigma^*$  if T on input w halts with f(w) on its output tape for all w. Say that f is computable in log-space.

**Defn:** A is <u>log-space reducible</u> to B ( $A \leq_L B$ ) if  $A \leq_m B$  by a reduction function that is computable in log-space.

**Theorem:** If  $A \leq_{\mathbf{L}} B$  and  $B \in \mathbf{L}$  then  $A \in \mathbf{L}$  Proof: TM for A = "On input w

- 1. Compute f(w)
- 2. Run decider for B on f(w). Output same."

BUT we don't have space to store f(w). So, (re-)compute symbols of f(w) as needed.

Check-in 20.1

### PATH is NL-complete

**Theorem:** *PATH* is NL-complete

Proof: 1)  $PATH \in NL \checkmark$ 

2) For all  $A \in NL$ ,  $A \leq_L PATH$ 

Let  $A \in NL$  be decided by NTM M in space  $O(\log n)$ .

[Modify M to erase work tape and move heads to left end upon accepting.]

Give a log-space reduction f mapping A to PATH.

$$f(w) = \langle G, s, t \rangle$$

 $w \in A$  iff G has a path from s to t

Here is a log-space transducer T to compute f in log-space.

T = "on input w

- 1. For all pairs  $c_i$ ,  $c_j$  of configurations of M on w.
- 2. Output those pairs which are legal moves for M.
- 3. Output  $c_{\text{start}}$  and  $c_{\text{accept}}$ ."

# $\overline{2SAT}$ is NL-complete

**Theorem:**  $\overline{2SAT}$  is NL-complete

Proof: 1) Show  $2SAT \in NL$  good exercise

2) Show  $PATH \leq_L \overline{2SAT}$ 

Give log-space reduction f from PATH to  $\overline{2SAT}$ .

$$f(\langle G, s, t \rangle) = \langle \phi \rangle$$

For each node u in G put a variable  $x_u$  in  $\phi$ .

For each edge (u, v) in G, put a clause  $(x_u \to x_v)$  in  $\phi$  [equivalent to  $(\overline{x_u} \lor x_v)$ ]. In addition put the clauses  $(x_s \lor x_s)$  and  $(x_t \to \overline{x_s})$  in  $\phi$ .

Show G has an path from s to t iff  $\phi$  is unsatisfiable.

- $(\rightarrow)$  Follow implications to get a contradiction.
- ( $\leftarrow$ ) If G has no path from s to t, then assign all  $x_u$  TRUE where u is reachable from s, and all other variables FALSE. That gives a satisfying assignment to  $\phi$ .

Straightforward to show f is computable in log-space.

## NL = coNL (part 1/4)

**Theorem** (Immerman-Szelepcsényi): NL = coNL

Proof: Show  $\overline{PATH} \in NL$ 

**Defn:** NTM M computes function  $f: \Sigma^* \to \Sigma^*$  if for all w

1) All branches of M on w halt with f(w) on the tape or reject.

2) Some branch of *M* on *w* does not reject.

Let 
$$path(G, s, t) = \begin{cases} YES, & \text{if } G \text{ has a path from } s \text{ to } t \\ NO, & \text{if not} \end{cases}$$

Let 
$$R = R(G, s) = \{u \mid path(G, s, u) = YES\}$$

Let 
$$c = c(G, s) = |R|$$

R = Reachable nodes c = # reachable

#### Check-in 20.2

Consider the statements:

- (1)  $\overline{PATH} \in NL$ , and
- (2) Some NL-machine computes the *path* function.

What implications can we prove *easily*?

- (a)  $(1) \rightarrow (2)$  only
- (b)  $(2) \rightarrow (1)$  only
- (c) Both implications
- (d) Neither implication

### NL = coNL (part 2/4) - key idea

**Theorem:** If some NL-machine computes c, then some NL-machine computes path.

Proof: "On input  $\langle G, s, t \rangle$ 

- 1. Compute *c*
- 2.  $k \leftarrow 0$
- 3. For each node u
- 4. Nondeterministically go to (p) or (n)
  - (p) Nondeterministically pick a path from s to u of length  $\leq m$ . If fail, then reject.

If u = t, then output YES, else set  $k \leftarrow k + 1$ .

- (n) Skip u and continue.
- 5. If  $k \neq c$  then reject.
- 6. Output NO." [found all c reachable nodes and none were t}

## NL = coNL (part 3/4)

```
Let path_d(G,s,t) = \begin{cases} \text{YES, if } G \text{ has a path } s \text{ to } t \text{ of length} \leq d \\ \text{NO, if not} \end{cases} Let R_d = R_d(G,s) = \{u \mid path_d(G,s,u) = \text{YES}\} Let c_d = c_d(G,s) = |R_d|
```

**Theorem:** If some NL-machine computes  $c_d$ , then some NL-machine computes  $path_d$ .

Proof: "On input  $\langle G, s, t \rangle$ 

- 1. Compute  $c_d$
- 2.  $k \leftarrow 0$
- 3. For each node u
- 4. Nondeterministically go to (p) or (n)
  - (p) Nondeterministically pick a path from s to u of length  $\leq d$ . If fail, then reject.
    - If u = t, then output YES, else set  $k \leftarrow k + 1$ .
  - (n) Skip u and continue.
- 5. If  $k \neq c_d$  then reject.
- 6. Output NO" [found all  $c_d$  reachable nodes and none were t}

### NL = coNL (part 4/4)

**Theorem:** If some NL-machine computes  $c_d$ , then some NL-machine computes  $path_{d+1}$ .

Proof: "On input  $\langle G, s, t \rangle$ 

- 1. Compute *c*
- 2.  $k \leftarrow 0$
- 3. For each node u
- 4. Nondeterministically go to (p) or (n)
  - (p) Nondeterministically pick a path from s to u of length  $\leq d$ . If fail, then reject.

If u has an edge to t, then output YES, else set  $k \leftarrow k + 1$ .

- (n) Skip u and continue.
- 5. If  $k \neq c_d$  then reject.
- 6. Output NO." [found all  $c_d$  reachable nodes and none had an edge to t}

**Corollary:** Some NL-machine computes  $c_{d+1}$  from  $c_d$ .

#### Check-in 20.3

Can we now show 2SAT is NL-complete?

- (a) No.
- (b) Yes.

Yes:  $\overline{PATH} \leq_{L} PATH \& PATH \leq_{L} \overline{2SAT}$ So  $\overline{PATH} \leq_{L} \overline{2SAT}$  thus  $PATH \leq_{L} 2SAT$ 

## Quick review of today

- 1. Log-space reducibility
- 2. L = NL? question
- 3. *PATH* is NL-complete
- 4.  $\overline{2SAT}$  is NL-complete
- 5. NL = coNL

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

#### 18.404/6.840 Lecture 21

#### Last time:

- Log-space reducibility
- L = NL? question
- PATH is NL-complete
- $\overline{2SAT}$  is NL-complete
- NL = coNL (unfinished)

#### Today: (Sipser §9.1)

- Finish NL = coNL
- Time and Space Hierarchy Theorems

### NL = coNL (part 1/4)

**Theorem** (Immerman-Szelepcsényi): NL = coNL

Proof: Show  $\overline{PATH} \in NL$ 

**Defn:** NTM M computes function  $f: \Sigma^* \to \Sigma^*$  if for all w

- 1) All branches of M on w halt with f(w) on the tape or reject.
- 2) Some branch of *M* on *w* does not reject.

Let 
$$path(G, s, t) = \begin{cases} YES, & \text{if } G \text{ has a path from } s \text{ to } t \\ NO, & \text{if not} \end{cases}$$

Let 
$$R = R(G, s) = \{u \mid path(G, s, u) = YES\}$$

Let 
$$c = c(G, s) = |R|$$

R = Reachable nodes c = # reachable

#### Check-in 21.1

Let *G* be the graph below.

What is the value of c = c(G, s)?

- (a) 2
- (e)  $\epsilon$
- (b) 3
- (f) 7
- (c) 4
- (g) 8
- (d) 5
- (h) 9

### NL = coNL (part 2/4) - key idea

**Theorem:** If some NL-machine computes c, then some NL-machine computes path.

Proof: "On input  $\langle G, s, t \rangle$  where G has m nodes

- 1. Compute *c*
- 2.  $k \leftarrow 0$
- 3. For each node u
- 4. Nondeterministically go to (p) or (n)
  - (p) Nondeterministically pick a path from s to u of length  $\leq m$ . If fail, then reject.

If u = t, then output YES, else set  $k \leftarrow k + 1$ .

- (n) Skip u and continue.
- 5. If  $k \neq c$  then reject.
- 6. Output NO." [found all c reachable nodes and none were t}

# NL = coNL (part 2/4) – key idea SIMPLIFIED!!

**Theorem:** If some NL-machine computes c, then some NL-machine computes path.

Proof: "On input (G, s, t) where G has m nodes

- 1. Compute *c*
- 2.  $k \leftarrow 0$
- 3. For each node u
- 4. Nondeterministically pick a path from s of length  $\leq m$ . If it ends at t then output YES and stop. If it ends at u, set  $k \leftarrow k+1$ .
- 5. If  $k \neq c$  then reject.
- 6. Output NO." [found all c reachable nodes and none were t}

### NL = coNL (part 3/4)

```
 \text{Let } path_d(G,s,t) = \begin{cases} \text{YES, if } G \text{ has a path } s \text{ to } t \text{ of length} \leq d \\ \text{NO, if not} \end{cases}   \text{Let } R_d = R_d(G,s) = \{u \mid path_d(G,s,u) = \text{YES}\}   \text{Let } c_d = c_d(G,s) = |R_d|
```

**Theorem:** If some NL-machine computes  $c_d$ , then some NL-machine computes  $path_d$ .

Proof: "On input  $\langle G, s, t \rangle$ 

- 1. Compute  $c_d$
- 2.  $k \leftarrow 0$
- 3. For each node u
- 4. Nondeterministically go to (p) or (n)
  - (p) Nondeterministically pick a path from s to u of length  $\leq d$ . If fail, then reject.

If u = t, then output YES, else set  $k \leftarrow k + 1$ .

- (n) Skip u and continue.
- 5. If  $k \neq c_d$  then reject.
- 6. Output NO" [found all  $c_d$  reachable nodes and none were t}

### NL = coNL (part 4/4)

**Theorem:** If some NL-machine computes  $c_d$ , then some NL-machine computes  $path_{d+1}$ .

Proof: "On input  $\langle G, s, t \rangle$ 

- 1. Compute *c*
- 2.  $k \leftarrow 0$
- 3. For each node u
- 4. Nondeterministically go to (p) or (n)
  - (p) Nondeterministically pick a path from s to u of length  $\leq d$ . If fail, then reject.

If u has an edge to t, then output YES, else set  $k \leftarrow k + 1$ .

- (n) Skip u and continue.
- 5. If  $k \neq c_d$  then reject.
- 6. Output NO." [found all  $c_d$  reachable nodes and none had an edge to t}

**Corollary:** Some NL-machine computes  $c_{d+1}$  from  $c_d$ .

Hence  $\overline{PATH} \in NL$ 

"On input  $\langle G, s, t \rangle$ 

- 1.  $c_0 = 1$ .
- 2. Compute each  $c_{d+1}$  from  $c_d$  for d=1 to m.
- 3. Accept if  $path_m(G, s, t) = NO$ .
- 4. Reject if  $path_m(G, s, t) = YES$ ."

#### Review: Major Complexity Classes

$$L \subseteq NL \subseteq P \subseteq NP \subseteq PSPACE$$

$$\downarrow \qquad \qquad \neq \qquad \qquad \downarrow$$

$$Today$$

The time and space hierarchy theorems show that if a TM is given more time (or space) then it can do more.\*

\* certain restrictions apply.

```
For example:
```

```
\mathsf{TIME}(n^2) \subsetneq \mathsf{TIME}(n^3) \quad [ \subsetneq \mathsf{means} \; \mathsf{proper} \; \mathsf{subset} \, ] \mathsf{SPACE}(n^2) \subsetneq \mathsf{SPACE}(n^3)
```

# Space Hierarchy Theorem (1/2)

**Theorem:** For any  $f: \mathbb{N} \to \mathbb{N}$  (where f satisfies a technical condition)

there is a language A where A requires O(f(n)) space, i.e,

- 1) A is decidable in O(f(n)) space, and
- 2) A is not decidable in o(f(n)) space

On other words,  $SPACE(o(f(n))) \subseteq SPACE(f(n))$ 

**Notation:** SPACE $(o(f(n))) = \{B \mid \text{ some TM } M \text{ decides } B \text{ in space } o(f(n))\}$ 

#### **Proof outline: (Diagonalization)**

Give TM D where

- 1) D runs in O(f(n)) space
- 2) D ensures that  $L(D) \neq L(M)$  for every TM M that runs in o(f(n)) space.

Let 
$$A = L(D)$$
.

# Space Hierarchy Theorem (2/2)

 $(2/2) \qquad \qquad f(n) \qquad \qquad \text{Mark off}$  f(n) tape  $w = w010110 \cdots 10100000 - \#$  (M)

**Goal:** Exhibit  $A \in SPACE(f(n))$  but  $A \notin SPACE(o(f(n)))$ 

Give D where A = L(D) and

- 1) D runs in O(f(n)) space -
- 2) D ensures that  $L(D) \neq L(M)$  for every TM M that runs in o(f(n)) space.

#### D = "On input w

- 1. Mark off f(n) tape cells where n = |w|. If ever try to use more tape, reject.
- 2. If  $w \neq \langle M \rangle$  for some TM M, reject.
- 3. Simulate\* *M* on *w* Accept if *M* rejects, Reject if *M* accepts

#### Issues:

1. What if M runs in o(f(n)) space but has a big constant? Then D won't have space to simulate M when w is small. FIX: simulate M on infinitely many w.

#### Check-in 21.2

What happens when we run D on input  $\langle D \rangle 1000000$ ?

- a) It loops
- b) It accepts
- c) It rejects
- d) We get a contradiction
- e) Smoke comes out

<sup>\*</sup>Note: D can simulate M with a constant factor space overhead.

# Time Hierarchy Theorem (1/2)

**Theorem:** For any  $f: \mathbb{N} \to \mathbb{N}$  where f is time constructible there is a language A where A requires O(f(n)) time, i.e,

- 1) A is decidable in O(f(n)) time, and
- 2) A is not decidable in  $o(f(n)/\log(f(n)))$  time

On other words, 
$$TIME\left(o\left(\frac{f(n)}{\log(f(n))}\right)\right) \subsetneq TIME(f(n))$$

**Proof outline:** Give TM *D* where

- 1) D runs in O(f(n)) time
- 2) D ensures that  $L(D) \neq L(M)$  for every TM M that runs in  $o(f(n)/\log(f(n)))$  time .

Let A = L(D).

# Time Hierarchy Theorem (2/2)

**Goal:** Exhibit  $A \in \mathsf{TIME}\big(f(n)\big)$  but  $A \notin \mathsf{TIME}\big(o\big(f(n)/\log\big(f(n)\big)\big)\big)$ 

A = L(D) where

- 1) D runs in O(f(n)) time
- 2) D ensures that  $L(D) \neq L(M)$  for every TM M that runs in  $o(f(n)/\log(f(n)))$  time.

D = "On input w

- 1. Compute f(n).
- 2. If  $w \neq \langle M \rangle 10^*$  for some TM M, reject.
- 3. Simulate\* M on w for  $f(n)/\log(f(n))$  steps. Accept if M rejects, Reject if M accepts or hasn't halted."
- \*Note: D can simulate M with a <u>log factor</u> time overhead due to the step counter.

#### Why do we lose a factor of $\log(f(n))$ ?

D must halt within O(f(n)) time. To do so, D counts the number of steps it uses and stops if the limit is exceeded. The counter has size  $\log(f(n))$  and is stored on the tape. It must be kept near the current head location. Cost of moving it adds a  $O(\log(f(n)))$  overhead factor. So to halt within O(f(n)) time, D stops when the counter reaches  $f(n)/\log(f(n))$ .

#### Recap: Separating Complexity Classes

$$L \subseteq NL \subseteq P \subseteq NP \subseteq PSPACE$$

Space Hierarchy Theorem

 $NL \subseteq SPACE(\log^2 n) \subsetneq SPACE(n) \subseteq PSPACE$ 

#### Check-in 21.3

Consider these two famous unsolved questions:

- 1. Does L = P?
- 2. Does P = PSPACE?

What do the hierarchy theorems tell us about these questions?

- a) Nothing
- b) At least one of these has answer "NO"
- c) At least one of these has answer "YES"

# Quick review of today

- 1. Finish NL = coNL
- 2. Space hierarchy theorem
- 3. Time hierarchy theorem

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 22

#### Last time:

- Finished NL = coNL
- Time and Space Hierarchy Theorems

Today: (Sipser §9.2)

- A "natural" intractable problem
- Oracles and P versus NP

# Review: Hierarchy Theorems

#### **Theorems:**

$$\begin{split} & \mathsf{SPACE}\big(o(f(n))\big) \subsetneq \; \mathsf{SPACE}\big(f(n)\big) \; \text{for space constructible} \; f. \\ & \mathsf{TIME}\Big(o\big(f(n)/\log\big(f(n)\big)\big)\big) \subsetneq \; \mathsf{TIME}\big(f(n)\big) \; \text{for time constructible} \; f. \end{split}$$

#### **Corollary:** NL ⊊ PSPACE

Implies  $TQBF \notin NL$  because the polynomial-time reductions in the proof that TQBF is PSPACE-complete can be done in log space.

#### Check-in 22.1

Which of these are known to be true? Check all that apply.

- (a)  $\mathsf{TIME}(2^n) \subsetneq \mathsf{TIME}(2^{n+1})$
- (b)  $\mathsf{TIME}(2^n) \subsetneq \mathsf{TIME}(2^{2n})$
- (c)  $NTIME(n^2) \subseteq PSPACE$
- (d) NP ⊊ PSPACE

## **Exponential Complexity Classes**

```
Defn: EXPTIME = \bigcup_k \text{TIME}\left(2^{\binom{n^k}{2}}\right)
         EXPSPACE = \bigcup_k \text{SPACE}\left(2^{(n^k)}\right)
                                                            Time Hierarchy Theorem
                                     L \subseteq NL \subseteq P \subseteq NP \subseteq PSPACE \subseteq EXPTIME \subseteq EXPSPACE
                                                              Space Hierarchy Theorem
```

**Defn:** *B* is EXPTIME-complete if

- $B \in \mathsf{EXPTIME}$
- For all  $A \in \mathsf{EXPTIME}, \ A \leq_{\mathsf{P}} B$

Same for EXPSPACE-complete

**Theorem:** If B is EXPTIME-complete then  $B \notin P$ 

**Theorem:** If B is EXPSPACE-complete then  $B \notin PSPACE$  (and  $B \notin P$ )

Next will exhibit an EXPSPACE-complete problem

### A "Natural" Intractable Problem

**Defn:**  $EQ_{REX} = \{\langle R_1, R_2 \rangle | R_1 \text{ and } R_2 \text{ are equivalent regular expressions} \}$ 

**Theorem:**  $EQ_{REX} \in PSPACE$ 

Proof: Later (if time) or exercise (uses Savitch's theorem).

**Notation:** If R is a regular expression write  $R^k$  to mean  $\widehat{RR \cdots R}$  (exponent is written in binary).

**Defn:**  $EQ_{\text{REX}\uparrow} = \{\langle R_1, R_2 \rangle | R_1 \text{ and } R_2 \text{ are equivalent regular expressions with exponentiation} \}$ 

**Theorem:**  $EQ_{REX\uparrow}$  is EXPSPACE-complete

Proof: 1)  $EQ_{REX\uparrow} \in EXPSPACE$ 

2) If  $A \in EXPSPACE$  then  $A \leq_P EQ_{REX}$ 

- 1) Given regular expressions with exponentiation  $R_1$  and  $R_2$ , expand the exponentiation by using repeated concatenation and then use  $EQ_{\text{REX}} \in \text{PSPACE}$ . The expansion is exponentially larger, so gives an EXPSPACE algorithm for  $EQ_{\text{REX}}$ .
- 2) Let  $A \in \mathsf{EXPSPACE}$  be decided by TM M in space  $2^{(n^k)}$ .

Give a polynomial-time reduction f mapping A to  $EQ_{REX\uparrow}$ .

# Showing $A \leq_{\mathbf{P}} EQ_{\mathbf{REX}\uparrow}$

**Theorem:**  $EQ_{REX\uparrow}$  is EXPSPACE-complete

Proof continued: Let  $A \in \mathsf{EXPSPACE}$  decided by TM M in space  $2^{(n^k)}$ .

Give a polynomial-time reduction f mapping A to  $EQ_{REX\uparrow}$ .

$$f(w) = \langle R_1, R_2 \rangle$$
  
 $w \in A \text{ iff } L(R_1) = L(R_2)$ 

Construct  $R_1$  so that  $L(R_1) = \text{all strings } \underbrace{\text{except a rejecting computation history for } M \text{ on } w.$  Construct  $R_2 = \Delta^*$  ( $\Delta$  is the alphabet for computation histories, i.e.,  $\Delta = \Gamma \cup Q \cup \{\#\}$ )

### $R_1$ construction: $R_1 = R_{\text{bad-start}} \cup R_{\text{bad-move}} \cup R_{\text{bad-reject}}$

Rejecting computation history for *M* on *w*:

#### Check-in 22.2

Roughly estimate the size of the rejecting computation history for M on w.

(a) 
$$2^n$$
 (c)  $2^{2^{(n^k)}}$ 

(b) 
$$2^{(n^k)}$$

Check-in 22.2

# $A \leq_{\mathsf{P}} EQ_{\mathsf{REX}\uparrow}$ $(R_{\mathsf{bad-start}})$

Construct  $R_1$  to generate all strings except a rejecting computation history for M on w.

 $R_1 = R_{\text{bad-start}} \cup R_{\text{bad-move}} \cup R_{\text{bad-reject}}$ 

Rejecting computation history for *M* on *w*:

 $R_{\mathrm{bad-start}}$  generates all strings that do not start with  $C_{\mathrm{start}} = q_0 w_1 w_2 \cdots w_n$  ... ...  $R_{\mathrm{bad-start}} = S_0 \cup S_1 \cup S_2 \cup \cdots \cup S_n \cup S_{\mathrm{blanks}} \cup S_{\#}$ 

Remember:  $\Delta$  is the alphabet for computation histories, i.e.,  $\Delta = \Gamma \cup Q \cup \{\#\}$ )

Notation: 
$$\Delta_{\varepsilon} = \Delta \cup \{\varepsilon\}$$

$$\Delta_{-b} = \Delta$$
 without b

$$\Delta^7$$
 = all strings of length 7

$$\Delta_{\varepsilon}^{7} = \text{all strings of length 0 thru 7}$$

$$S_{\text{blanks}} = \Delta^{n+1} \Delta_{\varepsilon}^{2^{(n^k)} - (n+2)} \Delta_{-} \Delta^*$$

all strings of length 
$$n+1$$
 thru  $2^{(n^k)}-1$   $S_{2^{(n^k)}-1}=\Delta^{2^{(n^k)}-1}\Delta$ 

$$S_{1} = \Delta \Delta_{-W_{1}} \Delta^{*}$$

$$S_{2} = \Delta^{2} \Delta_{-W_{2}} \Delta^{*}$$

$$\vdots$$

$$S_{n} = \Delta^{n} \Delta_{-W_{n}} \Delta^{*}$$

$$\begin{cases}
S_{n+1} = \Delta^{n+1} \Delta_{-\Delta} \Delta^{*} \\
\vdots \\
S_{2(n^{k})-1} = \Delta^{2(n^{k})} \Delta_{-\#} \Delta^{*}
\end{cases}$$

$$S_{\#} = \Delta^{2(n^{k})} \Delta_{-\#} \Delta^{*}$$

 $S_0 = \Delta_{-q_0} \Delta^*$ 

# $A \leq_{P} EQ_{REX\uparrow}$ ( $R_{bad-move} \& R_{bad-reject}$ )

Construct  $R_1$  to generate all strings except a rejecting computation history for M on w.

$$R_1 = R_{\text{bad-start}} \cup R_{\text{bad-move}} \cup R_{\text{bad-reject}}$$

Rejecting computation history for M on w:

$$\begin{array}{cccccccccccccccccccccccccccccccccccc$$

 $R_{\rm bad-reject}$  generates all strings that do not contain  $q_{\rm reject}$ 

$$R_{\text{bad-reject}} = \Delta^*_{-q_{\text{reject}}}$$

 $R_{\rm bad-move}$  generates all strings that contain an illegal 2×3 neighborhood

$$R_{\mathrm{bad-move}} = \bigcup_{\substack{\mathrm{illegal} \\ \mathrm{a} \ \mathrm{b} \ \mathrm{c} \\ \mathrm{d} \ \mathrm{e} \ \mathrm{f}}} \left[ \Delta^* \ \mathrm{abc} \ \Delta^{2^{\left(n^k\right)}-2} \ \mathrm{def} \ \Delta^* \right]$$

### Computation with Oracles

Let A be any language.

**Defn:** A TM M with oracle for A, written  $M^A$ , is a TM equipped with a "black box" that can answer queries "is  $x \in A$ ?" for free.

**Example:** A TM with an oracle for SAT can decide all  $B \in NP$  in polynomial time.

**Defn:**  $P^A = \{B \mid B \text{ is decidable in polynomial time with an oracle for } A\}$ Thus  $NP \subseteq P^{SAT}$ 

 $NP = P^{SAT}$ ? Probably No because  $coNP \subseteq P^{SAT}$ 

**Defn:**  $NP^A = \{B \mid B \text{ is decidable in nondeterministic polynomial time with an oracle for }A\}$  Recall  $MIN\text{-}FORMULA = \{\langle \phi \rangle \mid \phi \text{ is a minimal Boolean formula }\}$ 

**Example:**  $\overline{MIN-FORMULA} \in NP^{SAT}$ 

"On input  $\langle \phi \rangle$ 

- 1. Guess shorter formula  $\psi$
- 2. Use SAT oracle to solve the coNP problem:  $\phi$  and  $\psi$  are equivalent
- 3. Accept if  $\phi$  and  $\psi$  are equivalent. Reject if not."

### Oracles and P versus NP

Theorem: There is an oracle A where  $P^A = NP^A$ 

Proof: Let A = TQBF

 $NP^{TQBF} \subseteq NPSPACE = PSPACE \subseteq P^{TQBF}$ 

#### Relevance to the P versus NP question

**Recall:** We showed  $EQ_{REX\uparrow} \notin PSPACE$ . Could we show  $SAT \notin P$  using a similar method?

Reason: Suppose YES.

The Hierarchy Theorems are proved by a diagonalization. In this diagonalization, the TM D simulates some TM M. If both TMs were oracle TMs  $D^A$  and  $M^A$  with the same oracle A. the simulation and the diagonalization would still work. Therefore, if we could prove  $P \neq NP$  by a diagonalization, we would also prove that  $P^A \neq NP^A$  for every oracle A.

But that is false!

#### Check-in 22.3

Which of these are known to be true? Check all that apply.

(a) 
$$P^{SAT} = P^{\overline{SAT}}$$

(b) 
$$NP^{SAT} = coNP^{SAT}$$

(c) 
$$MIN$$
- $FORMULA \in P^{TQBF}$ 

(d) 
$$NP^{TQBF} = coNP^{TQBF}$$

## Quick review of today

- 1. Defined EXPTIME and EXPSPACE
- 2. Defined EXPTIME- and EXPSPACE-completeness
- 3. Showed  $EQ_{\text{REX}\uparrow}$  is EXPSPACE-complete and thus  $EQ_{\text{REX}\uparrow} \notin \text{PSPACE}$
- 4. Defined oracle TMs
- 5. Showed  $P^A = NP^A$  for some oracle A
- 6. Discussed relevance to the P vs NP question

# $EQ_{REX} \in PSPACE$

**Theorem:**  $EQ_{REX} \in PSPACE$ 

Proof: Show  $EQ_{REX} \in NPSPACE$ 

"On input  $\langle R_1, R_2 \rangle$  [ assume alphabet  $\Sigma$  ]

- 1. Convert  $R_1$  and  $R_2$  to equivalent NFAs  $N_1$  and  $N_2$  having  $m_1$  and  $m_2$  states.
- 2. Nondeterministically guess the symbols of a string s of length  $2^{m_1+m_2}$  and simulate  $N_1$  and  $N_2$  on s, storing only the current sets of states of  $N_1$  and  $N_2$ .
- 3. If they ever disagree on acceptance then accept.
- 4. If always agree on acceptance then reject."

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 23

### Last time:

- $EQ_{\text{REX}\uparrow}$  is EXPSPACE-complete
- Thus  $EQ_{\text{REX}↑}$   $\notin$  PSPACE
- Oracles and P versus NP

Today: (Sipser §10.2)

- Probabilistic computation
- The class BPP
- Branching programs

### **Probabilistic TMs**

**Defn:** A probabilistic Turing machine (PTM) is a variant of a NTM where each computation step has 1 or 2 possible choices.

Pr[ branch b ] =  $2^{-k}$  where b has k coin flips

$$Pr[M \text{ accepts } w] = \sum_{b \text{ accepts}} Pr[branch b]$$

Pr[M rejects w] = 1 - Pr[M accepts w]

**Defn:** For  $\epsilon \geq 0$  say PTM M decides language A with error probability  $\epsilon$  if for every w,  $\Pr[M \text{ gives the wrong answer about } w \in A] \leq \epsilon$  i.e.,  $w \in A \to \Pr[M \text{ rejects } w] \leq \epsilon$   $w \notin A \to \Pr[M \text{ accepts } w] \leq \epsilon$ .

### The Class BPP

**Defn:** BPP =  $\{A \mid \text{ some poly-time PTM decides } A \text{ with error } \epsilon = \frac{1}{3} \}$ 

**Amplification lemma:** If  $M_1$  is a poly-time PTM with error  $\epsilon_1 < ^1/_2$  then, for any  $0 < \epsilon_2 < ^1/_2$ , there is an equivalent poly-time PTM  $M_2$  with error  $\epsilon_2$ . Can strengthen to make  $\epsilon_2 < 2^{-\mathrm{poly}(n)}$ .

**Proof idea:**  $M_2 =$  "On input w

1. Run  $M_1$  on w for k times and output the majority response."

**Details:** Calculation to obtain k and the improved error probability.

Significance: Can make the error probability so small it is negligible.

## NP and BPP

### Check-in 23.1

Which of these are known to be true? Check all that apply.

- (a) BPP is closed under union.
- (b) BPP is closed under complement.
- (c)  $P \subseteq BPP$
- (d)  $BPP \subseteq PSPACE$

Check-in 23.1

## **Example: Branching Programs**

Defn: A branching program (BP) is a directed, acyclic (no cycles) graph that has

- 1. Query nodes labeled  $x_i$  and having two outgoing edges labeled 0 and 1.
- 2. Two output nodes labeled 0 and 1 and having no outgoing edges.
- 3. A designated start node.

BP B with query nodes  $x_1, \ldots, x_m$  describes a Boolean function  $f: \{0,1\}^m \to \{0,1\}$ : Follow the path designated by the query nodes' outgoing edges from the start note until reach an output node.

**Example:** For  $x_1 = 1$ ,  $x_2 = 0$ ,  $x_3 = 1$ 

BPs are equivalent if they describe the same Boolean function.

**Defn:**  $EQ_{BP} = \{\langle B_1, B_2 \rangle | B_1 \text{ and } B_2 \text{ are equivalent BPs (written } B_1 \equiv B_2) \}$ 

**Theorem:**  $EQ_{\rm BP}$  is coNP-complete (on pset 6)

 $EQ_{\rm RP} \in \mathsf{BPP}$ ?

Instead, consider a restricted problem.

## Read-once Branching Programs

**Defn:** A BP is <u>read-once</u> if it never queries a variable more than once on any path from the start node to an output.

**Defn:**  $EQ_{ROBP} = \{\langle B_1, B_2 \rangle | B_1 \text{ and } B_2 \text{ are equivalent read-once BPs} \}$ 

Theorem:  $EQ_{ROBP} \in BPP$ 

#### Check-in 23.2

Assuming (as we will show) that  $EQ_{ROBP} \in BPP$ , can we use that to show  $EQ_{BP} \in BPP$  by converting branching programs to read-once branching programs?

- (a) Yes, there is no need to re-read inputs.
- (b) No, we cannot do that conversion in general.
- (c) No, the conversion is possible but not in polynomial-time.

Not read-once

# $EQ_{ROBP} \in BPP$

Theorem:  $EQ_{ROBP} \in BPP$ 

Proof attempt: Let  $M = "On input \langle B_1, \overline{B_2} \rangle$ 

- 1. Pick k random input assignments and evaluate  $B_1$  and  $B_2$  on each one.
- 2. If  $B_1$  and  $B_2$  ever disagree on those assignments then *reject*. If they always agree on those assignments then *accept*."

What *k* to chose?

```
If B_1 \equiv B_2 then they always agree so \Pr[M \text{ accepts } \langle B_1, B_2 \rangle] = 1
If B_1 \not\equiv B_2 then want \Pr[M \text{ accepts } \langle B_1, B_2 \rangle] \leq {}^1/_3
so want \Pr[M \text{ rejects } \langle B_1, B_2 \rangle] \geq {}^2/_3.
```

But  $B_1$  and  $B_2$  may disagree rarely, say in 1 of the  $2^m$  possible assignments. That would require exponentially many samples to have a good chance of finding a disagreeing assignment and thus would require  $k > (^2/_3)2^m$ . But then this algorithm would use exponential time.

Try a different idea: Run  $B_1$  and  $B_2$  on non-Boolean inputs.

# **Boolean Labeling**

### Alternative way to view BP computation

Show by example: Input is  $x_1 = 0$ ,  $x_2 = 1$ ,  $x_3 = 1$ 

The BP follows its execution path.

Label all nodes and edges on the execution path with 1 and off the execution path with 0.

Output the label of the output node 1.

Obtain the labeling inductively by using these rules:

Label nodes from incoming edges

### **Arithmetization Method**

Method: Simulate  $\land$  and  $\lor$  with + and  $\times$ .

$$a \wedge b \rightarrow a \times b = ab$$
  
 $\overline{a} \rightarrow (1-a)$   
 $a \vee b \rightarrow a+b-ab$ 

Replace Boolean labeling with arithmetical labeling Inductive rules:

Start node labeled 1

Works because the BP is acyclic. The execution path can enter a node at most one time.

## Non-Boolean Inputs

Use the arithmetized interpretation of the BP's computation to define its operation on non-Boolean inputs.

Example:  $x_1 = 2$ ,  $x_2 = 3$ 

Recall label -1 = 1(1-2) -1 = 1(1-2) 1(2) = 2 2 = -1(1-3) 2(1-3) = -4 -3 = -1(3) 8 = 2 + 6 1 = -7 1(2) = 2 2(3) = 6 1 = -7

Recall labeling rules:

### Check-in 23.3

What is the output for this branching program using the arithmetized interpretation if  $x_1 = 1$ ,  $x_2 = y$ ?

- (a) (1 y)
- (b) (y+1)
- (c) y

# Quick review of today

- 1. Defined probabilistic Turing machines
- 2. Defined the class BPP
- 3. Sketched the amplification lemma
- 4. Introduced branching programs and read-once branching programs
- 5. Started the proof that  $EQ_{ROBP} \in BPP$
- 6. Introduced the arithmetization method

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 24

### Last time:

- Probabilistic computation
- The class BPP
- Branching programs
- Arithmetization
- Started showing !"  $_{ROBP} \in BPP$

Today: (Sipser §10.2)

- Finish !"  $_{ROBP} \in BPP$ 

### Review: Probabilistic TMs and BPP

**Defn:** A probabilistic Turing machine (PTM) is a variant of a NTM where each computation step has 1 or 2 possible choices.

**Defn:** For  $! \ge 0$  say PTM \$ decides language %with error probability ! if for every &, Pr[\$ gives the wrong answer about &  $\in$  %]  $\le$  !.

**Defn:** BPP = {%| some poly-time PTM decides %with error ! =  $\frac{+}{\Pi}$  }

**Amplification lemma:**  $2^{-./01(2)}$ 

#### Check-in 24.1

coin flip step each choice has 50% probability

Actually using a probabilistic algorithm presupposes a source of randomness. Can we use a standard pseudo-random number generator (PRG) as the source?

- (a) Yes, but the result isn't guaranteed.
- (b) Yes, but it will run in exponential time.
- (c) No, a TM cannot implement a PRG.
- (d) No, because that would show P = BPP.

### Review: Branching Programs

Defn: A <u>branching program</u> (BP) is a directed, acyclic (no cycles) graph that has

- 1. Query nodes labeled  $x_i$  and having two outgoing edges labeled 0 and 1.
- 2. Two output nodes labeled 0 and 1 and having no outgoing edges.
- 3. A designated start node.

**Theorem:**  $EQ_{BP}$  is coNP-complete (on pset 6)

**Defn:** A BP is <u>read-once</u> if it never queries a variable more than once on any path from the start node to an output.

**Defn:**  $EQ_{ROBP} = \{\langle B_1, B_2 \rangle | B_1 \text{ and } B_2 \text{ are equivalent read-once BPs} \}$ 

**Theorem:**  $EQ_{RORP} \in BPP$ 

Proof idea: Run  $B_1$  and  $B_2$  on a randomly selected non-Boolean input

and accept if get same output.

Method: Use arithmetization (simulating  $\Lambda$  and V with + and  $\times$ )

to define BP operation on non-Boolean inputs.

## **Boolean Labeling**

#### Alternative way to view BP computation

1 = output

Show by example: Input is  $x_1 = 0$ ,  $x_2 = 1$ ,  $x_3 = 1$ 

The BP follows its execution path.

Label all nodes and edges on the execution path with 1 and off the execution path with 0.

Output the label of the output node 1.

Obtain the labeling inductively by using these rules:

Label outgoing edges from nodes

Label nodes from incoming edges

### **Arithmetization Method**

**Method:** Simulate  $\wedge$  and  $\vee$  with + and  $\times$ .

$$' \land / \rightarrow ' \times / = ' / \\$$

Replace Boolean labeling with arithmetical labeling Inductive rules:

Start node labeled 1

Simulate V with + because the BP is acyclic. The execution path can enter a node at most one time.

## Non-Boolean Labeling

Use the arithmetized interpretation of the BP's computation to define its operation on non-Boolean inputs.

Example:  $!_{"} = 2$ ,  $!_{\#} = 3$ 

Recall labeling rules:

Algorithm sketch for 45  $_{ROBP}$ : "On input  $\langle : _{"}, : _{\#} \rangle$ 

- 1. Pick a random *non-Boolean* input assignment.
- 2. Evaluate: " and: # on that assignment.
- 3. If: " and: # disagree then reject.

  If they agree then accept."

More details and correctness proof to come. First some algebra...

# **Roots of Polynomials**

Let  $!(") = \$_{\%}"^{\&} + \$_{(}"^{\&)}( + \$_{*}"^{\&)}* + \dots + \$_{\&}$  be a polynomial. If , is some constant and !(,) = 0 call , a <u>root</u> of ! .

**Polynomial Lemma:** If ! (")  $\neq 0$  is polynomial of degree  $\leq 0$  then ! has  $\leq 0$  roots. Proof by induction (see text).

**Corollary 1:** If  $!_{(}(")$  and  $!_{*}(")$  are both degree  $\leq 0$  and  $!_{(} \neq !_{*}$  then  $!_{(}(,) = !_{*}(,))$  for  $\leq 0$  values , . Proof: Let  $!_{(} = !_{(} - !_{*}.)$ 

Above holds for any field 4 (a <u>field</u> is a set with + and  $\times$  operations that have typical properties). We will use a finite field  $4_6$  with 7 elements where 7 is prime and +,  $\times$  operate mod 7.

**Corollary 2:** If ! (")  $\neq 0$  has degree  $\leq 0$  and we pick a random  $8 \in 4_6$ , then  $Pr[!(8) = 0] \leq \frac{8}{6}$ . Proof: There are at most 0 roots out of 7 possibilities.

**Theorem** (Schwartz-Zippel): If ! (" $_{(},...,$ " $_{=}$ )  $\neq 0$  has degree  $\leq 0$  in each " $_{>}$ and we pick random &,...,&& $\in 4_6$  then  $\Pr[!(\&,...,\&)=0] \leq {}^{=\&}/_6$  Proof by induction (see text).

## Symbolic Execution

Leave the ! \$ as variables and obtain an expression in the ! \$ for the output of the BP.

Recall labeling rules: +(1-!\$) 0 1 +!\$ +!\$ +!\$

Exponents  $\leq 1$  Assume read <u>exactly</u> once so that for each 3 due to "read-once" (!  $_{\$}$ ) or  $(1 - ! _{\$})$  appears in every row

form of output 
$$= (1 - ! \cdot ) (x_{\#})^{X} (1 - ! \cdot ) (! \cdot ) \cdots (1 - ! \cdot 0)$$
  
 $+ (! \cdot ) (! \cdot ) (1 - ! \cdot ) \cdots (! \cdot 0)$   
 $+ (! \cdot ) (1 - ! \cdot ) (! \cdot ) \cdots (! \cdot 0)$   
 $\vdots$   
 $+ (! \cdot ) (! \cdot ) (! \cdot ) \cdots (! \cdot 0)$ 

Corresponds to the TRUE rows in the truth table of the Boolean function

# $EQ_{ROBP} \in BPP$

Algorithm for  $EQ_{ROBP} =$  "On input  $\langle B_1, B_2 \rangle$  [on variables  $x_1, ..., x_m$ ]

- 1. Find a prime  $q \geq 3m$ .
- 2. Pick a random *non-Boolean* input assignment  $r = r_1, ..., r_m$  where each  $r_i \in \mathbb{F}_q$ .
- 3. Evaluate  $B_1$  and  $B_2$  on r by using arithmetization.
- 4. If  $B_1$  and  $B_2$  agree on r then accept. If they disagree then reject."

Claim: (1) 
$$B_1 \equiv B_2 \to \Pr[\ p_1(r) = p_2(r)\ ] = 1$$
  
(2)  $B_1 \not\equiv B_2 \to \Pr[\ p_1(r) = p_2(r)\ ] \le {}^1/_3$ 

**Proof (1):** If  $B_1 \equiv B_2$  then they agree on all Boolean inputs. Thus their functions have the same truth table.

Thus their associated polynomials  $p_1$  and  $p_2$  are identical. Thus  $p_1$  and  $p_2$  always agree (even on non-Boolean inputs).

**Proof (2):** If  $B_1 \not\equiv B_2$  then  $p_1 \neq p_2$  so  $p = p_1 - p_2 \neq 0$ . From Schwartz-Zippel,  $\Pr[\ p_1(r) = p_2(r)\ ] \leq \frac{dm}{q} \leq \frac{m}{3m} = \frac{1}{3}$ .

(Note that d = 1.)

#### Check-in 24.2

If the BPs were not read-once, the polynomials might have exponents  $\geq 1$ . Where would the proof fail?

- (a)  $B_1 \equiv B_2$  implies they agree on all Boolean inputs
- (b) Agreeing on all Boolean inputs implies  $p_1=p_2$
- (c) Having  $p_1 = p_2$  implies  $p_1$  and  $p_2$  always agree

```
p_1 and p_2 each have the form:  (1-x_1) \ (x_2) \ (1-x_3) \ (x_4) \ \cdots \ (1-x_m)  + \ (x_1) \ (x_2) \ (x_3) \ (1-x_4) \cdots \ (x_m)  + \ (x_1) \ (1-x_2)(1-x_3) \ (x_4) \ \cdots \ (x_m)  \vdots  + \ (x_1) \ (x_2) \ (1-x_3) \ (x_4) \ \cdots \ (x_m)
```

# $EQ_{ROBP} \in BPP$

Algorithm for  $EQ_{ROBP} =$  "On input  $\langle B_1, B_2 \rangle$  [on variables  $x_1, ..., x_m$ ]

- 1. Find a prime  $q \geq 3m$ .
- 2. Pick a random *non-Boolean* input assignment  $r = r_1, ..., r_m$  where each  $r_i \in \mathbb{F}_q$ .
- 3. Evaluate  $B_1$  and  $B_2$  on r by using arithmetization.
- 4. If  $B_1$  and  $B_2$  agree on r then accept. If they disagree then reject."

Claim: (1) 
$$B_1 \equiv B_2 \to \Pr[\ p_1(r) = p_2(r)\ ] = 1$$
  
(2)  $B_1 \not\equiv B_2 \to \Pr[\ p_1(r) = p_2(r)\ ] \le {}^1/_3$ 

**Proof (1):** If  $B_1 \equiv B_2$  then they agree on all Boolean inputs. Thus their functions have the same truth table.

Thus their associated polynomials  $p_1$  and  $p_2$  are identical.

Thus  $p_1$  and  $p_2$  always agree (even on non-Boolean inputs).

**Proof (2):** If  $B_1 \not\equiv B_2$  then  $p_1 \neq p_2$  so  $p = p_1 - p_2 \neq 0$ . From Schwartz-Zippel,  $\Pr[\ p_1(r) = p_2(r)\ ] \leq {dm/q} \leq {m/3m} = {1/3}$ . (Note that d=1.)

#### Check-in 24.3

If  $p_1$  and  $p_2$  were exponentially large expressions, would that be a problem for the time complexity?

- (a) Yes, but luckily they are polynomial in size.
- (b) No, because we can evaluate them without writing them down.

```
p_1 and p_2 each have the form:  (1-x_1) \ (x_2) \ (1-x_3) \ (x_4) \ \cdots \ (1-x_m)  + \ (x_1) \ (x_2) \ (x_3) \ (1-x_4) \cdots \ (x_m)  + \ (x_1) \ (1-x_2)(1-x_3) \ (x_4) \ \cdots \ (x_m)  \vdots
```

 $+ (x_1) (x_2) (1-x_3) (x_4) \cdots (x_m)$ 

# Quick review of today

- 1. Simulated Read-once Branching Programs by polynomials
- 2. Gave probabilistic polynomial equality testing method
- 3. Showed!"  $_{ROBP} \in BPP$

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

## 18.404/6.840 Lecture 25

#### Last time:

- Schwartz-Zippel Theorem
- $EQ_{\text{ROBP}}$  ∈ BPP

Today: (Sipser §10.4)

- Interactive Proof Systems
- The class IP
- Graph isomorphism problem
- coNP  $\subseteq$  IP (part 1)

### Interactive Proofs – Introduction

**Illustration:** Graph isomorphism testing

**Defn:** Undirected graphs G and H are isomorphic if they are identical except

for a permutation (rearrangement) of the nodes.

### Interactive Proofs – Introduction

**Illustration:** Graph isomorphism testing

**Defn:** Undirected graphs G and H are isomorphic if they are identical except for a permutation (rearrangement) of the nodes.

**Defn:**  $ISO = \{\langle G, H \rangle | G \text{ and } H \text{ are isomorphic graphs} \}$   $ISO \in \mathbb{NP}$   $ISO \in \mathbb{P}$  ?  $ISO \in \mathbb{NP}$ ?

 $ISO \in NP$  therefore a Prover can convince a poly-time Verifier that G and H are isomorphic (if true).

Even though  $\overline{ISO} \in NP$  is unknown,

a Prover can still convince a poly-time Verifier that G and H are <u>not</u> isomorphic (if true).

Requires interaction and a probabilistic Verifier.

### Interactive Proofs – informal model

# Probabilistic polynomial time TM

© Sesame Workshop. All rights reserved. This content is excluded from our Creative Commons license. For more information, see <a href="https://ocw.mit.edu/fairuse">https://ocw.mit.edu/fairuse</a>.

Professor = Verifier (V)

Unlimited computation

Graduate Students = Prover (P)

© Source unknown. All rights reserved. This content is excluded from our Creative Commons license. For more information, see https://ocw.mit.edu/fairuse.

Professor wants to know if graphs G and H are isomorphic.

- He asks his Students to figure out the answer.
- But he doesn't trust their answer. He must be convinced.

If the Students claim that G and H are isomorphic, they can give the isomorphism and convince him.

But what if they claim that G and H are <u>not</u> isomorphic?

- The Professor randomly and secretly picks G or H and permutes it, then sends the result to the Students.
- If Students can identify which graph the Professor picked reliably (repeat this 100 times), then he's convinced.

### Interactive Proofs – formal model

#### Two interacting parties

**Verifier (V):** Probabilistic polynomial time TM

**Prover (P):** Unlimited computational power

Both P and V see input w.

They exchange a polynomial number of polynomial-size messages.

Then V accepts or rejects.

**Defn:**  $Pr[(V \leftrightarrow P) \text{ accepts } w] = probability that V accepts when V interacts with P, given input w.$ 

```
Defn: IP = \{A \mid \text{ for some V and P } (\text{This P is an "honest" prover})

w \in A \rightarrow \text{Pr } [(V \leftrightarrow P) \text{ accepts } w] \geq \frac{2}{3}

w \notin A \rightarrow \text{ for any prover } \tilde{P} \text{ Pr } [(V \leftrightarrow \tilde{P}) \text{ accepts } w] \leq \frac{1}{3}
```

Think of  $\tilde{P}$  as a "crooked" prover trying to make V accept when it shouldn't. An amplification lemma can improve the error probability from  $^1/_3$  to  $^1/_{2^{\text{poly}(n)}}$ 

## $\overline{ISO} \in IP$

Theorem:  $\overline{ISO} \in IP$ 

Proof: Protocol for V and (the honest) P on input  $\langle G, H \rangle$ 

- 1) Repeat twice:
- 2)  $\forall$ P Randomly choose G or H and permute to get K, then send K
- 3)  $\rightarrow$  V Compare K with G and H. Send "G" or "H" (V's choice in step 2)
- 4) Vaccepts if P was correct both times. Otherwise V rejects.

#### Check-in 25.1

Suppose we change the model to allow the Prover access to the Verifier's random choices. Now consider the same protocol as described above. What language does it describe?

- (a)  $\{\langle G, H \rangle | G \neq H\}$
- (b)  $\{\langle G, H \rangle | G \text{ and } H \text{ are not isomorphic } \}$
- (c)  $\{\langle G, H \rangle | G \text{ and } H \text{ are any two graphs } \}$
- (d) Ø

Check-in 25.1

### Facts about IP – Checkin 25.2

Which of the following is true? Check all that apply

- a) NP⊆IP
- b)  $BPP \subseteq IP$
- c) IP  $\subseteq$  PSPACE

**Surprising Theorem:** PSPACE ⊆ IP so IP = PSPACE

We will prove only a weaker statement:  $coNP \subseteq IP$ 

## #SAT problem

**Defn:**  $\#SAT = \{\langle \phi, k \rangle | \text{ Boolean formula } \phi \text{ has exactly } k \text{ satisfying assignments} \}$ 

Let  $\#\phi$  = the number of satisfying assignments of Boolean formula  $\phi$ .

So  $\#SAT = \{\langle \phi, k \rangle | k = \#\phi \}$ 

**Defn:** Language B is NP-hard if  $A \leq_{P} B$  for every  $A \in NP$ .

(Note: B is NP-complete if B is NP-hard and  $B \in NP$ .)

**Theorem:** #SAT is coNP-hard

Proof: Show  $\overline{SAT} \leq_P \#SAT$ 

$$f(\langle \phi \rangle) = \langle \phi, 0 \rangle$$

To show coNP  $\subseteq$  IP we will show  $\#SAT \in$  IP

### $\#SAT \in IP$ - notation

 $\#SAT = \{\langle \phi, k \rangle | \text{ Boolean formula } \phi \text{ has exactly } k \text{ satisfying assignments} \}$ 

Theorem:  $\#SAT \in IP$ 

**Proof:** First some notation. Assume  $\phi$  has m variables  $x_1, \dots, x_m$ .

Let  $\phi(0)$  be  $\phi$  with  $x_1 = 0$  (0 substituted for  $x_1$ ) 0 = FALSE and 1 = TRUE.

Let  $\phi(01)$  be  $\phi$  with  $x_1 = 0$  and  $x_2 = 1$ .

Let  $\phi(a_1 ... a_i)$  be  $\phi$  with  $x_1 = a_1$ , ...,  $x_i = a_i$  for  $a_1, ..., a_i \in \{0,1\}$ .

Call  $a_1, \dots, a_i$  presets. The remaining  $x_{i+1}, \dots, x_m$  stay as unset variables.

Let  $\#\phi$  = the number of satisfying assignments of  $\phi$ .

Let  $\#\phi(0)$  = the number of satisfying assignments of  $\phi(0)$ .

Let  $\#\phi(a_1 \dots a_i)$  = the number of satisfying assignments of  $\phi(a_1 \dots a_i)$ 

Equivalently:  $\#\phi(a_1 \dots a_i) = \sum_{a_{i+1}, \dots, a_m} \phi(a_1 \dots a_m)$ 

#### Check-in 25.3

If  $\#\phi = 9$  and  $\#\phi(0) = 6$  then what do we know?

a) 
$$\#\phi(1) = 3$$

a) 
$$\#\phi(1) = 3$$
 c)  $\#\phi(00) \le 5$ 

b) 
$$\#\phi(1) = 15$$

d) none of these

1. 
$$\#\phi(a_1 \dots a_i) = \\ \#\phi(a_1 \dots a_i 0) + \#\phi(a_1 \dots a_i 1)$$

2. 
$$\#\phi(a_1 ... a_m) = \phi(a_1 ... a_m)$$

## $\#SAT \in IP - 1^{st}$ attempt

```
Theorem: \#SAT \in IP
Proof: Protocol for V and (the honest) P on input \langle \phi, k \rangle
   P sends \#\phi; V checks k = \#\phi
    P sends \#\phi(0), \#\phi(1); V checks \#\phi = \#\phi(0) + \#\phi(1)
    P sends \#\phi(00), \#\phi(01), \#\phi(10), \#\phi(11); V checks \#\phi(0) = \#\phi(00) + \#\phi(01)
                                                                 \#\phi(1) = \#\phi(10) + \#\phi(11)
 \begin{array}{cccccccccccccccccccccccccccccccccccc
(m+1) \text{ V checks } \#\phi(1\cdots 1) = \#\phi(1\cdots 10) + \#\phi(1\cdots 11)
                                                                                          \#\phi(00) \#\phi(01) \#\phi(10) \#\phi(11)
                   \#\phi(1\cdots 1) = \phi(1\cdots 1)
        V accepts if all checks are correct. Otherwise V rejects.
                                                                                            \#\phi(0\cdots 0)
                                                                                                                \#\phi(1\cdots 1)
Problem: Exponential. How to fix?
                                                                                            \phi(0\cdots 0)
                                                                                                                \phi(1\cdots 1)
```

## Idea for fixing $\#SAT \in IP$ protocol

## Quick review of today

- 1. Introduced the interactive proof system model
- 2. Defined the class IP
- 3. Showed  $\overline{ISO} \in IP$
- 4. Started showing  $\#SAT \in IP$  to prove that  $coNP \subseteq IP$

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.

---

# 18.404/6.840 Lecture 26

### Last time:

- Interactive Proof Systems
- The class IP
- Graph isomorphism problem,  $\overline{ISO} \in IP$
- $-\#SAT \in IP \text{ (part 1)}$

## Today: (Sipser §10.4)

- Arithmetization of Boolean formulas
- Finish  $\#SAT \in IP$  and conclude that  $coNP \subseteq IP$

# **Review: Interactive Proofs**

#### Two interacting parties

**Verifier (V):** Probabilistic polynomial time TM **Prover (P):** Unlimited computational power

Both P and V see input w.

They exchange a polynomial number of polynomial-size messages.

Then V accepts or rejects.

**Defn:**  $Pr[(V \leftrightarrow P) \text{ accepts } w] = probability that V accepts when V interacts with P, given input w.$ 

```
Defn: IP = \{A \mid \text{ for some V and P } (\text{This P is an "honest" prover}) w \in A \rightarrow \text{Pr } [(V \leftrightarrow P) \text{ accepts } w] \geq \frac{2}{3} w \notin A \rightarrow \text{ for any prover } \tilde{P} \text{ Pr } [(V \leftrightarrow \tilde{P}) \text{ accepts } w] \leq \frac{1}{3} \} Think of \tilde{P} as a "crooked" prover trying to make V accept when it shouldn't.
```

Equivalently:  $IP = \{A \mid \text{ for some V }$ 

$$w \in A \rightarrow \exists P \ Pr[(V \leftrightarrow P) \ accepts \ w] \geq \frac{2}{3}$$
 Here, we emphasize how P is similar  $w \notin A \rightarrow \exists P \ Pr[(V \leftrightarrow P) \ accepts \ w] \geq \frac{1}{3}$  to the certificate for NP-languages.

An amplification lemma can improve the error probability from  $^{1}/_{3}$  to  $^{1}/_{2^{\text{poly}(n)}}$ 

## $coNP \subseteq IP$

**Surprising Theorem:** IP = PSPACE

IP  $\subseteq$  PSPACE: standard simulation, similar to NP  $\subseteq$  PSPACE

PSPACE  $\subseteq$  IP: show  $TQBF \in$  IP, we won't prove

 $coNP \subseteq IP$ : weaker but similar, show  $\#SAT \in IP$  (#SAT is coNP-hard)

 $\#SAT = \{\langle \phi, k \rangle | \text{ Boolean formula } \phi \text{ has exactly } k \text{ satisfying assignments} \}$ 

Theorem:  $\#SAT \in IP$ 

**Proof:** First some notation. Assume  $\phi$  has m variables  $x_1, \dots, x_m$ .

Let  $\phi(0)$  be  $\phi$  with  $x_1 = 0$  (0 substituted for  $x_1$ ) 0 = FALSE and 1 = TRUE. Let  $\phi(a_1 ... a_i)$  be  $\phi$  with  $x_1 = a_1$ , ...,  $x_i = a_i$  for  $a_1$ , ...,  $a_i \in \{0,1\}$ .

Call  $a_1, \ldots, a_i$  presets. The remaining  $x_{i+1}, \ldots, x_m$  stay as unset variables.

Let  $\#\phi$  = the number of satisfying assignments of  $\phi$ .

Let  $\#\phi(0)$  = the number of satisfying assignments of  $\phi(0)$ .

Let  $\#\phi(a_1 \dots a_i)$  = the number of satisfying assignments of  $\phi(a_1 \dots a_i)$ 

#### Check-in 26.1

Let  $\phi = (x_1 \lor x_2) \land (x_1 \lor \overline{x_2})$ 

Check all that are true:

- a)  $\#\phi = 1$  b)  $\#\phi = 2$
- c)  $\#\phi \ 0 = 1$  d)  $\#\phi(0) = 2$
- e)  $\#\phi(00) = 0$  f)  $\#\phi(00) = 1$

# $#SAT \in IP -1^{st}$ attempt

```
Theorem: \#SAT \in IP
Proof: Protocol for V and (the honest) P on input \langle \phi, k \rangle
   P sends \#\phi; V checks k = \#\phi
    P sends \#\phi(0), \#\phi(1); V checks \#\phi = \#\phi(0) + \#\phi(1)
    P sends \#\phi(00), \#\phi(01), \#\phi(10), \#\phi(11); V checks \#\phi(0) = \#\phi(00) + \#\phi(01)
                                                               \#\phi(1) = \#\phi(10) + \#\phi(11)
V checks \#\phi(1\cdots 1)=\#\phi(1\cdots 10)+\#\phi(1\cdots 11) m+1) V checks \#\phi(0\cdots 0)=\phi(0\cdots 0)
                   \#\phi(1\cdots 1) = \phi(1\cdots 1)
                                                                                        \#\phi(00) \#\phi(01) \#\phi(10) \#\phi(11)
        V accepts if all checks are correct. Otherwise V rejects.
                                                                                         \#\phi(0\cdots 0)
                                                                                                             \#\phi(1\cdots 1)
Problem: Exponential. Will fix.
                                                                                                             \phi(1\cdots 1)
                                                                                          \phi(0\cdots 0)
```

# Idea for fixing $\#SAT \in IP$ protocol

# **Arithmetizing Boolean formulas**

Simulate  $\wedge$  and  $\vee$  with + and  $\times$ 

$$\begin{array}{ccc} a \wedge b & \rightarrow & a \times b = ab \\ \overline{a} & \rightarrow & (1-a) \\ a \vee b & \rightarrow & a+b-ab \\ \phi & \rightarrow & p_{\phi} & \mathrm{degree}(p_{\phi}) \leq |\phi| \end{array}$$

Let  $\mathbb{F}_q = \{0,1,\ldots,q-1\}$  for prime  $q>2^m$  be a finite field  $(+,\times \operatorname{mod} q)$  and let  $a_1,\ldots,a_i\in\mathbb{F}_q$ Let  $\phi(a_1\ldots a_i)=p_{\phi}$  where  $x_1\cdots x_i=a_1\cdots a_i$  and remaining  $x_{i+1},\ldots,x_m$  stay as unset variables.

Let 
$$\#\phi(a_1 \dots a_i) = \sum_{a_{i+1}, \dots, a_m \in \{0,1\}} \phi(a_1 \dots a_m)$$

#### identities still true

1. 
$$\#\phi(a_1 \dots a_i) = \#\phi(a_1 \dots a_i 0) + \#\phi(a_1 \dots a_i 1)$$

2. 
$$\#\phi(a_1 ... a_m) = \phi(a_1 ... a_m)$$

## Check-in 26.2

Let  $\phi = (x_1 \lor x_2) \land (x_1 \lor \overline{x_2})$ . Check all that are true:

a) 
$$p_{\phi} = (x_1 + x_2 - x_1 x_2) ((1 - x_1) + (1 - x_2) - (1 - x_1)(1 - x_2))$$

b) 
$$p_{\phi} = (x_1 + x_2)((1 - x_1) + (1 - x_2))$$

c) 
$$p_{\phi} = (x_1 + x_2 - 2x_1x_2)$$

## $\#SAT \in IP - version 1$

```
Theorem: \#SAT \in \mathbb{P}

Proof: Protocol for V and (the honest) P on input \langle \phi, k \rangle

0) P sends \#\phi; V checks k = \#\phi

1) P sends \#\phi (b) all \phi (b) yn Vichielcks \#\phi sends \#\phi (0) \#\phi (1) [by evaluating polynomial for \#\phi (2) ]

[P needs it on show \#\phi (2) is correct ]

2) P sends \#\phi (r_1z) as a polynomial in z

V checks \#\phi (r_1) = \#\phi (r_10) + \#\phi (r_11) [by evaluating polynomial for \#\phi (r_1z) ]

V sends random r_2 \in \mathbb{F}_q

:

Recall \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z

V checks \#\phi (r_1 \dots r_{m-1}z) as a polynomial in z
```

# $\#SAT \in IP - version 2$

Input  $\langle \phi, k \rangle$ Prover sends

 $\#\phi$ 

$$#\phi(z) = 3z^d - 5z^{d-1} + \dots + 7$$

$$\#\phi(r_1z)=\cdots$$

$$\#\phi(r_1r_2z)=\cdots$$

$$\#\phi(r_1\cdots r_{m-1}z)=\cdots$$

**Verifier checks** 

If k is correct, V will accept.

If *k* is wrong, V probably will reject, whatever P does.

#### Check-in 26.3

# P = NP?

- a) YES. Deep learning will do  $SAT \in P$ , but we won't understand how.
- b) NO. But we will never prove it.
- c) NO. We will prove it but only after 100 years
- d) NO. We will prove it in n years,  $20 \le n \le 100$
- e) NO. We will prove it in n years,  $1 \le n < 20$
- f) NO. One of us is writing up the proof now...

# Quick review of today

Finished  $\#SAT \in IP$  and  $coNP \subseteq IP$ 

#### **Additional subjects:**

18.405/6.841 Advanced complexity F2021

18.425/6.875 Cryptography F2021

6.842 Randomness and Computation?

Good luck on the final!

Best wishes for the holidays and the New Year!

MIT OpenCourseWare <a href="https://ocw.mit.edu">https://ocw.mit.edu</a>

18.404J / 18.4041J / 6.840J Theory of Computation Fall 2020

For information about citing these materials or our Terms of Use, visit: <a href="https://ocw.mit.edu/terms">https://ocw.mit.edu/terms</a>.
