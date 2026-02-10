## Theorem 1
Given a finite-dimensional complex representation of a finite group, each invariant subspace has a corresponding invariant complementary subspace.

## Theorem (Maschke's Theorem)
Every finite-dimensional complex representation of a finite group can be written as a direct sum of irreducible representations.

## Proposition 1
The permutation representation restricted to $V = \{(x, y, z) \mid x + y + z = 0\}$ is irreducible.

## Proposition 2
For every $n$, the permutation representation of $S_n$ on $\CC^n$ has an $(n - 1)$-dimensional invariant subspace \[V = \left\{(x_1, \ldots, x_n) \mid \sum x_i = 0\right\} \subset \CC^n,\] consisting of vectors whose coordinates sum to zero. Furthermore, the representation of $S_n$ obtained by restricting the permutation representation to $V$ is irreducible.

## Lemma (hermitian exists)
If $\rho : G \to \operatorname{GL}(V)$ is a complex representation of a finite group, then there exists a $G$-invariant positive Hermitian form on $V$.

## Lemma (hermitian to invariant complement)
If $\rho : G \to \operatorname{GL}(V)$ has an invariant Hermitian form, then every invariant subspace of $V$ has an invariant complement.

## Theorem (Maschke's Theorem)
Every complex, finite-dimensional representation of a finite group is a direct sum of irreducible representations.

## Theorem (Maschke's Theorem)
Every complex representation of a finite group is isomorphic to a direct sum of irreducible representations.

## Proposition 3
If $\rho: G \to \operatorname{GL}(V)$ is a complex representation, then
\begin{enumerate}[label = (\alph*)]
    \item $\chi_\rho(g)$ is a sum of roots of unity;
    \item $\chi_\rho(g^{-1}) = \overline{\chi_\rho(g)}$;
    \item $\overline{\chi_\rho}$ is the character of another representation of the same dimension, denoted $\rho^*$ and called the \emph{dual representation}. % = \chi_{\rho^{*}}(g)$, which is the character of the dual representation of the same dimension.\todo{explain}
\end{enumerate}

## Theorem (Main Theorem)
Let $G$ be a finite group. Then:
\begin{enumerate}[label = (\alph*)]
    \item The characters of irreducible representations form a basis in the space of class functions on $G$.
    
    \item This basis is \emph{orthonormal} with respect to the Hermitian form on the space of class functions given by \[\langle f_1, f_2 \rangle = \frac{1}{|G|} \sum_{g \in G} f_1(g)\overline{f_2(g)}.\] 
    
    \item If $d_1$, \ldots, $d_m$ are the dimensions of the irreducible representations of $G$, then \[d_1^2 + d_2^2 + \cdots + d_n^2 = |G|,\] and each $d_i$ divides $|G|$.
\end{enumerate}

## Corollary 1
The character of a representation uniquely determines the representation, up to isomorphism.

## Corollary 2
The number of irreducible representations of $G$ is the number of conjugacy classes on $G$.

## Theorem 2
Let $G$ be a finite group, and let $\rho_1$, \ldots, $\rho_n$ be a full list of irreducible representations up to isomorphism. 
\begin{enumerate}[label = (\alph*)]
    \item The characters $\chi_{\rho_0}$, \ldots, $\chi_{\rho_n}$ form a basis for the space of class functions on $G$.

    \item The basis formed by $\chi_{\rho_0}$, \ldots, $\chi_{\rho_n}$ is orthonormal.
    
    \item If $d_i = \dim \rho_i$ for each $i$, then $\sum d_i^2 = |G|$, and each $d_i$ divides $|G|$.
\end{enumerate}

## Proposition 4
Any two one-dimensional characters are orthogonal.

## Proposition 5
If $G$ is abelian, then every irreducible representation is one-dimensional.

## Claim* 1
If we have a collection of pairwise commuting matrices, each of which is diagonalizable, then we can diagonalize \emph{all} of them simultaneously.

## Theorem (Schur's Lemma)
Let $\rho : G \to \operatorname{GL}(V)$ and $\psi : G \to \operatorname{GL}(W)$ be \emph{irreducible} representations. Then $\operatorname{Hom}_G(\rho, \psi)$ is $0$ if $\rho \not\cong \psi$, and is one-dimensional if $\rho \cong \psi$.

## Theorem (Schur's Lemma)
Suppose $\rho: G \to \operatorname{GL}(V)$ and $\psi: G \to \operatorname{GL}(W)$ are irreducible (and complex and finite-dimensional). Then \[\dim\left(\operatorname{Hom}_G(\rho, \psi)\right) = \begin{cases} 0 & \text{if } \rho \not\cong \psi \\ 1 & \text{if } \rho \cong \psi.\end{cases}\]

## Corollary 3
Let $\rho: G \to \operatorname{GL}(V)$ be a representation. Let $\rho_1$, \ldots, $\rho_n$ be the list of all irreducible representations of $G$ (up to isomorphism). Then \[\rho \cong \bigoplus_{i = 1}^n \rho_i^{d_i}\] where $d_k = \dim \operatorname{Hom}_G(\rho_k, \rho)$ for all $k$.

## Lemma 1
There is a representation $C$ of $G$ acting on $\operatorname{Mat}_{m \times n}(\CC)$, where for each $g \in G$, $g$ is sent to the matrix \[C_g : A \mapsto S_gAR_g^{-1}.\]

## Proposition (charproduct)
For the representation $\gamma$ described above, we have \[\chi_{\gamma} = \chi_\psi \overline{\chi_\rho}.\]

## Lemma 2
Let $A$ and $B$ be $n \times n$ and $m \times m$ matrices. Consider the linear map $A \otimes B$ from $\operatorname{Mat}_{m\times n}(\mathbb{C})$ to itself defined as \[A \otimes B : E \mapsto BEA.\] Then we have \[\trace(A\otimes B) = \trace(A) \cdot \trace(B).\]

## Proposition 6
The characters of the irreducible representations of $G$ are orthonormal.

## Corollary (coeffs from orthonormality)
Any representation $\rho : G \to \operatorname{GL}(V)$ can be split as a sum of irreducibles as \[\rho \cong \bigoplus \rho_i^{n_i},\] where for each $k$, \[n_k = \langle \chi_\rho, \chi_k \rangle.\]

## Corollary 4
If $\rho = \bigoplus \rho_i^{n_i}$ as before, then \[\langle \chi_\rho, \chi_\rho \rangle = \sum n_i^2.\] In particular, $\rho$ is irreducible if and only if $\langle \chi_\rho, \chi_\rho \rangle = 1$.

## Proposition 7
The character of the regular representation is \[\chi_\rho(g) = \begin{cases} |G| & \text{if } g = 1 \\ 0 & \text{otherwise}.\end{cases}\]

## Proposition (decomposition of regular rep)
The regular representation decomposes into irreducibles as \[\rho \cong \bigoplus \rho_i^{d_i},\] where $d_i$ denotes the dimension of $\rho_i$.

## Proposition 8
If the irreducible representations of $G$ have dimensions $d_1$, \ldots, $d_n$, then we have \[\lvert G \rvert = d_1^2 + \cdots + d_n^2.\]

## Proposition (f in basis of chars)
For any class function $f$, we have \[f = \sum \langle f, \chi_i \rangle \chi_i.\]

## Proposition (zero pairing implies zero)
If $f$ is a class function and $\langle f, \chi_k \rangle = 0$ for all $k$, then $f$ is the zero function.

## Lemma (trace equals pairing)
For any representation $\rho$ and function $f$, we have $\trace \rho(f) = \langle \chi_\rho, \overline{f} \rangle$.

## Lemma (class functions equivariant)
If $f$ is a class function, then $\rho(f) \in \operatorname{End}_G(\rho)$.

## Proposition 9
In any ring $R$, $0_R \cdot a = 0_R$ for all $a \in R$.

## Corollary 5
The additive identity $0_R$ cannot have a multiplicative inverse unless $0_R = 1_R$. (In other words, division by $0$ is only possible when $0 = 1$.)

## Proposition 10
For a ring homomorphism $\varphi: R \to S$, it must be the case that $\varphi(0_R) = 0_S$.

## Proposition (Quotient Ring)
Let $R$ be a ring and $I \subset R$ an ideal. Since $I$ is a normal subgroup of $R$ under addition (as both are abelian groups), we can construct the quotient $R/I$ of additive groups. Then $R/I$ is in fact a ring (with multiplication defined in the natural way --- the product of the cosets corresponding to $x$ and $y$ is the coset corresponding to $xy$), called the \textbf{quotient ring}.

## Proposition 11
A ring $Q$ is isomorphic to a product of rings $R \times S$ if and only if $Q$ contains an idempotent other than $0$ and $1$.

## Proposition (Mapping Property)
Suppose we have a ring $R$, and a ring homomorphism $\varphi : R \to S$. Then given $\alpha_1$, \ldots, $\alpha_n \in S$, there exists a unique extension of $\varphi$ to a homomorphism $\widetilde{\varphi} : R[x_1, \ldots, x_n] \to S$ such that $\widetilde{\varphi}(r) = \varphi(r)$ for $r \in R$, and $\widetilde{\varphi}(x_i) = \alpha_i$ for all $i$.

## Proposition (field iff two ideals)
A ring $R$ is a field if and only if it has exactly two ideals.

## Proposition (F[x] is a PID)
Every ideal in $F[x]$ is principal. More precisely, if $I \subset F[x]$ is a nonzero ideal and $P$ a (nonzero) element of $I$ of minimal degree, with $\deg(P) = n$, then we have $I = (P)$, and the images of $1$, $x$, $x^2$, \ldots, $x^{n - 1}$ form a basis in $F[x]/I$ (as a vector space over $F$).

## Proposition 12
If $F$ is a field and $P \in F[x]$, then $F[x]/(P) \cong F[\alpha]$, where $\alpha$ is a root of $P$.

## Proposition (maximal iff field)
An ideal $I \subset R$ is maximal if and only if $R/I$ is a field.

## Proposition 13
Suppose $R = F[x_1, \ldots, x_n]/(P_1, \ldots, P_m)$. Then any common zero $\alpha = (\alpha_1, \ldots, \alpha_n)$ of $P_1$, \ldots, $P_m$ yields a maximal ideal of $R$, which is the image of $\mathfrak{m}_\alpha$ when quotienting out by $(P_1, \ldots, P_m)$.

## Theorem (Hilbert's Nullstelensatz)
Every maximal ideal of $\CC[x_1, \cdots, x_n]$ is of the form $\mathfrak{m}_{\alpha}$ for some $\alpha = (\alpha_1, \cdots, \alpha_n)$.

## Corollary 6
The maximal ideals in $R = \CC[x_1, \cdots, x_n]/(P_1, \cdots, P_m)$ are in bijection with the common zeroes of the polynomials $P_i$.

## Theorem (Hilbert's Nullstelensatz)
The maximal ideals in $\CC[x_1, \cdots, x_n]$ are exactly the kernels of evaluation homomorphisms, and thus they are in bijection with $\CC^n$.

## Corollary (nullstelensatz corollary)
The maximal ideals in $\CC[x_1, \cdots, x_n]/(P_1, \cdots, P_m)$ are in bijection with the common zeroes of $P_1$, \ldots, $P_m$.

## Proposition 14
If $a$ is \emph{not} a zero divisor, then $R \subset R_{(a)}$.

## Proposition (factor)
For a field $F$, every polynomial $P \in F[x]$ factors as a product of irreducible polynomials in an essentially unique way (up to rearrangement of the factors or multiplying the factors by scalars).

## Lemma (lemma factor)
If $P$ is irreducible and $P \mid QS$, then $P \mid Q$ or $P \mid S$.

## Theorem 3
Any PID is a UFD.

## Proposition (euclidean pid)
A Euclidean domain is a PID, and therefore a UFD.

## Theorem (R UFD implies R[x])
If $R$ is a UFD, then $R[x]$ is also a UFD.

## Corollary 7
The rings $\mathbb{Z}[x]$ and $\mathbb{C}[x_1, \ldots, x_n]$ are UFDs.

## Proposition 15
In a UFD, the gcd of any two elements always exists.

## Lemma (Gauss's Lemma)
If $P, Q \in R[x]$ are primitive, then so is $PQ$.

## Theorem (ufd polynomial)
If $R$ is a unique factorization domain, then $R[x]$ is also a unique factorization domain.

## Lemma (Gauss's Lemma)
If $P$ and $Q$ are primitive, then $PQ$ is as well.

## Corollary (primitive)
If $P, Q \in \ZZ[x]$ are such that $P$ divides $Q$ in $\QQ[x]$ and $P$ is primitive, then $P$ divides $Q$ in $\ZZ[x]$.

## Corollary 8
The irreducible elements in $\ZZ[x]$ fall into two categories: $\pm p$ for prime integers $p$, and primitive polynomials which are irreducible in $\QQ[x]$.

## Corollary 9
The polynomials with integer coefficients, $\ZZ[x]$, form a unique factorization domain.

## Lemma 3
Let $p \in \ZZ$ be a prime number. Then $p = a^2 + b^2$ if and only if $p$ is \emph{not} a prime in $\ZZ[i]$.

## Lemma 4
Let $p \in \ZZ$ be a prime number. Then $p$ is \emph{not} prime in $\ZZ[i]$ if and only if $p = 2$ or $p \equiv 1 \pmod{4}$.

## Claim* 2
$p$ is not a prime in $\ZZ[i]$ if and only if there exists $\alpha \in \ZZ[i]$ such that $p \nmid \alpha$, but $p \mid \alpha\overline{\alpha}$.

## Theorem 4
The full list of primes in $\ZZ[i]$, up to association, can be constructed as follows: consider all integer primes $p$. 
\begin{itemize}
    \item If $p \equiv 3 \pmod{4}$, then $p$ itself is a Gaussian prime. 
    \item If $p \equiv 1 \pmod{4}$, then it factors as $(a - bi)(a + bi)$, and both factors $a \pm bi$ are Gaussian primes. 
    \item If $p = 2$, then it factors as $(1 + i)(1 - i)$, and since $1 + i$ and $1 - i$ are associate, they correspond to the same Gaussian prime.
\end{itemize}

## Theorem 5
The complete list of all primes in $\ZZ[i]$, up to association, consists of:
\begin{itemize}
    \item for each integer prime $p = 4k + 3 \in \ZZ$, the Gaussian prime $p$ itself;
    \item for each integer prime $p = 4k + 1 \in \ZZ$, the two Gaussian primes $a \pm bi$ where $a^2 + b^2 = p$;
    \item the prime $1 + i$. 
\end{itemize}

## Claim* 3
If $a^2 + b^2 = p$ is an integer prime, then $a + bi$ is prime in $\ZZ[i]$.

## Corollary 10
If $n$ has prime factorization $n = p_1^{d_1}\cdots p_r^{d_r}$ in $\ZZ$, then $n$ is a sum of squares if and only if the exponent $d_i$ is even for all primes $p_i \equiv 3 \pmod{4}$.

## Theorem (Fermat)
For an integer $n > 2$, the equation \[a^n + b^n = c^n\] has no solutions where $a$, $b$, and $c$ are all nonzero integers.

## Lemma 5
The element $\alpha$ is an algebraic integer if and only if $P(\alpha) = 0$ for \emph{some} monic polynomial $P \in \ZZ[x].$

## Theorem 6
For a number field $F$, the set of algebraic integers in $F$ is a subring of $F$. Furthermore, this is the largest subring that is finitely generated as an abelian group under addition. 
% The set of algebraic integers in a number field has quite a bit of additional structure.
% \begin{enumerate}[label = (\alph*)]
%     \item If $F$ is a number field, then the set of algebraic integers is a subring of $F$.
%     \item In fact, this is the largest subring that is finitely generated as an abelian group under addition.
% \end{enumerate}

## Lemma 6
An ideal $I$ is prime if and only if $R/I$ is an integral domain.

## Lemma 7
A maximal ideal is always prime.

## Theorem (unique ideal factorization)
Let $R$ be the ring of algebraic integers in a number field. Then every nonzero ideal $I \subset R$ factors uniquely (up to permutation of factors) as a product of prime ideals.

## Proposition (lattice properties)
Suppose that $L$ and $L'$ are lattices, with $L' \subset L$. 
    \begin{itemize}
        \item The quotient $L/L'$ is finite. 
        \item If $L''$ is a subgroup of $L$ (under addition) with $L' \subset L'' \subset L$, then $L''$ is also a lattice. 
    \end{itemize}

## Corollary 11
Every nonzero ideal of $R$ is again a lattice.

## Lemma 8
A nonzero ideal in $R$ is prime if and only if it is maximal.

## Proposition (key proposition)
Multiplication of ideals has the \emph{cancellation property} --- if we have ideals $I$, $I'$, and $J$ (with $J \neq 0$), then \[IJ = I'J \implies I = I'.\] 
    
    Furthermore, divisibility is the same as inclusion --- if $I \subset J$, then there exists an ideal $J'$ such that $I = JJ'$.

## Lemma (I Iconj is principal)
If $I \subset R$ is an ideal, then $I\overline{I}$ is a principal ideal generated by an integer $n \in \mathbb{Z}$.

## Lemma (IconjI principal)
If $I \subset R$ is an ideal, then $I\overline{I} = (n)$ for some $n \in \mathbb{Z}$.

## Proposition (key proposition 2)
Multiplication of ideals has the following two properties:
    \begin{enumerate}[label = (\alph*)]
        \item Cancellation: if $IJ = I'J$ and $J \neq 0$, then $I = I'$. 
        \item If $I \subset J$, then $I = JJ'$ for some $J'$. 
    \end{enumerate}

## Lemma (ideal in maximal)
Every non-unit ideal $I$ in $R$ is contained in a maximal ideal.

## Theorem (unique ideal factorization 2)
Every nonzero ideal $I \subset R$ factors uniquely (up to permutation of factors) as a product of prime ideals.

## Lemma 9
If $P$ is a prime ideal, and $I$ and $J$ are ideals with $I \not\subset P$ and $J \not\subset P$, then $IJ \not\subset P$.

## Proposition 16
If $I \sim I'$, then $IJ \sim I'J$.

## Theorem 7
The ideal class group $\operatorname{Cl}(F)$ is finite.

## Lemma 10
If $P$ is a prime (nonzero) ideal in $R$, then either $P = (q)$ for an integer prime $q$, or $P\overline{P} = (q)$ for an integer prime $q$.

## Lemma 11
An odd integer prime $q$ remains prime in $R$ if and only if the equation $\overline{a}^2 = d\overline{b}^2$ has no solutions in $\FF_q$ except $(0, 0)$, or equivalently, if $d$ is neither $0$ nor a square mod $q$.

## Theorem 8
The ideal class group $\operatorname{Cl}(F)$ is finite.

## Lemma 12
In the case of $\ZZ[\sqrt{-5}] \subset \QQ[\sqrt{-5}]$, the class group is $\ZZ/2\ZZ$. The two similarity classes of ideals are represented by $(1)$, and by $(2, 1 + \sqrt{-5})$. 
% There are exactly two similarity classes of ideals in $R,$ represented by $(1),$ principal ideals, and $(2, 1 \pm \sqrt{-d}$.

## Claim* 4
We must have $\beta = \alpha \cdot (1 + \sqrt{-5})/2$.

## Theorem 9
Every ideal in $R$ can be factored uniquely as a product of prime ideals.

## Proposition 17
We can still conclude each factor is a $p$th power if $p$ is regular.

## Theorem 10
The class group $\operatorname{Cl}(F)$ is finite.

## Proposition (boundednorm)
Every ideal class has a representative with bounded norm --- more precisely, with norm at most \[\mu = \begin{cases} \sqrt{|d|/3} & \text{if } d \equiv 1 \pmod{4} \\ 2\sqrt{|d|/3} & \text{if } d \equiv 2, 3 \pmod{4}.\end{cases}\]

## Lemma (geolemma)
An ideal $I$ of norm $n$ contains a nonzero element $\alpha \neq 0$ with $\alpha\overline{\alpha} \leq \mu n$.

## Claim* 5
We have the bound $|v|^2\cdot \sqrt{3}/2 \leq \Delta_I$.

## Claim* 6
We have $\operatorname{N}(I) = [R : I]$.

## Theorem (Smith normal form)
Every $n \times m$ matrix over a Euclidean domain $R$ can be reduced by elementary row and column operations to a matrix in \emph{Smith normal form} --- if we let $B = (b_{ij})$, then we have $b_{ij} = 0$ for all $i \neq j$, and $b_{11} \mid b_{22} \mid b_{33} \mid \cdots$.  %where $b_{ij} = 0$ if $i \neq j,$ and letting $d_i = b_{ii}$, $d_i$ divides $d_{k}$ if $i < k.$ \todo{explain the smith normal form more}

## Corollary 12
Every finitely presented module over a Euclidean domain is isomorphic to a direct sum of \emph{cyclic} modules (modules which are generated by one element) --- we can write \[M \cong R^a \oplus R/(d_1) \oplus R/(d_2) \oplus \cdots \oplus R/(d_k),\] where we additionally have $d_1 \mid d_2 \mid \cdots \mid d_k$.

## Theorem (smith normal form)
For a Euclidean domain $R$, any $n \times m$ matrix $B$ can be reduced using elementary row and column operations to a matrix $D$, where $d_{ij} = 0$ for all $i \neq j$, and $d_{11} \mid d_{22} \mid \cdots$.

## Lemma (b prime gcd)
By row and column operations, we can arrive at a matrix $B'$ such that $b_{11}' = \gcd(b_{ij}) = \gcd(b_{ij}')$.

## Corollary (abelian groups)
Every finitely presented abelian group is isomorphic to \[\ZZ/d_1\ZZ \times \ZZ/d_2\ZZ \times \cdots \times \ZZ/d_n\ZZ \times \ZZ^a,\] for some positive integers $d_i$ with $d_1 \mid d_2 \mid \cdots \mid d_n$.

## Theorem 11
Any finitely presented abelian group $A$ is isomorphic to \[\mathbb{Z}/d_1\ZZ \times \mathbb{Z}/d_2\ZZ \times \cdots \times \mathbb{Z}/d_n\ZZ \times \mathbb{Z}^a,\] where $d_1 \mid d_2 \mid \cdots \mid d_n$.

## Lemma 13
The multiplicities of the powers of $p$ in the decomposition of $A_p$ as a product of cyclic groups are uniquely determined by $A$.

## Proposition 18
A ring $R$ is Noetherian if and only if every submodule in a finitely generated $R$-module is itself finitely generated.

## Corollary 13
If $R$ is Noetherian, every finitely generated module is finitely presented.

## Theorem (Hilbert Basis Theorem)
If $R$ is Noetherian, then $R[x]$ is Noetherian.

## Proposition (noetheriansubmodules)
A ring $R$ is Noetherian if and only if every submodule in a finitely generated $R$-module is itself finitely generated.

## Corollary (finpresented)
If $R$ is Noetherian, then every finitely generated module is finitely presented.

## Lemma (noetherianhomomorphisms)
If we have a surjective homomorphism $\varphi : M \to N$ of $R$-modules, then:
    \begin{enumerate}
        \item If $M$ is finitely generated, then $N$ is also finitely generated. 
        \item If $N$ is finitely generated, and $K = \ker(\varphi)$ is also finitely generated, then $M$ is also finitely generated. 
    \end{enumerate}

## Lemma 14
A quotient of a Noetherian ring is again Noetherian --- if $R$ is a Noetherian ring and $I$ an ideal of $R$, then the ring $S = R/I$ is also Noetherian.

## Theorem (Hilbert Basis Theorem)
If $R$ is Noetherian, then $R[x]$ is also Noetherian.

## Corollary 14
If $R$ is Noetherian, then $R[x_1, \ldots, x_n]/I$ is also Noetherian, for any ideal $I$.

## Corollary 15
Any algebraic subset in $\mathbb{C}^n$ --- a subset given by a collection of polynomial equations --- is always given by a \emph{finite} set of polynomial equations.

## Proposition (chaincondition)
A ring is Noetherian if and only if every increasing chain of ideals stabilizes. In other words, if there is a chain of ideals $I_1 \subseteq I_2 \subseteq \cdots$, then from some point on, $I_n = I_{n + 1} = \cdots$.

## Proposition (chaincondition2)
A ring is Noetherian if and only if every increasing chain of ideals stabilizes --- in other words, given any chain of ideals $I_1 \subseteq I_2 \subseteq \cdots$, from some point on we must have $I_n = I_{n + 1} = \cdots$.

## Corollary 16
In a PID, every element can be factored as a product of irreducibles.

## Proposition 19
In a Noetherian ring, every (non-unit) ideal is contained in a maximal ideal.

## Lemma 15
If we have a field extension $L/K$, then $\alpha \in L$ is algebraic if and only if $K(\alpha)$ is finite-dimensional over $K$.

## Corollary 17
If $L/K$ is finite, then every $\alpha \in L$ is algebraic over $K$.

## Proposition (tower)
Suppose that we have a tower of field extensions $K \supset E \supset F$, where $K/E$ and $E/F$ are finite. Then $K/F$ is finite, and \[[K : F] = [K : E] \cdot [E : F].\]

## Fact 1
Every field is a (possibly infinite) extension of either $\QQ$, or $\FF_p$ for a prime $p$. These are called the \textbf{primary fields}.

## Theorem (tower2)
We have \[[E : K] = [E : F]\cdot [F : K].\] In particular, $E/K$ is finite if and only if both $E/F$ and $F/K$ are finite.

## Corollary (algebraic)
If $\alpha, \beta \in L$ are algebraic over $K$, then $\alpha + \beta$, $\alpha\beta$, and $\frac{\alpha}{\beta}$ are also algebraic.

## Corollary 18
Given an arbitrary extension, the set of elements in $L$ which are algebraic over $K$ form a subfield of $L$, called the \textbf{algebraic closure} of $K$ in $L$.

## Corollary 19
If $E/F/K$ is a tower of finite extensions, then $[F : K] \mid [E : K]$.

## Fact 2
A regular $n$-gon is constructible with compass and straightedge if and only if $\zeta_n = e^{2\pi i/n}$ lies in an extension $\QQ(\alpha_1, \alpha_n)$ such that $\alpha_i^2 \in \QQ(\alpha_1, \ldots, \alpha_{n - 1})$ for all $i$.

## Theorem (constructible)
Let $n = p$ be prime. Then a regular $p$-gon can be constructed if and only if $p = 2^k + 1$.

## Proposition 20
If $p$ is prime, we have $\deg(\zeta_n) = p - 1$, or equivalently $[\QQ(\zeta_p) : \QQ] = p - 1$.

## Proposition 21
Given any polynomial $P$, its splitting field exists, and any two splitting fields of $P$ are isomorphic.

## Proposition 22
If $F$ is a field, and $P$ a (not necessarily irreducible) polynomial in $F$, then there exists a \emph{unique} extension $E/F$ up to isomorphism, such that $P$ splits as a product of linear factors in $E[x]$ as $P(x) = \prod (x - \alpha_i)$, and $E = F(\alpha_1, \ldots, \alpha_n)$.

## Theorem (finite fields)
For every prime $p$ and every $n \geq 1$, there exists a field of $q = p^n$ elements. Furthermore, any two such fields are isomorphic.

## Lemma (artin schreier)
Let $F$ be any field containing $\FF_p$, and let $q = p^n$. Then the set of roots of $A$ in $F$, \[\{x \in F \mid x^q - x = 0\},\] is a subfield of $F$.

## Proposition 23
The multiplicative group $\FF_q^\times$ is cyclic, and is therefore isomorphic to $\ZZ/(q - 1)\ZZ$.

## Lemma (cyclicmultgroup)
If $F$ is any field and $G$ is a finite subgroup of $F^\times$, then $G$ is cyclic.

## Corollary 20
For any finite field $\mathbb{F}_q$, its multiplicative group $\mathbb{F}_q^\times$ is cyclic, meaning $\mathbb{F}_q^\times \cong \mathbb{Z}/(q - 1)$.

## Corollary 21
We have $\mathbb{F}_q \cong \mathbb{F}_p(\alpha)$, and therefore, there exists an irreducible polynomial of any degree over $\mathbb{F}_p$.

## Proposition 24
If $p \neq \ell$, then $R/(p)$ is a field if and only if $\ord_{\mathbb{F}_\ell^\times} p = \ell - 1$.

## Theorem 12
If $E/F$ is a splitting field of some polynomial, then $\sigma_\gamma$ extends to an automorphism of $X$ which is the identity on $Y$, coming from an automorphism of $E$ which is the identity on $F$.

## Theorem (fundamental thm of algebra)
The field $\mathbb{C}$ is algebraically closed --- in other words, every nonconstant polynomial $P \in \mathbb{C}[x]$ has a root.

## Lemma 16
If $\gamma(t) = \gamma_1(t)\gamma_2(t)$, then $w(\gamma) = w(\gamma_1) + w(\gamma_2)$.

## Theorem 13
If $E/F$ is a finite separable extension, then the extension is generated by one element --- meaning $E = F(\alpha)$ for some $\alpha$.

## Theorem 14
If $E/F$ is a finite separable extension, then $E = F(\alpha)$ for some $\alpha$.

## Theorem (all minimal polyn split)
Suppose that $E/F$ is a splitting field of some polynomial. Then for \emph{any} $\alpha \in E$, the minimal polynomial of $\alpha$ must split completely (into linear factors) in $E$.

## Proposition (galois group size)
For any finite (separable) extension $E/F$, we have \[\lvert\operatorname{Gal}(E/F)\rvert \leq [E : F],\] with equality if and only if $E$ is the splitting field of some polynomial.

## Theorem (main theorem of galois theory)
If $E/F$ is a Galois extension with Galois group $\operatorname{Gal}(E/F)$, then there is a bijection between subgroups of $G$, and intermediate subfields $F \subseteq K \subseteq E$ --- where a subgroup $H \subset G$ is mapped to its \textbf{fixed field} \[K = E^H = \{x \in E \mid \sigma(x) = x \text{ for all } \sigma \in H\},\] and a subfield $K$ is mapped to the set of $\sigma \in G$ which fix all elements of $K$ (which by definition is $\operatorname{Gal}(E/K)$).

## Proposition 25
If $P$ is irreducible, this action is transitive --- any root can be sent to any other root.

## Theorem 15
If $E/F$ is a Galois extension (i.e. $\lvert\operatorname{Gal}(E/F)\rvert = [E : F]$), then intermediate subfields $F \subset K \subset E$ are in bijection with subgroups $H \subset G$, where a subgroup $H$ is mapped to its \textbf{fixed field} $E^H$, and a subfield $K$ is mapped to the set of $g \in G$ which fix all elements of $K$.

## Lemma (group theory lemma)
Suppose $p$ is prime, and $G \subset S_p$ such that $G$ acts on $[1, \ldots, p]$ transitively, and $G$ contains a transposition $(ij)$. Then $G = S_p$.

## Lemma 17
Both maps in the correspondence send $[E : K]$ to $\lvert H \rvert$.

## Proposition 26
The extension $K/F$ is Galois if and only if $K$ is invariant under all $g \in \operatorname{Gal}(E/F)$, which happens if and only if the corresponding $H \subset G$ is normal. In that case, $\operatorname{Gal}(K/F) = G/H$.

## Proposition 27
If $K = E^H$, then $K/F$ is Galois if and only if $K$ is invariant under all $g \in G$, which occurs if and only if $H$ is normal.

## Proposition 28
If $p = 2^k + 1$ is a Fermat prime, then a regular $p$-gon can be constructed by a compass and straightedge.

## Fact 3
$\Phi_n$ is irreducible in $\mathbb{Q}[x]$.

## Proposition 29
In this case $E/F$ is Galois, and \[\operatorname{Gal}(E/F) \cong \mathbb{Z}/m\ZZ\] for some $m \mid n$. In fact, if $x^n - a$ is irreducible in $F[x]$, then $m = n$.

## Proposition 30
Given an extension $E/F$ and some $\alpha \in E$ such that $\alpha$ can be obtained from elements of $F$ by arithmetic operations (addition, subtraction, multiplication, and division) and extracting arbitrary $n$th roots (where we're allowed to choose any of the possible $n$th roots), then $\alpha$ lies in a Galois extension of $F$ with a solvable Galois group.

## Proposition 31
$S_n$ is not solvable for $n \geq 5$.

## Corollary 22
A root of a polynomial $P$ of degree $5$ with Galois group $S_5$ cannot be expressed through the rational numbers in radicals.

## Lemma 18
If $G/K \cong H$ (equivalently, if there is an onto map $G \twoheadrightarrow H$ with kernel $K$), then:
    \begin{enumerate}
        \item If $K$ and $H$ are solvable, then $G$ is solvable. 
        \item If $G$ is solvable, then $H$ is solvable. 
    \end{enumerate}

## Lemma 19
$S_5$ is not solvable. In fact, $A_5$ is simple.

## Proposition (radical implies solvable)
Any radical extension is contained in a Galois extension with a solvable Galois group.

## Lemma 20
Under the same assumptions, if $E = F(\beta_1, \ldots, \beta_k)$ where $\beta_i^n \in F$ for all $i$ (and $F$ contains a primitive $n$th root of unity), then $\operatorname{Gal}(E/F) \subset (\ZZ/n\ZZ)^k$. In particular, $\operatorname{Gal}(E/F)$ is still abelian.

## Corollary 23
There are many nonradical extensions of $\mathbb{Q}$.

## Theorem 16
We have \[R_n = \mathbb{Z}[\sigma_1, \sigma_2, \ldots, \sigma_n].\]

## Corollary 24
A symmetric polynomial in the roots of $P$ can be written as a polynomial in the coefficients of $P$.

## Theorem (fundamental thm of sym poly)
We have $R_n = \ZZ[\sigma_1^{(n)}, \sigma_2^{(n)}, \ldots, \sigma_n^{(n)}]$, where \begin{align*}
        \sigma_1^{(n)} &= x_1 + \cdots + x_n, \\
        \sigma_2^{(n)} &= x_1x_2 + \cdots + x_{n - 1}x_n, \\
        &\;\; \vdots \\
        \sigma_n^{(n)} &= x_1\cdots x_n.
    \end{align*}

## Proposition 32
We have $\operatorname{Gal}(P) \subset A_n$ if and only if  the discriminant $\Delta$ of $P$ is a square.

## Proposition 33
If $F$ contains a primitive cube root of unity $\omega$, and $E/F$ is a Galois extension with $\operatorname{Gal}(E/F) = \mathbb{Z}/3$, then $E = F(\alpha)$ for some $\alpha^3 = a \in F$.

## Fact 4
We have \[\QQ[x_1, \ldots, x_n]^{A_n} = \QQ[x_1, \ldots, x_n]^{S_n} \oplus \delta\QQ[x_1, \ldots, x_n]^{S_n}.\]

## Proposition 34
Every $p$-group is solvable --- if $G$ is a finite group with $\lvert G\rvert = p^n$ for a prime $p$, then $G$ is solvable. Moreover, there exists a chain of subgroups \[G = G_0 \supset G_1 \supset \cdots \supset G_n = \{1\},\] such that for all $i$, $G_{i + 1}$ is a normal subgroup of $G_i$ and $G_i/G_{i + 1} \cong \mathbb{Z}/p$.

## Lemma 21
$G$ has a nontrivial center.

## Theorem 17
$\mathbb{C}$ is the only finite extension of $\mathbb{R}$.

## Lemma 22
$\lvert G \rvert$ is a power of $2$.

## Theorem 18
The extension $\mathbb{F}_{q^n}/\mathbb{F}_q$ is always a Galois extension; and $\operatorname{Gal}(\mathbb{F}_{q^n}/\mathbb{F}_q)$ is cyclic and generated by the \textbf{Frobenius automorphism} $\operatorname{Fr}_q : x \mapsto x^q$.

## Fact 5
The irreducible representations of $\operatorname{U}(n)$ are indexed by sequences of $n$ integers $d_1 \geq \cdots \geq d_n$.

## Theorem (final part of thm)
If $\rho : G \to \operatorname{GL}(V)$ is an irreducible representation of dimension $d$, then $d$ divides $|G|$.

## Proposition 35
For any irreducible representation $\rho : G \to \operatorname{GL}(V)$ of dimension $d$, we have  \[\rho(\overline{\chi_\rho}) = \frac{|G|}{d} \cdot \operatorname{Id}.\]

## Lemma 23
Algebraic integers have the following standard properties:
    \begin{enumerate}[label=(\alph*)]
        \item If $\alpha$ and $\beta$ are algebraic integers, so are $\alpha + \beta$ and $\alpha\beta$. 
        \item If $\alpha \in \QQ$ is an algebraic integer, then $\alpha \in \ZZ$. 
    \end{enumerate}

## Proposition 36
Let $\rho : G \to \operatorname{GL}(V)$ be any representation of $G$. Then if $f : G \to \CC$ is a function such that $f(g)$ is an algebraic integer for every $g$, and $\rho(f) = r\cdot \operatorname{Id}$ for a rational number $r$, then $r$ must be an integer.

## Lemma 24
For any two functions $\phi$ and $\psi$, we have \[\rho(\phi * \psi) = \rho(\phi)\rho(\psi).\]
