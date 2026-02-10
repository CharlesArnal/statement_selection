# All Mathematical Statements from Introduction to Numerical Methods (18.335J)

Note: This is a numerical methods textbook (MIT 18.335J) consisting of lecture slides, notes on specific algorithms, and computational techniques. It does NOT contain formally labeled theorems, lemmas, propositions, or corollaries in the traditional sense. The textbook references several well-known mathematical results informally, and presents a few semi-formal proofs. The statements below are extracted from these informal references and semi-formal presentations.

## Statement 1: Monotone Convergence Theorem for Sequences (referenced as "Rudin theorem 3.14")
A monotonic-decreasing sequence that is bounded below converges.

(Referenced at line 40 of the textbook in the context of proving convergence of Newton's method for square roots.)

## Statement 2: Equivalence of Norms on Finite-Dimensional Vector Spaces
If we are given two norms $\|\cdot\|_a$ and $\|\cdot\|_b$ on some finite-dimensional vector space $V$ over $\mathbb{C}$, there exists a pair of real numbers $0 < C_1 \le C_2$ such that, for all $x \in V$:
$$C_1 \|x\|_b \le \|x\|_a \le C_2 \|x\|_b.$$

(Stated at line 215 and proved in detail through Steps 1-4, lines 215-298.)

## Statement 3: Extreme Value Theorem
A continuous function on a compact set must achieve a maximum and minimum value on the set.

(Stated at line 288, used in Step 4 of the equivalence of norms proof.)

## Statement 4: Convex Optimization -- Local Optima are Global Optima
For a convex problem (convex objective and constraints), any local optimum must be a global optimum.

(Stated at line 1304 in the overview of optimization problems.)

## Statement 5: Cauchy-Schwarz Inequality
For any inner product $\langle x, y \rangle$, it is always true that $\langle x, x \rangle \langle \delta, \delta \rangle \geq |\langle x, \delta \rangle|^2$.

(Stated at line 1966 in the context of proving positive-definiteness of the BFGS update.)

## Statement 6: Hellmann-Feynman Theorem
For a real-symmetric matrix $A(\mathbf{p})$ with eigenvector $\mathbf{x}$ and eigenvalue $\alpha$ (i.e., $A\mathbf{x} = \alpha\mathbf{x}$), the derivative of the eigenvalue with respect to parameters is $\alpha_{\mathbf{p}} = \mathbf{x}^T A_p \mathbf{x}$.

(Stated at line 1550 as a consequence of the adjoint method for eigenproblems.)

## Statement 7: Abel's Theorem (Abel-Ruffini Theorem, referenced informally)
There is no general algebraic solution to polynomial equations of degree five or higher.

(Referenced at line 962: "We already knew this would not work, because of Abel's theorem," in the context of why direct Householder reflectors cannot compute the Schur factorization.)

## Statement 8: Euler's Identity
$e^{i\phi} = \cos\phi + i\sin\phi$.

(Stated at line 2025 in the context of the DFT definition.)

## Statement 9: Chinese Remainder Theorem (referenced informally)
If $\gcd(N_1, N_2) = 1$, there exists a re-indexing based on the Chinese Remainder Theorem.

(Referenced at lines 2054 and 2225 in the context of FFT algorithms.)

## Statement 10: Sherman-Morrison Formula
$(A + uv^T)^{-1} = A^{-1} - \frac{A^{-1}uv^TA^{-1}}{1 + v^TA^{-1}u}$.

(Stated at line 1970 in the context of BFGS updates.)

## Statement 11: Backward Stability of Householder Hessenberg Reduction
The Householder Hessenberg reduction algorithm is backward stable: $\tilde{Q}\tilde{H}\tilde{Q}^* = A + \delta A$, where $\frac{\|\delta A\|}{\|A\|} = O(\epsilon_{\text{machine}})$ and $\tilde{Q}$ is an exactly unitary matrix.

(Stated at lines 1003-1007.)

## Statement 12: DFT Inverse Formula
The DFT defined by $y_k = \sum_{n=0}^{N-1} x_n e^{-\frac{2\pi i}{N}nk}$ has inverse $x_n = \frac{1}{N} \sum_{k=0}^{N-1} y_k e^{+\frac{2\pi i}{N} nk}$.

(Stated at lines 2017-2024, with the proof left as a homework problem.)

## Statement 13: Convolution Theorem
Cyclic convolution $c_n = \sum_{m=0}^{N-1} a_m b_{n-m}$ can be evaluated in $O(N \log N)$ time via: $c_n = \text{inverse FFT}(\text{FFT}(a_n) \cdot \text{FFT}(b_n))$.

(Stated at line 2060.)
