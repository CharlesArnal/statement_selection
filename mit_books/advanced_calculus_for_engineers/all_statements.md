# All Mathematical Statements

## Statement 1: Continuity of Components of Complex Functions
**Location**: Line 261
**Text**: Theorem: If f(z) = u + iv is continuous, then u(x,y) and v(x,y) are continuous.

## Statement 2: Cauchy-Riemann Equations
**Location**: Lines 267-270
**Text**: Theorem (Cauchy-Riemann Equations): If f(z) = u + iv is analytic (where u = u(x,y), v = v(x,y) are real and z = x + iy), then du/dx = dv/dy and du/dy = -dv/dx.

## Statement 3: Cauchy Integral Theorem
**Location**: Line 340
**Text**: Cauchy Integral Theorem: If f(z) is analytic inside C and continuous on C, then the contour integral of f(z) around C equals zero: oint_C f(z) dz = 0.

## Statement 4: ML-Formula (Estimation Lemma)
**Location**: Lines 368-371
**Text**: ML-Formula: If |f(z)| <= M for z on curve C in S, then |integral_C f(z) dz| <= M * (length of C).

## Statement 5: Cauchy Integral Formula
**Location**: Lines 373-376
**Text**: Cauchy Integral Formula: If f(z) is analytic, then oint_C f(z)/(z - z_0) dz = 2*pi*i * f(z_0), equivalently f(z_0) = (1/(2*pi*i)) * oint_C f(z)/(z - z_0) dz.

## Statement 6: Theorem on Residues at Simple Poles (g/h form)
**Location**: Lines 556-597
**Text**: Theorem: If f(z) = g(z)/h(z), where g and h are analytic in 0 < |z - z_0| < delta, h(z_0) = 0, h'(z_0) != 0, and g(z_0) != 0, then z_0 is a simple pole of f(z) and the residue is Res_{z=z_0} f(z) = g(z_0)/h'(z_0).

## Statement 7: Residue Formula for mth Order Poles
**Location**: Lines 601-603
**Text**: Theorem: If z_0 is an mth order pole of f(z), then C_{-1} = (1/(m-1)!) * lim_{z->z_0} d^{m-1}/dz^{m-1} [(z - z_0)^m f(z)].

## Statement 8: Residue Theorem
**Location**: Lines 605-607
**Text**: Residue Theorem: If f(z) has isolated singularities at z_1, z_2, ..., z_n and is analytic elsewhere, then oint_C f(z) dz = 2*pi*i * sum_{k=1}^{n} Res_{z=z_k} f(z), where C encloses all these points counterclockwise.

## Statement 9: Theorem 1 (Vanishing Integral on Large Arc)
**Location**: Line 836
**Text**: Theorem 1: If z*f(z) -> 0 uniformly as |z| = R -> infinity, z = R*e^{i*theta}, then lim_{R->infinity} integral_{C_R} f(z) dz = 0, where C_R is a circular arc |z| = R, theta_1 <= theta <= theta_2.

## Statement 10: Theorem 2 (Jordan's Lemma)
**Location**: Lines 844-846
**Text**: Theorem 2 (Jordan's Lemma): If f(z) -> 0 uniformly as |z| -> infinity, then: (i) alpha > 0: integral over upper semicircle C_R+ of e^{i*alpha*z} f(z) dz -> 0 as R -> infinity; (ii) alpha < 0: integral over lower semicircle C_R- of e^{i*alpha*z} f(z) dz -> 0 as R -> infinity; and similarly for the other two cases with reversed signs.

## Statement 11: Theorem 3 (Small Circle Integral Vanishes)
**Location**: Line 848
**Text**: Theorem 3: If (z - z_0)*f(z) -> 0 uniformly as |z - z_0| = delta -> 0, then integral over the small circle of f(z) dz -> 0.

## Statement 12: Theorem 4 (Half-Residue at Simple Pole on Contour)
**Location**: Line 852
**Text**: Theorem 4: If z_0 is a simple pole of f(z), then lim_{epsilon->0} integral over a semicircular indent of radius epsilon around z_0 equals i*pi * Res_{z=z_0} f(z) (i.e., half the full residue contribution).

## Statement 13: Frobenius Method Theorem (Solutions at Regular Singular Points)
**Location**: Lines 1065
**Text**: Theorem (Frobenius): For the indicial equation with roots s_1 and s_2: if s_1 != s_2 and s_1 - s_2 is not an integer, there exist 2 independent solutions of Frobenius form; if s_1 != s_2 and s_1 - s_2 is an integer, there exist 1 or 2 solutions of Frobenius form; if s_1 = s_2, there is 1 solution of Frobenius form.

## Statement 14: Sturm-Liouville Eigenvalue Theorem
**Location**: Lines 2119-2121
**Text**: Theorem: For a proper Sturm-Liouville problem d/dx[p(x) dy/dx] + [q(x) + lambda*r(x)]y = 0 with homogeneous boundary conditions, the eigenvalues lambda form a discrete set {lambda_n}, and the corresponding eigenfunctions {phi_n(x)} are orthogonal with respect to the weight function r(x), i.e., integral r(x) phi_n phi_m dx = 0 if lambda_n != lambda_m.

## Statement 15: Fourier Convergence Theorem (Fourier's Theorem)
**Location**: Line 2469
**Text**: Theorem (Fourier): Any piecewise continuous function f(x) on [0, l] can be expanded in a Fourier sine series: f(x) = sum_{n=1}^{infinity} E_n sin(n*pi*x/L), where the convergence is understood in the mean (L^2 convergence). The coefficients are given by E_n = (2/L) * integral_0^L f(x) sin(n*pi*x/L) dx.
