# Short Assessment: Intersection Theory on Moduli Spaces vs. Mathlib

## Summary Statistics

- **Total formal statements found:** 91
- **Statements with partial or full match in mathlib:** 5
- **Statements with no match in mathlib:** 86
- **Match rate:** ~5.5%

## Statements with Mathlib Coverage

| # | Statement | Mathlib Status | Mathlib File |
|---|-----------|---------------|--------------|
| 1 | Theorem 2.18 (Grassmannian functor representability) | PARTIAL -- Grassmannian defined as a set of submodules; representability as a scheme is listed as TODO | `Mathlib/RingTheory/Grassmannian.lean` |
| 2 | Theorem 5.10 (Valuative criterion for separatedness) | YES -- formalized for schemes (not stacks) | `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` |
| 3 | Theorem 5.11 (Valuative criterion of properness) | YES -- formalized for schemes (not stacks) | `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` |
| 4 | Theorem 2.2 (Hilbert scheme representability) | NO | not in mathlib |
| 5 | Picard group (Theorems 4.1, 4.2 from Part 2) | TANGENTIAL -- Picard group defined for commutative rings, not for moduli stacks | `Mathlib/RingTheory/PicardGroup.lean` |

## Why the Match Rate Is So Low

This textbook covers advanced topics at the research frontier of algebraic geometry:

1. **Moduli spaces** (M_g, M_{g,n}, Kontsevich spaces): Not defined in mathlib at all. No stacks, no Deligne-Mumford theory, no coarse moduli spaces.
2. **Intersection theory / Chow rings**: Entirely absent from mathlib.
3. **Schubert calculus** (Pieri, Giambelli, Littlewood-Richardson): Not in mathlib.
4. **GIT quotients**: Not in mathlib. No reductive groups, no stability conditions.
5. **Brill-Noether theory**: Not in mathlib.
6. **Uniformization, Teichmuller theory**: Not in mathlib.
7. **Stable reduction, Kodaira dimension**: Not in mathlib.
8. **Hilbert schemes**: Not in mathlib (only the Hilbert polynomial in RingTheory).

The only area where mathlib has begun to develop relevant infrastructure is basic scheme theory (separated/proper morphisms, valuative criteria) and the module-level definition of the Grassmannian.
