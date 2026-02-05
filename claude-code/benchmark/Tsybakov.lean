/-
  Tsybakov Propositions 1.1 and 1.2: Variance and Bias Bounds for Kernel Density Estimators
  From: A. B. Tsybakov, Introduction to Nonparametric Estimation, Chapter 1
-/
import Mathlib

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-!
# Kernel Density Estimation

## Main Definitions
- `IsKernel`: A function K : ℝ → ℝ is a kernel if ∫ K = 1
- `IsKernelOfOrder`: A kernel of order ℓ has vanishing moments up to order ℓ
- `HolderClass`: The Hölder class Σ(β, L) of functions
- `DensityClass`: The class P(β, L) of probability densities in the Hölder class
- `KernelEstimator`: The Parzen-Rosenblatt kernel density estimator

## Main Results
- `Tsybakov.Proposition_1_1`: Variance bound σ²(x₀) ≤ C₁/(nh)
- `Tsybakov.Proposition_1_2`: Bias bound |b(x₀)| ≤ C₂ h^β
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Tsybakov's floor function: the greatest integer strictly less than β.
    This differs from the standard floor function for integer values:
    - tsybakovFloor 2 = 1 (greatest integer strictly less than 2)
    - tsybakovFloor 2.5 = 2 (greatest integer strictly less than 2.5)
    See Tsybakov, Chapter 1: "⌊β⌋ will denote the greatest integer strictly less than β" -/
def tsybakovFloor (β : ℝ) : ℕ :=
  Nat.floor β - if β = Nat.floor β then 1 else 0

/-- A kernel is an integrable function K : ℝ → ℝ with ∫ K(u) du = 1 -/
def IsKernel (K : ℝ → ℝ) : Prop :=
  Integrable K MeasureTheory.volume ∧
  ∫ u, K u = 1

/-- A kernel of order ℓ ≥ 1 is a kernel K such that ∫ u^j K(u) du = 0 for j = 1, ..., ℓ -/
def IsKernelOfOrder (K : ℝ → ℝ) (ℓ : ℕ) : Prop :=
  IsKernel K ∧
  ∀ j : ℕ, 1 ≤ j → j ≤ ℓ → ∫ u, (u : ℝ) ^ j * K u = 0

/-- The Hölder class Σ(β, L) on an interval T.
    Functions f : T → ℝ that are ⌊β⌋ times differentiable with Hölder continuous
    highest derivative: |f^(ℓ)(x) - f^(ℓ)(x')| ≤ L|x - x'|^(β - ℓ) where ℓ = ⌊β⌋
    Note: ⌊β⌋ is Tsybakov's floor (greatest integer strictly less than β) -/
def HolderClass (β L : ℝ) : Set (ℝ → ℝ) :=
  let ℓ := tsybakovFloor β
  { f | ContDiff ℝ ℓ f ∧
        ∀ x x' : ℝ, ‖iteratedDeriv ℓ f x - iteratedDeriv ℓ f x'‖ ≤ L * |x - x'| ^ (β - ℓ) }

/-- The density class P(β, L) consists of probability densities in the Hölder class.
    p ∈ P(β, L) iff p ≥ 0, ∫ p = 1, and p ∈ Σ(β, L) -/
def DensityClass (β L : ℝ) : Set (ℝ → ℝ) :=
  { p | (∀ x, 0 ≤ p x) ∧
        ∫ x, p x = 1 ∧
        p ∈ HolderClass β L }

/-- The kernel density estimator (Parzen-Rosenblatt estimator) at a point x₀
    given observations X₁, ..., Xₙ, kernel K, and bandwidth h -/
def kernelEstimator (K : ℝ → ℝ) (h : ℝ) (X : Fin n → ℝ) (x₀ : ℝ) : ℝ :=
  (1 / (n * h)) * ∑ i, K ((X i - x₀) / h)

/-- The bias of a kernel estimator at x₀:
    b(x₀) = E[p̂ₙ(x₀)] - p(x₀) = (1/h) ∫ K((z-x₀)/h) p(z) dz - p(x₀) -/
def estimatorBias (K : ℝ → ℝ) (h : ℝ) (p : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  (1 / h) * ∫ z, K ((z - x₀) / h) * p z - p x₀

/-- The variance of a kernel estimator at x₀ -/
def estimatorVariance (K : ℝ → ℝ) (h : ℝ) (n : ℕ) (p : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  (1 / (n * h)) * (∫ z, K ((z - x₀) / h) ^ 2 * p z - h * (∫ z, K ((z - x₀) / h) * p z) ^ 2)

/-- Upper bound constant C₁ for variance in Proposition 1.1 -/
def varianceConstant (K : ℝ → ℝ) (p_max : ℝ) : ℝ :=
  p_max * ∫ u, K u ^ 2

/-- Upper bound constant C₂ for bias in Proposition 1.2
    Note: ℓ = ⌊β⌋ uses Tsybakov's floor (greatest integer strictly less than β) -/
def biasConstant (K : ℝ → ℝ) (β L : ℝ) : ℝ :=
  let ℓ := tsybakovFloor β
  (L / Nat.factorial ℓ) * ∫ u, |u| ^ β * |K u|

namespace Tsybakov

/-- **Proposition 1.1** (Variance bound for kernel estimators)

Suppose that the density p satisfies p(x) ≤ p_max < ∞ for all x ∈ ℝ.
Let K : ℝ → ℝ be a function such that ∫ K²(u) du < ∞.
Then for any x₀ ∈ ℝ, h > 0, and n ≥ 1 we have

  σ²(x₀) ≤ C₁ / (n * h)

where C₁ = p_max * ∫ K²(u) du.
-/
theorem Proposition_1_1
    (K : ℝ → ℝ)
    (p : ℝ → ℝ)
    (p_max : ℝ)
    (h : ℝ)
    (n : ℕ)
    (x₀ : ℝ)
    (hK_L2 : Integrable (fun u => K u ^ 2) MeasureTheory.volume)
    (hp_bounded : ∀ x, p x ≤ p_max)
    (hp_max_pos : 0 < p_max)
    (hh : 0 < h)
    (hn : 1 ≤ n) :
    estimatorVariance K h n p x₀ ≤ varianceConstant K p_max / (n * h) := by
  sorry

/-- **Proposition 1.2** (Bias bound for kernel estimators)

Assume that p ∈ P(β, L) and let K be a kernel of order ℓ = ⌊β⌋ satisfying
∫ |u|^β |K(u)| du < ∞. Then for all x₀ ∈ ℝ, h > 0 and n ≥ 1 we have

  |b(x₀)| ≤ C₂ * h^β

where C₂ = (L / ℓ!) * ∫ |u|^β |K(u)| du.
Note: ⌊β⌋ is Tsybakov's floor (greatest integer strictly less than β).
-/
theorem Proposition_1_2
    (K : ℝ → ℝ)
    (p : ℝ → ℝ)
    (β L : ℝ)
    (h : ℝ)
    (n : ℕ)
    (x₀ : ℝ)
    (hβ : 0 < β)
    (hL : 0 < L)
    (hp : p ∈ DensityClass β L)
    (hK : IsKernelOfOrder K (tsybakovFloor β))
    (hK_moment : Integrable (fun u => |u| ^ β * |K u|) MeasureTheory.volume)
    (hh : 0 < h)
    (hn : 1 ≤ n) :
    |estimatorBias K h p x₀| ≤ biasConstant K β L * h ^ β := by
  sorry

end Tsybakov

end
