/-
  Bubeck Theorem 3.18: Nesterov's Accelerated Gradient Descent Convergence
  From: S. Bubeck, Convex Optimization: Algorithms and Complexity, Chapter 3
-/
import Mathlib

open Set Filter Topology InnerProductSpace
open scoped ENNReal NNReal Topology

noncomputable section

/-!
# Nesterov's Accelerated Gradient Descent

## Main Definitions
- `IsConvex`: Convexity of a function on a set
- `IsStronglyConvex`: α-strong convexity
- `IsSmooth`: β-smoothness (β-Lipschitz gradient)
- `NesterovAGD`: Nesterov's accelerated gradient descent iterates

## Main Results
- `Bubeck.Theorem_3_18`: Convergence rate for Nesterov's accelerated gradient descent
  on strongly convex and smooth functions
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient of f at x, defined as the Riesz representation of the Fréchet derivative -/
def grad (f : E → ℝ) (x : E) : E :=
  (toDual ℝ E).symm (fderiv ℝ f x)

/-- A function f is β-smooth if its gradient is β-Lipschitz:
    ‖∇f(x) - ∇f(y)‖ ≤ β‖x - y‖ for all x, y -/
def IsSmooth (f : E → ℝ) (β : ℝ) : Prop :=
  Differentiable ℝ f ∧
  ∀ x y : E, ‖grad f x - grad f y‖ ≤ β * ‖x - y‖

/-- A function f is α-strongly convex if for all x, y:
    f(x) - f(y) ≤ ⟨∇f(x), x - y⟩ - (α/2)‖x - y‖² -/
def IsStronglyConvex (f : E → ℝ) (α : ℝ) : Prop :=
  Differentiable ℝ f ∧
  ∀ x y : E, f x - f y ≤ ⟪grad f x, x - y⟫_ℝ - (α / 2) * ‖x - y‖ ^ 2

/-- The condition number κ = β/α for a β-smooth and α-strongly convex function -/
def conditionNumber (α β : ℝ) : ℝ := β / α

/-- Nesterov's accelerated gradient descent primary sequence (y_t).
    y_{t+1} = x_t - (1/β)∇f(x_t) -/
def nesterovPrimaryStep (f : E → ℝ) (β : ℝ) (x : E) : E :=
  x - (1 / β) • grad f x

/-- Nesterov's accelerated gradient descent secondary sequence (x_t).
    x_{t+1} = (1 + (√κ-1)/(√κ+1)) y_{t+1} - ((√κ-1)/(√κ+1)) y_t -/
def nesterovSecondaryStep (κ : ℝ) (y_new y_old : E) : E :=
  let r := (Real.sqrt κ - 1) / (Real.sqrt κ + 1)
  (1 + r) • y_new - r • y_old

/-- The sequence of iterates for Nesterov's accelerated gradient descent -/
structure NesterovIterates (f : E → ℝ) (β κ : ℝ) where
  x : ℕ → E  -- secondary sequence
  y : ℕ → E  -- primary sequence
  init : x 0 = y 0
  primary_step : ∀ t, y (t + 1) = nesterovPrimaryStep f β (x t)
  secondary_step : ∀ t, x (t + 1) = nesterovSecondaryStep κ (y (t + 1)) (y t)

/-- Existence of a minimizer x* with ∇f(x*) = 0 -/
def HasMinimizer (f : E → ℝ) (x_star : E) : Prop :=
  Differentiable ℝ f ∧ grad f x_star = 0 ∧ ∀ x, f x_star ≤ f x

namespace Bubeck

/-- **Theorem 3.18** (Nesterov's accelerated gradient descent convergence)

Let f be α-strongly convex and β-smooth, then Nesterov's accelerated gradient descent
satisfies:

  f(y_t) - f(x*) ≤ (α + β)/2 · ‖x₁ - x*‖² · exp(-(t-1)/√κ)

where κ = β/α is the condition number.

This achieves the optimal oracle complexity of O(√κ log(1/ε)) for strongly convex
smooth optimization.
-/
theorem Theorem_3_18
    (f : E → ℝ)
    (α β : ℝ)
    (x_star : E)
    (hα : 0 < α)
    (hβ : 0 < β)
    (hαβ : α ≤ β)
    (hf_strongly_convex : IsStronglyConvex f α)
    (hf_smooth : IsSmooth f β)
    (hf_min : HasMinimizer f x_star)
    (iterates : NesterovIterates f β (conditionNumber α β))
    (t : ℕ)
    (ht : 1 ≤ t) :
    f (iterates.y t) - f x_star ≤
      ((α + β) / 2) * ‖iterates.x 0 - x_star‖ ^ 2 *
        Real.exp (-(↑t - 1) / Real.sqrt (conditionNumber α β)) := by
  sorry

/-- Corollary: The number of iterations to reach ε-accuracy is O(√κ log(1/ε)) -/
theorem oracle_complexity
    (f : E → ℝ)
    (α β : ℝ)
    (x_star x₀ : E)
    (ε : ℝ)
    (hα : 0 < α)
    (hβ : 0 < β)
    (hαβ : α ≤ β)
    (hε : 0 < ε)
    (hf_strongly_convex : IsStronglyConvex f α)
    (hf_smooth : IsSmooth f β)
    (hf_min : HasMinimizer f x_star)
    (iterates : NesterovIterates f β (conditionNumber α β))
    (h_init : iterates.x 0 = x₀) :
    ∃ T : ℕ, T ≤ Nat.ceil (Real.sqrt (conditionNumber α β) *
                           Real.log (((α + β) / 2) * ‖x₀ - x_star‖ ^ 2 / ε)) ∧
              f (iterates.y T) - f x_star ≤ ε := by
  sorry

end Bubeck

end
