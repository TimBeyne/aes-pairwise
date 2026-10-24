import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.Perm

/-!
# Definitions in the statements of the main theorems

Together with `AES/AES.lean`, this file contains every definition that the
statements of Theorems 3, 4, 5 and Corollary 2 depend on; the rest of the
project consists of proofs, which Lean checks.

Matrices over a difference set `A` have rows indexed by output differences and
columns by input differences. In the theorem statements `‖·‖` on matrices is
the Euclidean operator norm (`open scoped Matrix.Norms.L2Operator`).
-/

namespace PairwiseIndependence

section DifferenceDistribution

variable {A κ : Type*} [AddCommGroup A] [Fintype A] [Fintype κ]

/-- The key-averaged difference-distribution matrix from Equation (1) of the paper. -/
noncomputable def differenceDistributionMatrix (f : κ → A → A) : Matrix A A ℝ := by
  classical
  exact fun b a =>
    (∑ k : κ, ∑ x : A, if f k (x + a) = f k x + b then (1 : ℝ) else 0) /
      ((Fintype.card κ * Fintype.card A : ℕ) : ℝ)

/-- The difference-distribution matrix `U` of a uniformly random permutation of
`A`. -/
noncomputable def uniformDifferenceDistributionMatrix
    (A : Type*) [AddCommGroup A] [Fintype A] : Matrix A A ℝ := by
  classical
  exact differenceDistributionMatrix (fun σ : Equiv.Perm A => (σ : A → A))

end DifferenceDistribution

section Probability

variable {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
  [Fintype κ]

/-- The keyed family `f` with input and output whitening keys: the key
`(k, k₁, k₂)` maps `x` to `f k (x + k₁) + k₂`. -/
def whitenedCipher (f : κ → A → A) (key : κ × A × A) (x : A) : A :=
  f key.1 (x + key.2.1) + key.2.2

/-- Exact pair-output probability, expressed as a finite uniform average. -/
noncomputable def jointOutputProbability (f : κ → A → A)
    (x₁ x₂ y₁ y₂ : A) : ℝ := by
  classical
  exact (∑ key : κ × A × A,
    if whitenedCipher f key x₁ = y₁ ∧ whitenedCipher f key x₂ = y₂
    then (1 : ℝ) else 0) /
      ((Fintype.card κ * Fintype.card A * Fintype.card A : ℕ) : ℝ)

/-- The paper's statistical distance for a fixed pair of distinct inputs. -/
noncomputable def pairwiseDistance (f : κ → A → A) (x₁ x₂ : A) : ℝ := by
  classical
  exact (1 / 2 : ℝ) *
    ∑ y₁ : A, ∑ y₂ : A,
      if y₁ = y₂ then 0 else
        |jointOutputProbability f x₁ x₂ y₁ y₂ -
          1 / ((Fintype.card A : ℝ) * (Fintype.card A - 1))|

/-- Definition 1 in the paper, with uniform independent whitening keys. -/
def IsPairwiseIndependent (f : κ → A → A) (ε : ℝ) : Prop :=
  ∀ x₁ x₂ : A, x₁ ≠ x₂ → pairwiseDistance f x₁ x₂ ≤ ε

end Probability

section Shark

variable {A : Type*} [AddCommGroup A] [Fintype A] {n : ℕ}

abbrev State (A : Type*) (n : ℕ) := Fin n → A

/-- Number of active word positions in a state. -/
def activeCoordinates [DecidableEq A] (x : State A n) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- The word-level MDS condition used by Theorem 3: every nonzero input and
its image have at least `n + 1` active coordinates together. This formulation
also covers the AES superbox mixing layer, which is additive on 32-bit words
without being linear over a 32-bit field. -/
def IsMDS [DecidableEq A] (L : State A n ≃+ State A n) : Prop :=
  ∀ x : State A n, x ≠ 0 → n + 1 ≤ activeCoordinates x + activeCoordinates (L x)

/-- Apply a bijective S-box independently to every coordinate. -/
def substitute (S : A ≃ A) (x : State A n) : State A n := fun i => S (x i)

/-- The paper's two-round SHARK core: substitution, key addition, linear mixing,
then substitution. Its difference-distribution matrix is bounded by Theorem 3. -/
def sharkTwoCore (S : A ≃ A) (L : State A n ≃+ State A n)
    (key : State A n) (x : State A n) : State A n :=
  substitute S (L (substitute S x + key))

end Shark

end PairwiseIndependence
