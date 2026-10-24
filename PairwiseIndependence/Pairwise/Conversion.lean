import PairwiseIndependence.Pairwise.Stochastic
import PairwiseIndependence.Pairwise.LinearAlgebra

/-!
# Conversion from spectral to one-norm bounds

This file exposes the paper's Lemma 6. It combines the stochastic identities
for difference-distribution matrices with the purely linear-algebraic norm
estimate. The keys in the two families are independent when their matrices
are multiplied; `differenceDistributionMatrix_keyedComposition` gives the
concrete intermediate-key model for such a product.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

/-- Lemma 6 (Conversion) of the paper. `p` bounds all entries for nonzero input
differences of the first keyed permutation family. The conclusion uses the
matrix one norm and the spectral two norm exactly as in the paper. -/
theorem lemma6_conversion
    {A κ ι : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (f : κ → A → A) (g : ι → A → A)
    (hf : ∀ key, Function.Bijective (f key))
    (hg : ∀ key, Function.Bijective (g key))
    (p : ℝ) (hp : 0 ≤ p)
    (hmax : ∀ a b : A, a ≠ 0 → differenceDistributionMatrix f b a ≤ p) :
    matrixOneNorm
      (differenceDistributionMatrix g * differenceDistributionMatrix f -
        uniformDifferenceDistributionMatrix A) ≤
      (Fintype.card A : ℝ) * p *
        ‖differenceDistributionMatrix g - uniformDifferenceDistributionMatrix A‖ := by
  exact conversion_core _ _ p hp
    (differenceDistributionMatrix_product_centering f g hf hg)
    (centeredDifferenceDistributionMatrix_entry_bound f hf p hp hmax)

/-- Iterating Lemma 6: a nontrivial differential bound for one block and a
spectral bound for that block control the one norm after `r + 1` independent
blocks. The case `r = 0` uses the entry bound directly. -/
theorem conversion_power
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key))
    (p β : ℝ) (hp : 0 ≤ p)
    (hmax : ∀ a b : A, a ≠ 0 → differenceDistributionMatrix f b a ≤ p)
    (hspectral :
      ‖differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A‖ ≤ β)
    (r : ℕ) :
    matrixOneNorm
      ((differenceDistributionMatrix f) ^ (r + 1) -
        uniformDifferenceDistributionMatrix A) ≤
      (Fintype.card A : ℝ) * p * β ^ r := by
  let D := differenceDistributionMatrix f
  let U := uniformDifferenceDistributionMatrix A
  have hentry : ∀ b a : A, |(D - U) b a| ≤ p :=
    centeredDifferenceDistributionMatrix_entry_bound f hf p hp hmax
  have hDU : D * U = U := differenceDistributionMatrix_mul_uniform f hf
  have hUD : U * D = U := uniform_mul_differenceDistributionMatrix f hf
  have hUU : U * U = U := uniformDifferenceDistributionMatrix_mul_self
  cases r with
  | zero =>
      simp only [zero_add, pow_one, pow_zero, mul_one]
      rw [matrixOneNorm_le_iff]
      intro a
      calc
        (∑ b : A, |(D - U) b a|) ≤ ∑ _b : A, p :=
          Finset.sum_le_sum (fun b _ => hentry b a)
        _ = (Fintype.card A : ℝ) * p := by simp
  | succ r =>
      have hpow : D ^ (r + 1) * U = U :=
        power_mul_stationary_projection D U hDU r
      have hcenter :
          D ^ (r + 1) * D - U =
            (D ^ (r + 1) - U) * (D - U) := by
        rw [sub_mul, mul_sub, mul_sub, hpow, hUD, hUU]
        abel
      have hnorm : ‖D ^ (r + 1) - U‖ ≤ β ^ (r + 1) := by
        rw [centered_power D U hDU hUD hUU r]
        calc
          ‖(D - U) ^ (r + 1)‖ ≤ ‖D - U‖ ^ (r + 1) := norm_pow_le _ _
          _ ≤ β ^ (r + 1) := by gcongr
      change matrixOneNorm (D ^ (r + 1 + 1) - U) ≤
        (Fintype.card A : ℝ) * p * β ^ (r + 1)
      rw [pow_succ]
      calc
        matrixOneNorm (D ^ (r + 1) * D - U) ≤
            (Fintype.card A : ℝ) * p * ‖D ^ (r + 1) - U‖ :=
          conversion_core D (D ^ (r + 1)) p hp hcenter hentry
        _ ≤ (Fintype.card A : ℝ) * p * β ^ (r + 1) := by gcongr

end PairwiseIndependence
