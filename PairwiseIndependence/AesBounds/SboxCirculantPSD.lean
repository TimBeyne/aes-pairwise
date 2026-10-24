import PairwiseIndependence.AesBounds.SboxCirculantCertificate
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Positive-semidefinite circulant certificate on nonzero byte differences

This file turns the one-row rational computation into a matrix certificate.
`SboxCyclicIdentification` identifies its Gram coefficients with the
inverse-byte difference-distribution matrix.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

private abbrev ByteCycle := ZMod 255

private def byteCycleToFin (z : ByteCycle) : Fin 255 :=
  (ZMod.finEquiv 255).symm z

private def cyclicGram (z : ByteCycle) : ℚ :=
  aesSboxCyclicGramCoefficient (byteCycleToFin z)

private def cyclicFactor (z : ByteCycle) : ℚ :=
  aesSboxCyclicFactorCoefficient (byteCycleToFin z)

private def cyclicAutocorrelation (z : ByteCycle) : ℚ :=
  ∑ x : ByteCycle, cyclicFactor x * cyclicFactor (x + z)

private def cyclicResidual (z : ByteCycle) : ℚ :=
  (if z = 0 then (70315 / 1000000 : ℚ) ^ 2 else 0) -
    cyclicGram z - cyclicAutocorrelation z

private theorem cyclicResidual_diagonalDominant :
    (∑ z ∈ Finset.univ.erase (0 : ByteCycle), |cyclicResidual z|) <
      cyclicResidual 0 := by
  native_decide

private theorem cyclicResidual_neg (z : ByteCycle) :
    cyclicResidual (-z) = cyclicResidual z := by
  have h : ∀ z : ByteCycle, cyclicResidual (-z) = cyclicResidual z := by
    native_decide
  exact h z

private def cyclicGramMatrix : Matrix ByteCycle ByteCycle ℚ :=
  fun i j => cyclicGram (j - i)

private def cyclicFactorMatrix : Matrix ByteCycle ByteCycle ℚ :=
  fun i j => cyclicFactor (j - i)

private def cyclicResidualMatrix : Matrix ByteCycle ByteCycle ℚ :=
  fun i j => cyclicResidual (j - i)

private theorem cyclicFactorMatrix_gram_apply (i j : ByteCycle) :
    (cyclicFactorMatrixᵀ * cyclicFactorMatrix) i j =
      cyclicAutocorrelation (j - i) := by
  have hbij : Function.Bijective (fun k : ByteCycle => i - k) := by
    constructor
    · intro a b h
      change i - a = i - b at h
      have hneg : -a = -b := add_left_cancel (by simpa only [sub_eq_add_neg] using h)
      exact neg_injective hneg
    · intro a
      exact ⟨i - a, by simp⟩
  have hsum :
      (∑ k : ByteCycle, cyclicFactor (i - k) * cyclicFactor (j - k)) =
        ∑ k : ByteCycle, cyclicFactor k * cyclicFactor (k + (j - i)) := by
    exact Fintype.sum_bijective (fun k : ByteCycle => i - k) hbij
      (fun k => cyclicFactor (i - k) * cyclicFactor (j - k))
      (fun k => cyclicFactor k * cyclicFactor (k + (j - i)))
      (fun k => by
        change cyclicFactor (i - k) * cyclicFactor (j - k) =
          cyclicFactor (i - k) * cyclicFactor ((i - k) + (j - i))
        rw [show j - k = (i - k) + (j - i) by abel])
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, cyclicFactorMatrix,
    cyclicAutocorrelation] using hsum

private theorem cyclicResidualMatrix_rowSum (i : ByteCycle) :
    (∑ j ∈ Finset.univ.erase i, |cyclicResidualMatrix i j|) =
      ∑ k ∈ Finset.univ.erase (0 : ByteCycle), |cyclicResidual k| := by
  have hbij : Function.Bijective (fun j : ByteCycle => j - i) := by
    simpa only [sub_eq_add_neg] using
      (AddGroup.addRight_bijective (-i) :
        Function.Bijective (fun j : ByteCycle => j + -i))
  have hsum :
      (∑ j : ByteCycle, |cyclicResidual (j - i)|) =
        ∑ k : ByteCycle, |cyclicResidual k| :=
    Fintype.sum_bijective (fun j : ByteCycle => j - i) hbij
      (fun j => |cyclicResidual (j - i)|)
      (fun k => |cyclicResidual k|) (fun j => rfl)
  calc
    (∑ j ∈ Finset.univ.erase i, |cyclicResidualMatrix i j|) =
        (∑ j : ByteCycle, |cyclicResidual (j - i)|) - |cyclicResidual 0| := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      simp only [cyclicResidualMatrix, sub_self]
    _ = (∑ k : ByteCycle, |cyclicResidual k|) - |cyclicResidual 0| := by
      rw [hsum]
    _ = ∑ k ∈ Finset.univ.erase (0 : ByteCycle), |cyclicResidual k| := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : ByteCycle))]

private theorem cyclicResidualMatrix_symmetric :
    cyclicResidualMatrixᵀ = cyclicResidualMatrix := by
  ext i j
  change cyclicResidual (i - j) = cyclicResidual (j - i)
  rw [show i - j = -(j - i) by abel, cyclicResidual_neg]

private theorem cyclicResidualMatrix_real_posSemidef :
    (cyclicResidualMatrix.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  let R : Matrix ByteCycle ByteCycle ℝ :=
    cyclicResidualMatrix.map (fun q : ℚ => (q : ℝ))
  have hR : R.IsHermitian := by
    change Rᴴ = R
    simpa only [R, Matrix.conjTranspose, star_trivial,
      Matrix.transpose_map] using
      congrArg (fun X : Matrix ByteCycle ByteCycle ℚ =>
        X.map (fun q : ℚ => (q : ℝ))) cyclicResidualMatrix_symmetric
  apply matrix_posSemidef_of_diagonalDominant R hR
  intro i
  have hQ :
      (∑ j ∈ Finset.univ.erase i, |cyclicResidualMatrix i j|) ≤
        cyclicResidualMatrix i i := by
    rw [cyclicResidualMatrix_rowSum]
    exact le_of_lt (by simpa only [cyclicResidualMatrix, sub_self] using
      cyclicResidual_diagonalDominant)
  change (∑ j ∈ Finset.univ.erase i,
    |(cyclicResidualMatrix i j : ℝ)|) ≤ (cyclicResidualMatrix i i : ℝ)
  exact_mod_cast hQ

private theorem cyclicGram_rational_factorization :
    (70315 / 1000000 : ℚ) ^ 2 • (1 : Matrix ByteCycle ByteCycle ℚ) -
      cyclicGramMatrix =
        cyclicFactorMatrixᵀ * cyclicFactorMatrix + cyclicResidualMatrix := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    cyclicGramMatrix, cyclicResidualMatrix,
    cyclicFactorMatrix_gram_apply]
  by_cases hij : i = j
  · subst j
    simp [cyclicResidual]
  · have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    simp [cyclicResidual, hij, hji]

/-- The proposed 255×255 cyclic Gram matrix has an exact rational
sum-of-squares certificate with a diagonally dominant residual. -/
theorem aesSboxCyclicGram_bound :
    Matrix.PosSemidef
      (((70315 / 1000000 : ℝ) ^ 2) •
        (1 : Matrix ByteCycle ByteCycle ℝ) -
        cyclicGramMatrix.map (fun q : ℚ => (q : ℝ))) := by
  let B : Matrix ByteCycle ByteCycle ℝ :=
    cyclicFactorMatrix.map (fun q : ℚ => (q : ℝ))
  have hsum : (Bᴴ * B +
      cyclicResidualMatrix.map (fun q : ℚ => (q : ℝ))).PosSemidef :=
    (Matrix.posSemidef_conjTranspose_mul_self B).add
      cyclicResidualMatrix_real_posSemidef
  have hcast := congrArg
    (fun X : Matrix ByteCycle ByteCycle ℚ =>
      X.map (fun q : ℚ => (q : ℝ)))
    cyclicGram_rational_factorization
  have hcast2 :
      (((70315 / 1000000 : ℚ) ^ 2 •
          (1 : Matrix ByteCycle ByteCycle ℚ) - cyclicGramMatrix).map
          (fun q : ℚ => (q : ℝ))) =
        Bᵀ * B + cyclicResidualMatrix.map (fun q : ℚ => (q : ℝ)) := by
    change (((70315 / 1000000 : ℚ) ^ 2 •
        (1 : Matrix ByteCycle ByteCycle ℚ) - cyclicGramMatrix).map
        (fun q : ℚ => (q : ℝ))) =
      (cyclicFactorMatrixᵀ * cyclicFactorMatrix + cyclicResidualMatrix).map
        (fun q : ℚ => (q : ℝ)) at hcast
    rw [Matrix.map_add _ (by intro a b; norm_num),
      Matrix.map_mul_ratCast, Matrix.transpose_map] at hcast
    simpa only [B] using hcast
  have heq :
      ((70315 / 1000000 : ℝ) ^ 2) •
          (1 : Matrix ByteCycle ByteCycle ℝ) -
          cyclicGramMatrix.map (fun q : ℚ => (q : ℝ)) =
        Bᴴ * B +
          cyclicResidualMatrix.map (fun q : ℚ => (q : ℝ)) := by
    rw [show Bᴴ = Bᵀ by ext i j; simp [Matrix.conjTranspose]]
    rw [← hcast2]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  rw [heq]
  exact hsum

/-- The real Gram-kernel candidate, indexed by multiplicative exponents of
nonzero AES bytes. The coefficient table is checked by the rational
sum-of-squares certificate above; its AES S-box identification is separate. -/
noncomputable def aesSboxCyclicGramRealMatrix :
    Matrix (ZMod 255) (ZMod 255) ℝ :=
  fun i j =>
    (aesSboxCyclicGramCoefficient
      ((ZMod.finEquiv 255).symm (j - i)) : ℝ)

/-- Any real matrix with this cyclic Gram matrix has norm below the rational
threshold used by the finite certificate. -/
theorem aesSboxCyclicGram_norm_le
    (M : Matrix (ZMod 255) (ZMod 255) ℝ)
    (hGram : Mᴴ * M = aesSboxCyclicGramRealMatrix) :
    ‖M‖ ≤ (70315 : ℝ) / 1000000 := by
  apply matrix_twoNorm_le_of_gram_residual_posSemidef M
    ((70315 : ℝ) / 1000000) (by norm_num)
  rw [hGram]
  simpa only [aesSboxCyclicGramRealMatrix, cyclicGramMatrix,
    cyclicGram, byteCycleToFin, Matrix.map_apply] using
      aesSboxCyclicGram_bound

end PairwiseIndependence
