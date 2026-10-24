import PairwiseIndependence.AesBounds.SboxNormTransfer
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The AES affine output map preserves the one-byte matrix norm

The paper's S-box is inversion followed by an affine bit permutation. The
constant disappears in output differences, and the linear part only
permutes difference-distribution-matrix rows.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

/-- The linear part of the FIPS AES affine byte map. -/
def aesAffineLinear (x : AesByte) : AesByte :=
  fun i => x i + x (i + 4) + x (i + 5) + x (i + 6) + x (i + 7)

private def aesInverseAffineLinear (x : AesByte) : AesByte :=
  fun i => x (i + 7) + x (i + 5) + x (i + 2)

private theorem aesAffineLinear_add (x y : AesByte) :
    aesAffineLinear (x + y) = aesAffineLinear x + aesAffineLinear y := by
  funext i
  simp only [aesAffineLinear, Pi.add_apply]
  abel

private theorem aesInverseAffineLinear_affineLinear (x : AesByte) :
    aesInverseAffineLinear (aesAffineLinear x) = x := by
  have h : ∀ x : AesByte,
      aesInverseAffineLinear (aesAffineLinear x) = x := by
    native_decide
  exact h x

private theorem aesAffineLinear_inverseAffineLinear (x : AesByte) :
    aesAffineLinear (aesInverseAffineLinear x) = x := by
  have h : ∀ x : AesByte,
      aesAffineLinear (aesInverseAffineLinear x) = x := by
    native_decide
  exact h x

/-- The additive AES output-difference permutation. -/
def aesAffineLinearEquiv : AesByte ≃+ AesByte where
  toFun := aesAffineLinear
  invFun := aesInverseAffineLinear
  left_inv := aesInverseAffineLinear_affineLinear
  right_inv := aesAffineLinear_inverseAffineLinear
  map_add' := aesAffineLinear_add

theorem aesAffine_eq_linear_add_constant (x : AesByte) :
    aesAffine x = aesAffineLinearEquiv x + aesByteOfNat 0x63 := by
  funext i
  rfl

/-- The constant `63` cancels from an AES output difference. -/
theorem aesAffine_difference_iff (u v b : AesByte) :
    aesAffine u = aesAffine v + b ↔
      u = v + aesAffineLinearEquiv.symm b := by
  rw [aesAffine_eq_linear_add_constant,
    aesAffine_eq_linear_add_constant]
  have htarget :
      aesAffineLinearEquiv v + aesByteOfNat 0x63 + b =
        aesAffineLinearEquiv (v + aesAffineLinearEquiv.symm b) +
          aesByteOfNat 0x63 := by
    rw [map_add, aesAffineLinearEquiv.apply_symm_apply]
    abel
  rw [htarget]
  constructor
  · intro h
    apply aesAffineLinearEquiv.injective
    exact add_right_cancel h
  · intro h
    rw [h]

/-- The AES S-box difference-distribution matrix is the inverse-byte
matrix with output-difference rows permuted by the affine linear layer. -/
theorem aesSbox_differenceDistributionMatrix_rowPermuted (b a : AesByte) :
    deterministicDifferenceDistributionMatrix aesSbox b a =
      deterministicDifferenceDistributionMatrix aesFieldInverse
        (aesAffineLinearEquiv.symm b) a := by
  classical
  unfold deterministicDifferenceDistributionMatrix differenceDistributionMatrix
  congr 1
  apply Finset.sum_congr rfl
  intro key _
  apply Finset.sum_congr rfl
  intro x _
  simp only [aesSbox]
  have hiff := aesAffine_difference_iff
    (aesFieldInverse (x + a)) (aesFieldInverse x) b
  by_cases h : aesFieldInverse (x + a) =
      aesFieldInverse x + aesAffineLinearEquiv.symm b
  · simp only [if_pos (hiff.mpr h), if_pos h]
  · have hs : ¬ (aesAffine (aesFieldInverse (x + a)) =
        aesAffine (aesFieldInverse x) + b) :=
      fun h' => h (hiff.mp h')
    simp only [if_neg hs, if_neg h]

private theorem aesUniformDifferenceDistributionMatrix_rowPermuted
    (b a : AesByte) :
    uniformDifferenceDistributionMatrix AesByte b a =
      uniformDifferenceDistributionMatrix AesByte
        (aesAffineLinearEquiv.symm b) a := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [uniformDifferenceDistributionMatrix_apply]
    · have hb' : aesAffineLinearEquiv.symm b ≠ 0 := by
        intro h
        apply hb
        have h' := congrArg aesAffineLinearEquiv h
        simpa using h'
      simp [uniformDifferenceDistributionMatrix_apply, hb, hb']
  · by_cases hb : b = 0
    · subst b
      simp [uniformDifferenceDistributionMatrix_apply, ha]
    · have hb' : aesAffineLinearEquiv.symm b ≠ 0 := by
        intro h
        apply hb
        have h' := congrArg aesAffineLinearEquiv h
        simpa using h'
      simp [uniformDifferenceDistributionMatrix_apply, ha, hb, hb']

private def aesAffineRowPerm : Equiv.Perm AesByte :=
  aesAffineLinearEquiv.symm.toEquiv

private theorem aesAffineRowPerm_mul_apply
    (M : Matrix AesByte AesByte ℝ) (b a : AesByte) :
    (aesAffineRowPerm.permMatrix ℝ * M) b a =
      M (aesAffineLinearEquiv.symm b) a := by
  have h := Matrix.permMatrix_mulVec (σ := aesAffineRowPerm)
    (v := fun c : AesByte => M c a)
  have hb := congrArg (fun v : AesByte → ℝ => v b) h
  simpa only [Matrix.mulVec, Matrix.mul_apply, dotProduct,
    aesAffineRowPerm] using hb

/-- The centered FIPS S-box matrix is obtained from the centered inverse
matrix by an orthogonal row permutation. -/
theorem aesSbox_centered_eq_affineRowPerm_mul :
    deterministicDifferenceDistributionMatrix aesSbox -
        uniformDifferenceDistributionMatrix AesByte =
      aesAffineRowPerm.permMatrix ℝ *
        (deterministicDifferenceDistributionMatrix aesFieldInverse -
          uniformDifferenceDistributionMatrix AesByte) := by
  ext b a
  rw [Matrix.sub_apply, aesSbox_differenceDistributionMatrix_rowPermuted,
    aesUniformDifferenceDistributionMatrix_rowPermuted,
    aesAffineRowPerm_mul_apply, Matrix.sub_apply]

/-- The certified one-byte bound for the actual FIPS AES S-box. The
threshold is slightly larger than the paper's stated `9/128`, but the
paper's two rounded Section 6 spectral exponents still follow from it. -/
theorem aesSbox_differenceDistributionMatrix_norm_le :
    ‖deterministicDifferenceDistributionMatrix aesSbox -
        uniformDifferenceDistributionMatrix AesByte‖ ≤
      (70315 : ℝ) / 1000000 := by
  rw [aesSbox_centered_eq_affineRowPerm_mul]
  calc
    ‖aesAffineRowPerm.permMatrix ℝ *
        (deterministicDifferenceDistributionMatrix aesFieldInverse -
          uniformDifferenceDistributionMatrix AesByte)‖ ≤
        ‖aesAffineRowPerm.permMatrix ℝ‖ *
          ‖deterministicDifferenceDistributionMatrix aesFieldInverse -
            uniformDifferenceDistributionMatrix AesByte‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ ‖deterministicDifferenceDistributionMatrix aesFieldInverse -
          uniformDifferenceDistributionMatrix AesByte‖ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (Matrix.permMatrix_l2_opNorm_le aesAffineRowPerm)
          (norm_nonneg
            (deterministicDifferenceDistributionMatrix aesFieldInverse -
              uniformDifferenceDistributionMatrix AesByte))
    _ ≤ (70315 : ℝ) / 1000000 :=
      aesFieldInverse_differenceDistributionMatrix_norm_le

theorem aesByte_card_ge_three : 3 ≤ Fintype.card AesByte := by
  norm_num [aesByte_card]

end PairwiseIndependence
