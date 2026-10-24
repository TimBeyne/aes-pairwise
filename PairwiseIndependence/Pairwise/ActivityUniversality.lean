import PairwiseIndependence.Pairwise.Activity

/-!
# Universality of the activity-space block for MDS layers

The paper's activity-coordinate formula depends only on the alphabet size and
the number of words. This file lifts that coordinate statement to equality
of the actual projected Hilbert-space operators. It lets a numerical
certificate for one MDS layer apply to every MDS layer with the same
parameters, including AES MixColumns.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {n : ℕ}

/-- The paper's centered normalized activity-coordinate matrix, with rows
and columns indexed only by activity patterns. It is independent of the
particular MDS layer. -/
noncomputable def mdsCenteredActivityCoordinateMatrix (q n : ℕ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  fun y x => activityCenteredCoordinate (n := n) q x y

/-- The actual MDS difference-distribution matrix has exactly the canonical
activity-coordinate matrix above. -/
theorem linear_centered_activityBasisMatrix_eq_canonical
    (L : State A n ≃+ State A n) (hMDS : IsMDS L) :
    (activityBasisMatrix (A := A) (n := n))ᵀ *
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n)) *
      activityBasisMatrix (A := A) (n := n) =
        mdsCenteredActivityCoordinateMatrix (Fintype.card A) n := by
  ext y x
  exact linear_centered_activityBasisMatrix_coordinate_eq L hMDS x y

/-- The paper's orthonormal activity coordinates give the *exact* norm of
the projected operator. `Pairwise/Activity.lean` already proves the forward bound;
this reverse bound uses the norm-preserving coordinate map. -/
theorem activityTruncatedOperator_norm_eq_compression
    (u : A) (hu : u ≠ 0)
    (M : Matrix (State A n) (State A n) ℝ) :
    ‖activityTruncatedOperator (A := A) (n := n) M‖ =
      ‖(activityOrthonormalBasisMatrix (n := n) u hu)ᵀ * M *
        activityOrthonormalBasisMatrix (n := n) u hu‖ := by
  let C := activityOrthonormalBasisMatrix (n := n) u hu
  let K := Cᵀ * M * C
  apply le_antisymm (activityTruncatedOperator_norm_le_compression u hu M)
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) K‖ ≤
    ‖activityTruncatedOperator (A := A) (n := n) M‖
  apply ContinuousLinearMap.opNorm_le_bound
    (Matrix.toEuclideanCLM (𝕜 := ℝ) K)
    (norm_nonneg (activityTruncatedOperator (A := A) (n := n) M))
  intro v
  let c : (Fin n → Bool) → ℝ := (WithLp.linearEquiv 2 ℝ _) v
  have h := (activityTruncatedOperator (A := A) (n := n) M).le_opNorm
    (activityOrthonormalBasisVector (n := n) u hu c)
  rw [activityTruncatedOperator_orthonormalBasisVector u hu M c,
    activityOrthonormalBasisVector_norm,
    activityOrthonormalBasisVector_norm] at h
  change ‖WithLp.toLp 2 (K *ᵥ c)‖ ≤
    ‖activityTruncatedOperator (A := A) (n := n) M‖ *
      ‖WithLp.toLp 2 c‖
  exact h

/-- The exact numerical activity-space problem for any MDS layer is the
norm of one small canonical matrix, independent of the layer and S-box. -/
theorem linear_centered_truncatedNorm_eq_canonical
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L) :
    ‖activityTruncatedOperator
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) -
        uniformDifferenceDistributionMatrix (State A n))‖ =
      ‖(activityGramInverseSquareRoot (n := n) u hu)ᵀ *
        mdsCenteredActivityCoordinateMatrix (Fintype.card A) n *
        activityGramInverseSquareRoot (n := n) u hu‖ := by
  let B := activityBasisMatrix (A := A) (n := n)
  let R := activityGramInverseSquareRoot (n := n) u hu
  let M := deterministicDifferenceDistributionMatrix
      (fun a : State A n => L a) -
    uniformDifferenceDistributionMatrix (State A n)
  rw [activityTruncatedOperator_norm_eq_compression u hu]
  change ‖(B * R)ᵀ * M * (B * R)‖ =
    ‖Rᵀ * mdsCenteredActivityCoordinateMatrix (Fintype.card A) n * R‖
  calc
    ‖(B * R)ᵀ * M * (B * R)‖ = ‖Rᵀ * (Bᵀ * M * B) * R‖ := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by rw [linear_centered_activityBasisMatrix_eq_canonical L hMDS]

end PairwiseIndependence
