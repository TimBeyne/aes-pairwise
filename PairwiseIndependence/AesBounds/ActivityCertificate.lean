import PairwiseIndependence.Pairwise.ActivityUniversality
import PairwiseIndependence.AesBounds.Superbox
import PairwiseIndependence.Pairwise.MatrixNormCertificate

/-!
# Finite certificate target for the AES superbox activity block

The paper reports the `2^(-13.351)` activity-block norm numerically. The
preceding algebra proves that this block is independent of the concrete MDS
layer and S-box. The remaining certificate is the norm of a 16×16 matrix
indexed by four-bit activity patterns; no AES state enumeration is needed.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

/-- For the AES byte size, the square-root normalization of activity
coordinates is the rational power `16^m`. -/
theorem aesActivity_sqrt_card_pow (m : ℕ) :
    Real.sqrt ((256 : ℝ) ^ m) = (16 : ℝ) ^ m := by
  have hpow : (256 : ℝ) ^ m = ((16 : ℝ) ^ m) ^ 2 := by
    calc
      (256 : ℝ) ^ m = ((16 : ℝ) * 16) ^ m := by norm_num
      _ = ((16 : ℝ) ^ m) ^ 2 := by rw [mul_pow, pow_two]
  rw [hpow]
  exact Real.sqrt_sq (pow_nonneg (by norm_num) _)

/-- A rational-entry form of the paper's 16×16 centered activity matrix
for four AES bytes. Its entries depend only on the two activity weights. -/
noncomputable def aesRationalCenteredActivityMatrix :
    Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ :=
  fun y x =>
    ((if 5 ≤ activityWeight x + activityWeight y then
        (256 : ℝ) ^ (activityWeight x + activityWeight y - 4)
      else 1) -
      (1 +
        (((256 : ℝ) ^ activityWeight x - 1) *
          ((256 : ℝ) ^ activityWeight y - 1)) /
            ((256 : ℝ) ^ 4 - 1))) /
      (16 : ℝ) ^ (activityWeight x + activityWeight y)

/-- The canonical activity-coordinate matrix equals its rational form.
This removes square roots before the finite numerical certificate. -/
theorem aesCenteredActivityMatrix_eq_rational :
    mdsCenteredActivityCoordinateMatrix (2 ^ 8) 4 =
      aesRationalCenteredActivityMatrix := by
  ext y x
  change ((if 5 ≤ activityWeight x + activityWeight y then
      ((2 ^ 8 : ℕ) : ℝ) ^ (activityWeight x + activityWeight y - 4)
    else 1) -
      (1 +
        ((((2 ^ 8 : ℕ) : ℝ) ^ activityWeight x - 1) *
          (((2 ^ 8 : ℕ) : ℝ) ^ activityWeight y - 1)) /
            (((2 ^ 8 : ℕ) : ℝ) ^ 4 - 1))) /
    Real.sqrt (((2 ^ 8 : ℕ) : ℝ) ^
      (activityWeight x + activityWeight y)) = _
  norm_num only [Nat.reducePow, Nat.cast_ofNat]
  rw [aesActivity_sqrt_card_pow]
  simp only [aesRationalCenteredActivityMatrix]
  norm_num

/-- The activity-basis Gram matrix for four AES bytes is the rational
Boolean-cube kernel at `1/16`. -/
theorem aesActivityGram_eq_rational :
    (activityBasisMatrix (A := AesByte) (n := 4))ᵀ *
        activityBasisMatrix (A := AesByte) (n := 4) =
      booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) := by
  rw [activityBasisMatrix_gram_eq_booleanKernel, aesByte_card]
  have hsqrt : Real.sqrt (256 : ℝ) = 16 := by
    rw [show (256 : ℝ) = (16 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  norm_num [hsqrt]

/-- A certificate for two rational quadratic forms suffices to bound the
canonical activity block. The forms use the rational Gram kernel and the
rational centered difference-distribution matrix. -/
theorem aesActivityCanonical_norm_le_of_posSemidef
    (u : AesByte) (hu : u ≠ 0)
    (hplus : Matrix.PosSemidef
      ((9566 / 100000000 : ℝ) •
        booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) +
        aesRationalCenteredActivityMatrix))
    (hminus : Matrix.PosSemidef
      ((9566 / 100000000 : ℝ) •
        booleanActivityGramKernel (n := 4) (1 / 16 : ℝ) -
        aesRationalCenteredActivityMatrix)) :
    ‖(activityGramInverseSquareRoot (n := 4) u hu)ᵀ *
        aesRationalCenteredActivityMatrix *
        activityGramInverseSquareRoot (n := 4) u hu‖ ≤
      (9566 / 100000000 : ℝ) := by
  apply matrix_twoNorm_le_of_gram_posSemidef_bounds
    (booleanActivityGramKernel (n := 4) (1 / 16 : ℝ))
    aesRationalCenteredActivityMatrix
    (activityGramInverseSquareRoot (n := 4) u hu)
    (9566 / 100000000 : ℝ) (by norm_num)
  · simpa only [← aesActivityGram_eq_rational] using
      activityGramInverseSquareRoot_orthonormal (n := 4) u hu
  · exact hplus
  · exact hminus

/-- A bound on the canonical 16×16 activity-coordinate matrix certifies the
first of the four displayed block estimates in Theorem 4 for the concrete
AES superbox. The premise is solely finite linear algebra. -/
theorem aesIndependentSuperbox_activityBlock_le_of_canonical_bound
    (u : AesByte) (hu : u ≠ 0)
    (hcertificate :
      ‖(activityGramInverseSquareRoot (n := 4) u hu)ᵀ *
          aesRationalCenteredActivityMatrix *
          activityGramInverseSquareRoot (n := 4) u hu‖ ≤
        (2 : ℝ) ^ (-(13.351 : ℝ))) :
    ‖activityTruncatedOperator
      (differenceDistributionMatrix
          (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) -
        uniformDifferenceDistributionMatrix (State AesByte 4))‖ ≤
      (2 : ℝ) ^ (-(13.351 : ℝ)) := by
  rw [aesIndependentSuperbox_activityTruncatedOperator_eq_mixColumn]
  rw [linear_centered_truncatedNorm_eq_canonical u hu
    aesMixColumnEquiv aesMixColumn_isMDS]
  rw [aesByte_card, aesCenteredActivityMatrix_eq_rational]
  exact hcertificate

end PairwiseIndependence
