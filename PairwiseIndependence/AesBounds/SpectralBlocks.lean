import PairwiseIndependence.Pairwise.SpectralWeightTwoBlocks
import PairwiseIndependence.AesBounds.SboxAffineBridge
import PairwiseIndependence.AesBounds.Superbox
import PairwiseIndependence.Pairwise.OneWordSpectralBias
import PairwiseIndependence.AesBounds.SpectralNumerics

/-!
# Theorem 4's three spectral blocks for the AES superbox

The superbox is the two-round SHARK construction with the AES S-box and
MixColumns, so Remark 1's refined `l=2` bounds apply. The S-box enters only
through its certified norm `σ ≤ 70315/10^6`.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

/-- The AES S-box as a family over a one-element key space. -/
abbrev aesSboxFamily : Unit → AesByte ≃ AesByte := fun _ => aesSboxEquiv

/-- The certified S-box norm is the spectral parameter of the SHARK proof. -/
theorem aesSbox_activityComplementOperator_norm_le :
    ‖keyedSboxActivityComplementOperator aesSboxFamily‖ ≤ 70315 / 1000000 := by
  rw [keyedSboxActivityComplementOperator_norm_eq_sub_uniform aesSboxFamily
    (by norm_num [aesByte_card])]
  exact aesSbox_differenceDistributionMatrix_norm_le

private theorem aesIndependentSuperbox_eq_keyedShark :
    differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) =
      differenceDistributionMatrix (keyedSharkTwoCore aesSboxFamily aesMixColumnEquiv) :=
  aesIndependentSuperbox_differenceDistributionMatrix_eq_sharkTwoCore.trans
    (sharkTwoCore_differenceDistributionMatrix_eq_keyed aesSboxEquiv aesMixColumnEquiv)

private theorem sqrt_card_aesByte : Real.sqrt (Fintype.card AesByte : ℝ) = 16 := by
  rw [aesByte_card]
  norm_num only [Nat.reducePow, Nat.cast_ofNat]
  rw [show (256 : ℝ) = (16 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Remark 1's coefficient for the blocks `V → V⊥` and `V⊥ → V` at `q = 2^8`,
`n = 4`. -/
private theorem aesMixed_coefficient :
    ((1 - (Real.sqrt (Fintype.card AesByte : ℝ))⁻¹) ^ (4 - 2))⁻¹ *
      ((Nat.choose 4 2 * Nat.choose 4 0 : ℕ) *
        ((Nat.choose (2 * 4 - 2) (4 - 1) : ℝ) * ((Fintype.card AesByte : ℝ)⁻¹) ^ (4 - 1) *
          ((Fintype.card AesByte : ℝ) - 2))) *
      ((1 - (Real.sqrt (Fintype.card AesByte : ℝ))⁻¹) ^ (4 - 0))⁻¹ =
      254 * 6 * 20 / 15 ^ 6 := by
  rw [sqrt_card_aesByte]
  norm_num [aesByte_card, Nat.choose]

/-- Remark 1's coefficient for the block `V⊥ → V⊥` at `q = 2^8`, `n = 4`. -/
private theorem aesComplement_coefficient :
    ((1 - (Real.sqrt (Fintype.card AesByte : ℝ))⁻¹) ^ (4 - 1))⁻¹ *
      ((Nat.choose 4 1 * Nat.choose 4 1 : ℕ) *
        ((Nat.choose (2 * 4 - 2) (4 - 1) : ℝ) * ((Fintype.card AesByte : ℝ)⁻¹) ^ (4 - 1) *
          ((Fintype.card AesByte : ℝ) - 2))) *
      ((1 - (Real.sqrt (Fintype.card AesByte : ℝ))⁻¹) ^ (4 - 1))⁻¹ =
      254 * 16 * 20 / 15 ^ 6 := by
  rw [sqrt_card_aesByte]
  norm_num [aesByte_card, Nat.choose]

private theorem aesByteOfNat_one_ne_zero : aesByteOfNat 1 ≠ (0 : AesByte) := by decide

theorem aesIndependentSuperbox_activityToComplement_sq_le_cyclic :
    ‖activityToComplementOperator
      (differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x))‖ ^ 2 ≤
      (70315 / 1000000 : ℝ) ^ 6 + 254 * 6 * 20 / 15 ^ 6 * (70315 / 1000000 : ℝ) ^ 4 := by
  rw [aesIndependentSuperbox_eq_keyedShark]
  refine (keyedSharkTwoCore_activityToComplement_sq_le_weightTwo (n := 4)
    (aesByteOfNat 1) aesByteOfNat_one_ne_zero aesSboxFamily aesMixColumnEquiv
    aesMixColumn_isMDS aesByte_card_ge_three (by omega)).trans ?_
  rw [aesMixed_coefficient]
  have h := aesSbox_activityComplementOperator_norm_le
  have h0 := norm_nonneg (keyedSboxActivityComplementOperator aesSboxFamily)
  have h6 := pow_le_pow_left₀ h0 h 6
  have h4 := pow_le_pow_left₀ h0 h 4
  linarith

theorem aesIndependentSuperbox_complementToActivity_sq_le_cyclic :
    ‖activityComplementToActivityOperator
      (differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x))‖ ^ 2 ≤
      (70315 / 1000000 : ℝ) ^ 6 + 254 * 6 * 20 / 15 ^ 6 * (70315 / 1000000 : ℝ) ^ 4 := by
  rw [aesIndependentSuperbox_eq_keyedShark]
  refine (keyedSharkTwoCore_activityComplementToActivity_sq_le_weightTwo (n := 4)
    (aesByteOfNat 1) aesByteOfNat_one_ne_zero aesSboxFamily aesMixColumnEquiv
    aesMixColumn_isMDS aesByte_card_ge_three (by omega)).trans ?_
  rw [aesMixed_coefficient]
  have h := aesSbox_activityComplementOperator_norm_le
  have h0 := norm_nonneg (keyedSboxActivityComplementOperator aesSboxFamily)
  have h6 := pow_le_pow_left₀ h0 h 6
  have h4 := pow_le_pow_left₀ h0 h 4
  linarith

theorem aesIndependentSuperbox_complementBlock_sq_le_cyclic :
    ‖activityComplementOperator
      (differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x))‖ ^ 2 ≤
      2 * (70315 / 1000000 : ℝ) ^ 6 + 254 * 16 * 20 / 15 ^ 6 * (70315 / 1000000 : ℝ) ^ 4 := by
  rw [aesIndependentSuperbox_eq_keyedShark]
  refine (keyedSharkTwoCore_activityComplement_sq_le_weightTwo (n := 4)
    (aesByteOfNat 1) aesByteOfNat_one_ne_zero aesSboxFamily aesMixColumnEquiv
    aesMixColumn_isMDS aesByte_card_ge_three (by omega)).trans ?_
  rw [aesComplement_coefficient]
  have h := aesSbox_activityComplementOperator_norm_le
  have h0 := norm_nonneg (keyedSboxActivityComplementOperator aesSboxFamily)
  have h6 := pow_le_pow_left₀ h0 h 6
  have h4 := pow_le_pow_left₀ h0 h 4
  linarith

/-- Theorem 4's bound on the block `V⊥ → V` of the AES superbox. -/
theorem theorem4_aesIndependentSuperbox_complementToActivityBlock :
    ‖activityComplementToActivityOperator
      (differenceDistributionMatrix
          (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) -
        uniformDifferenceDistributionMatrix (State AesByte 4))‖ ≤
      (2 : ℝ) ^ (-(11.178 : ℝ)) := by
  rw [activityComplementToActivityOperator_sub_uniform]
  let T := activityComplementToActivityOperator
    (differenceDistributionMatrix (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x))
  exact (sq_le_sq₀ (norm_nonneg T) (Real.rpow_nonneg (by norm_num) _)).mp
    (aesIndependentSuperbox_complementToActivity_sq_le_cyclic.trans
      aesMixedSpectralSquaredBound_cyclic_le_paper)

/-- Theorem 4's bound on the block `V → V⊥` of the AES superbox. -/
theorem theorem4_aesIndependentSuperbox_activityToComplementBlock :
    ‖activityToComplementOperator
      (differenceDistributionMatrix
          (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) -
        uniformDifferenceDistributionMatrix (State AesByte 4))‖ ≤
      (2 : ℝ) ^ (-(11.178 : ℝ)) := by
  rw [activityToComplementOperator_sub_uniform]
  let T := activityToComplementOperator
    (differenceDistributionMatrix (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x))
  exact (sq_le_sq₀ (norm_nonneg T) (Real.rpow_nonneg (by norm_num) _)).mp
    (aesIndependentSuperbox_activityToComplement_sq_le_cyclic.trans
      aesMixedSpectralSquaredBound_cyclic_le_paper)

/-- Theorem 4's bound on the block `V⊥ → V⊥` of the AES superbox. -/
theorem theorem4_aesIndependentSuperbox_complementBlock :
    ‖activityComplementOperator
      (differenceDistributionMatrix
          (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) -
        uniformDifferenceDistributionMatrix (State AesByte 4))‖ ≤
      (2 : ℝ) ^ (-(10.598 : ℝ)) := by
  rw [activityComplementOperator_sub_uniform]
  let T := activityComplementOperator
    (differenceDistributionMatrix (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x))
  exact (sq_le_sq₀ (norm_nonneg T) (Real.rpow_nonneg (by norm_num) _)).mp
    (aesIndependentSuperbox_complementBlock_sq_le_cyclic.trans
      aesComplementSpectralSquaredBound_cyclic_le_paper)

end PairwiseIndependence
