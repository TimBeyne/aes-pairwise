import PairwiseIndependence.AesBounds.SharkBridge
import PairwiseIndependence.AesBounds.Superbox
import PairwiseIndependence.KeliherSui.WideTrail
import PairwiseIndependence.AesBounds.SboxAffineBridge
import PairwiseIndependence.AesBounds.SboxCyclicIdentification
import PairwiseIndependence.KeliherSui.Witness

/-!
# Keliher--Sui differential estimate

Keliher and Sui give the exact maximum expected differential probability
`53 / 2^34` for two AES rounds. Their four-round consequence is the fourth
power of that value. `KeliherSui/WideTrail.lean` proves the abstract MDS
product-sum step toward that fourth power. This file states the resulting
bound for the independent-round-key AES core used here and checks the
numerical rounding in the main paper. The universal two-round upper bound
is proved separately in `KeliherSui/UpperBound.lean`. `KeliherSui/Witness.lean`
proves that a concrete superbox entry attains `53 / 2^34`, including the
matrix-to-256-trail reduction.

Source: L. Keliher and J. Sui, *Exact maximum expected differential and linear
probability for two-round Advanced Encryption Standard*, IET Information
Security 1(2), 2007, DOI: 10.1049/iet-ifs:20060161.
-/

namespace PairwiseIndependence

/-- Keliher--Sui's universal upper bound on the two-round maximum expected
differential probability, stated for the concrete four-byte AES superbox
used by Theorem 4. The matching lower bound is proved by
`keliherSui_twoRoundEstimate_attained`; the upper bound is proved by
`keliherSui_twoRound_upper_bound` in `KeliherSui/UpperBound.lean`. -/
def KeliherSuiTwoRoundEstimate : Prop :=
  ∀ u v : State AesByte 4, u ≠ 0 →
    differenceDistributionMatrix
      (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x)
        v u ≤ (53 : ℝ) / (2 : ℝ) ^ 34

/-- The cited Keliher--Sui four-round differential estimate, stated for the
exact concrete independent-round-key family of Theorem 5. This declaration
names an explicit proof obligation. -/
def KeliherSuiFourRoundEstimate : Prop :=
  ∀ a b : AesByteState AesByte, a ≠ 0 →
    differenceDistributionMatrix aesIndependentFourRoundCore b a ≤
      ((53 : ℝ) / (2 : ℝ) ^ 34) ^ 4

/-- The fourth-power step for any nonnegative two-round differential bound
on the independently keyed concrete AES superbox. -/
theorem aesIndependentTwoRoundBound_fourRound
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hTwo : ∀ u v : State AesByte 4, u ≠ 0 →
      differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x)
          v u ≤ μ) :
    ∀ a b : AesByteState AesByte, a ≠ 0 →
      differenceDistributionMatrix aesIndependentFourRoundCore b a ≤ μ ^ 4 := by
  classical
  intro a b ha
  let S := aesCoordinateSuperbox aesSboxEquiv aesMixColumnEquiv
  let L := aesStyleMiddleLinearLayer aesCoordinateShiftRows
    (aesCoordinateMixColumns aesMixColumnEquiv)
  have hword (u v : State AesByte 4) (h : u ≠ 0 ∨ v ≠ 0) :
      differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => S key x) v u ≤ μ := by
    by_cases hu : u = 0
    · rcases h with hu' | hv
      · exact (hu' hu).elim
      · rw [hu, differenceDistributionMatrix_zero_input]
        simp only [hv, ↓reduceIte]
        exact hμ
    · exact hTwo u v hu
  have hMDS : IsMDS L :=
    aesCoordinateMiddle_isMDS aesMixColumnEquiv aesMixColumn_isMDS
  have hshift : aesCoordinateShiftRows a ≠ 0 := by
    intro hs
    apply ha
    exact aesCoordinateShiftRows.injective (by simpa using hs)
  have hcore := keyedSharkTwoCore_differential_le_four
    S L hMDS μ hword (aesCoordinateShiftRows a) b hshift
  have hmatrix :=
    aesStyleFourRoundCore_differenceDistributionMatrix_eq_keyedShark_preShiftRows
      (aesCoordinateSubBytes aesSboxEquiv)
      aesCoordinateShiftRows
      (aesCoordinateMixColumns aesMixColumnEquiv)
      S
      (aesCoordinateShiftRows_subBytes_commute aesSboxEquiv)
      (aesCoordinateSuperbox_factorization aesSboxEquiv aesMixColumnEquiv)
  change differenceDistributionMatrix aesIndependentFourRoundCore b a ≤ μ ^ 4
  change differenceDistributionMatrix
    (aesStyleFourRoundCore
      (aesCoordinateSubBytes aesSboxEquiv)
      aesCoordinateShiftRows
      (aesCoordinateMixColumns aesMixColumnEquiv)) b a ≤ μ ^ 4
  rw [hmatrix]
  have hpre :
      differenceDistributionMatrix
        (fun key : AesByteState AesByte × AesByteState AesByte ×
            AesByteState AesByte =>
          fun x => keyedSharkTwoCore S L key (aesCoordinateShiftRows x)) b a =
      differenceDistributionMatrix (keyedSharkTwoCore S L) b
        (aesCoordinateShiftRows a) := by
    exact differenceDistributionMatrix_family_comp_addEquiv_apply
      (keyedSharkTwoCore S L) aesCoordinateShiftRows b a
  rw [hpre]
  exact hcore

/-- The fourth-power step of Keliher--Sui at their sharp two-round value.
It uses the MDS graph product theorem rather than enumerating the 128-bit
state space. -/
theorem KeliherSuiTwoRoundEstimate.fourRound
    (hTwo : KeliherSuiTwoRoundEstimate) :
    KeliherSuiFourRoundEstimate :=
  aesIndependentTwoRoundBound_fourRound
    ((53 : ℝ) / (2 : ℝ) ^ 34) (by positivity) hTwo

/-- The numerical rounding of Keliher--Sui's four-superbox bound used in
Corollary 2. -/
theorem keliherSui_fourSuperboxBound_le_paper :
    ((53 : ℝ) / (2 : ℝ) ^ 34) ^ 4 ≤ 1 / (2 : ℝ) ^ 113 := by
  norm_num

/-- The cited estimate implies the rounded differential bound used by the
paper's Lemma 6. -/
theorem KeliherSuiFourRoundEstimate.le_paper
    (h : KeliherSuiFourRoundEstimate)
    (a b : AesByteState AesByte) (ha : a ≠ 0) :
    differenceDistributionMatrix aesIndependentFourRoundCore b a ≤
      1 / (2 : ℝ) ^ 113 :=
  (h a b ha).trans keliherSui_fourSuperboxBound_le_paper

end PairwiseIndependence
