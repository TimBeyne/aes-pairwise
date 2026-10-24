import PairwiseIndependence.AesBounds.SuperboxBound
import PairwiseIndependence.Pairwise.SharkBound
import PairwiseIndependence.AesBounds.Theorem4Assembly
import PairwiseIndependence.AesBounds.SharkBridge
import PairwiseIndependence.Theorem5
import PairwiseIndependence.AES.Equivalence
import PairwiseIndependence.Pairwise.IteratedBlocks

/-!
# From Theorem 4 to Theorem 5

After the Appendix B.1 rearrangement, four AES-style rounds are the keyed
two-round SHARK core on four 32-bit words. Theorem 3 with `q = 2^32`, `n = 4`
and `l = 3` then turns the superbox bound `2^(-10.146)` into `2^(-39)`.
-/

namespace PairwiseIndependence
open scoped Matrix.Norms.L2Operator

/-- Theorem 5 for the generic AES-style four-round map, conditional on its
column superbox factorization, the MDS middle layer, and the paper's superbox
norm bound. The exact all-key rearrangement and ShiftRows norm invariance are
proved in `AesBounds/SharkBridge.lean`. -/
theorem theorem5_aesStyleFourRoundCore_of_superbox_bound
    {W : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    (hcard : Fintype.card W = 2 ^ 32)
    (subBytes : State W 4 ≃ State W 4)
    (shiftRows mixColumns : State W 4 ≃+ State W 4)
    (S : W → W ≃ W)
    (hcomm : ∀ x : State W 4,
      shiftRows (subBytes x) = subBytes (shiftRows x))
    (hSuperbox : ∀ key x : State W 4,
      aesStyleSuperbox subBytes mixColumns key x = keyedSubstitute S key x)
    (hMDS : IsMDS (aesStyleMiddleLinearLayer shiftRows mixColumns))
    (hsuperbox :
      ‖differenceDistributionMatrix (fun key : W => fun x : W => S key x) -
        uniformDifferenceDistributionMatrix W‖ ≤
          (2 : ℝ) ^ (-(10.146 : ℝ))) :
    ‖differenceDistributionMatrix
        (aesStyleFourRoundCore subBytes shiftRows mixColumns) -
      uniformDifferenceDistributionMatrix (State W 4)‖ ≤
        1 / (2 : ℝ) ^ 39 := by
  rw [aesStyleFourRoundCore_spectralBias_eq_keyedShark
    subBytes shiftRows mixColumns S hcomm hSuperbox]
  exact theorem5_keyedShark_of_paper_differenceDistributionMatrix_bound
    hcard S (aesStyleMiddleLinearLayer shiftRows mixColumns) hMDS hsuperbox

/-- Theorem 5 for the implementation's four-round core. -/
theorem theorem5_aesIndependentRoundKeys :
    ‖differenceDistributionMatrix aesIndependentFourRoundCore -
      uniformDifferenceDistributionMatrix (AesByteState AesByte)‖ ≤
        1 / (2 : ℝ) ^ 39 :=
  theorem5_aesStyleFourRoundCore_of_superbox_bound (by simp [State])
    (aesCoordinateSubBytes aesSboxEquiv) aesCoordinateShiftRows
    (aesCoordinateMixColumns aesMixColumnEquiv)
    (aesCoordinateSuperbox aesSboxEquiv aesMixColumnEquiv)
    (aesCoordinateShiftRows_subBytes_commute aesSboxEquiv)
    (aesCoordinateSuperbox_factorization aesSboxEquiv aesMixColumnEquiv)
    (aesCoordinateMiddle_isMDS aesMixColumnEquiv aesMixColumn_isMDS)
    theorem4_aesIndependentSuperbox

/-- Theorem 5 of the paper; the statement is in `Theorem5.lean`. Four rounds
are the four-round core followed by ShiftRows, MixColumns and a round key, none
of which changes `‖D − U‖`. -/
theorem theorem5_aesFourRounds : Theorem5 := by
  unfold Theorem5
  let L := aesCoordinateShiftRows.trans (aesCoordinateMixColumns aesMixColumnEquiv)
  letI : Fintype ((AES.State × AES.State × AES.State) × AES.State) := instFintypeProd _ _
  rw [show AES.rounds 4 = fun k => (fun p : (AES.State × AES.State × AES.State) × AES.State =>
      fun s => L (aesIndependentFourRoundCore p.1 s) + p.2) (AES.fourRoundKeys k) from
    funext₂ AES.rounds_four,
    differenceDistributionMatrix_key_reindex AES.fourRoundKeys
      (fun p s => L (aesIndependentFourRoundCore p.1 s) + p.2),
    differenceDistributionMatrix_add_key (fun p s => L (aesIndependentFourRoundCore p s)),
    differenceDistributionMatrix_addEquiv_comp_spectralBias_eq]
  exact theorem5_aesIndependentRoundKeys

end PairwiseIndependence
