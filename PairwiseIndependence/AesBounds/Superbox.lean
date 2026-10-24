import PairwiseIndependence.AES.Instances
import PairwiseIndependence.Pairwise.KeyedShark

/-!
# The AES superbox as a SHARK construction

Reindexing the uniform middle key through MixColumns identifies the AES
superbox with the paper's two-round SHARK core. Its activity-space block
therefore depends only on MixColumns, as in Section 5 of the paper.
-/

namespace PairwiseIndependence

-- Stated for an arbitrary S-box: `simp` must not unfold the concrete table.
private theorem aesCoordinateSuperbox_eq_sharkTwoCore (s : AesByte ≃ AesByte)
    (key x : State AesByte 4) :
    aesCoordinateSuperbox s aesMixColumnEquiv key x =
      sharkTwoCore s aesMixColumnEquiv (aesMixColumnEquiv.symm key) x := by
  funext i
  change s (aesMixColumnEquiv (fun j => s (x j)) i + key i) =
    s (aesMixColumnEquiv ((fun j => s (x j)) + aesMixColumnEquiv.symm key) i)
  simp [map_add]

/-- The AES superbox and `Shark[4, 2^8, S, MixColumns]` have the same
key-averaged difference-distribution matrix. -/
theorem aesIndependentSuperbox_differenceDistributionMatrix_eq_sharkTwoCore :
    differenceDistributionMatrix
      (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) =
    differenceDistributionMatrix (sharkTwoCore aesSboxEquiv aesMixColumnEquiv) := by
  let e : State AesByte 4 ≃ State AesByte 4 := aesMixColumnEquiv.symm.toEquiv
  have hfun : (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) =
      fun key x => sharkTwoCore aesSboxEquiv aesMixColumnEquiv (e key) x :=
    funext fun key => funext fun x => aesCoordinateSuperbox_eq_sharkTwoCore aesSboxEquiv key x
  rw [hfun]
  exact differenceDistributionMatrix_key_reindex e _

/-- The activity-space block of the AES superbox is the MixColumns block,
independently of the S-box. -/
theorem aesIndependentSuperbox_activityTruncatedOperator_eq_mixColumn :
    activityTruncatedOperator
      (differenceDistributionMatrix
          (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) -
        uniformDifferenceDistributionMatrix (State AesByte 4)) =
    activityTruncatedOperator
      (deterministicDifferenceDistributionMatrix
          (fun x : State AesByte 4 => aesMixColumnEquiv x) -
        uniformDifferenceDistributionMatrix (State AesByte 4)) := by
  rw [aesIndependentSuperbox_differenceDistributionMatrix_eq_sharkTwoCore,
    sharkTwoCore_differenceDistributionMatrix_eq_keyed,
    keyedSharkTwoCore_truncatedOperator_eq_linear]

end PairwiseIndependence
