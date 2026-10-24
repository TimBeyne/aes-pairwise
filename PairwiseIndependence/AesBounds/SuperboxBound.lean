import PairwiseIndependence.AesBounds.ActivityFiniteCertificate
import PairwiseIndependence.AesBounds.SpectralBlocks
import PairwiseIndependence.AesBounds.Theorem4Assembly
import PairwiseIndependence.Theorem4
import PairwiseIndependence.AES.Equivalence

/-!
# Theorem 4 for the implementation's superbox

The key-averaged difference-distribution matrix `D` of the superbox satisfies
`‖D − U‖₂ ≤ 2^(-10.146)`. `Theorem4.lean` restates this for the definitions in
`AES/AES.lean`. The four blocks of `D − U` with respect to
`V ⊕ V⊥` are bounded in `AesBounds/ActivityFiniteCertificate.lean` (the
truncated-differential block, Section 5) and `AesBounds/SpectralBlocks.lean`
(the three spectral blocks, Section 6).
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

/-- Theorem 4 for `aesIndependentSuperbox`. -/
theorem theorem4_aesIndependentSuperbox :
    ‖differenceDistributionMatrix
        (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x) -
      uniformDifferenceDistributionMatrix (State AesByte 4)‖ ≤
        (2 : ℝ) ^ (-(10.146 : ℝ)) :=
  theorem4_superbox_of_paper_block_bounds aesByte_card _
    theorem4_aesIndependentSuperbox_activityBlock
    theorem4_aesIndependentSuperbox_complementToActivityBlock
    theorem4_aesIndependentSuperbox_activityToComplementBlock
    theorem4_aesIndependentSuperbox_complementBlock

/-- Theorem 4 of the paper; the statement is in `Theorem4.lean`. -/
theorem theorem4_aesSuperbox : Theorem4 := by
  unfold Theorem4
  rw [show AES.superbox = fun k c => aesIndependentSuperbox k c from
    funext₂ AES.superbox_eq]
  exact theorem4_aesIndependentSuperbox

end PairwiseIndependence
