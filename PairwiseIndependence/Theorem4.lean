import PairwiseIndependence.Pairwise.Definitions
import PairwiseIndependence.AES.AES

/-!
# Theorem 4: the AES superbox

The difference-distribution matrix of the AES superbox (`AES.superbox`),
averaged over a uniform key, is within `2^(-10.146)` of the uniform matrix.
`‖·‖` on matrices is the Euclidean operator norm.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

/-- Theorem 4 of the paper (AES superbox). -/
def Theorem4 : Prop :=
  ‖differenceDistributionMatrix AES.superbox -
    uniformDifferenceDistributionMatrix AES.Column‖ ≤ (2 : ℝ) ^ (-(10.146 : ℝ))

end PairwiseIndependence
