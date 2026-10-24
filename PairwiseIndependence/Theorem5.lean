import PairwiseIndependence.Pairwise.Definitions
import PairwiseIndependence.AES.AES

/-!
# Theorem 5: four rounds of AES

The difference-distribution matrix of four AES rounds (`AES.rounds 4`), averaged
over independent uniform round keys, is within `2^(-39)` of the uniform matrix.
`‖·‖` on matrices is the Euclidean operator norm.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

/-- Theorem 5 of the paper (AES, four rounds). -/
def Theorem5 : Prop :=
  ‖differenceDistributionMatrix (AES.rounds 4) -
    uniformDifferenceDistributionMatrix AES.State‖ ≤ 1 / (2 : ℝ) ^ 39

end PairwiseIndependence
