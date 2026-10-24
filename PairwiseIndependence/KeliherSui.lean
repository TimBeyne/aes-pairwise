import PairwiseIndependence.Pairwise.Definitions
import PairwiseIndependence.AES.AES

/-!
# The Keliher–Sui bound

The maximal key-averaged probability of a differential with nonzero input over
the AES superbox is `53 / 2^34`. The paper cites this bound (Section 4.3); its
proof is in `KeliherSui/`.
-/

namespace PairwiseIndependence

/-- The Keliher–Sui bound: `53 / 2^34` bounds every differential with nonzero
input over the AES superbox, and some differential attains it. -/
def KeliherSuiBound : Prop :=
  (∀ u v : AES.Column, u ≠ 0 →
    differenceDistributionMatrix AES.superbox v u ≤ (53 : ℝ) / (2 : ℝ) ^ 34) ∧
  ∃ u v : AES.Column, u ≠ 0 ∧
    differenceDistributionMatrix AES.superbox v u = (53 : ℝ) / (2 : ℝ) ^ 34

end PairwiseIndependence
