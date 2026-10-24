import PairwiseIndependence.Pairwise.Definitions
import PairwiseIndependence.AES.AES

/-!
# Corollary 2: pairwise independence of `4r + 4` AES rounds

`4r + 4` rounds of AES with independent uniform round keys (`AES.cipher r`,
with the first and last round keys as the whitening keys of
`IsPairwiseIndependent`) are `2^14 · 2^(-39r)`-pairwise independent.
-/

namespace PairwiseIndependence

/-- Corollary 2 of the paper. -/
def Corollary2 : Prop :=
  ∀ r : ℕ, IsPairwiseIndependent (AES.cipher r) ((2 : ℝ) ^ 14 * (1 / (2 : ℝ) ^ 39) ^ r)

end PairwiseIndependence
