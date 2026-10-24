import PairwiseIndependence.AES.Sbox
import PairwiseIndependence.AES.MDS

/-!
# The concrete AES maps used in the proofs

The bit-level S-box and MixColumns implementations substituted into the
round structure of `AES/Rounds.lean`. `AES/Equivalence.lean` proves that
these maps agree with the definitions in `AES/AES.lean`.
-/

namespace PairwiseIndependence

/-- The AES superbox on one column: SubBytes, MixColumns, AddRoundKey and
SubBytes. Theorem 4 bounds its key-averaged difference-distribution matrix. -/
def aesIndependentSuperbox (key : State AesByte 4) :
    State AesByte 4 ≃ State AesByte 4 :=
  aesCoordinateSuperbox aesSboxEquiv aesMixColumnEquiv key

/-- Three full AES rounds and the SubBytes layer of the fourth, with
independent round keys: the four-round core of Theorem 5 (Appendix B.1). -/
def aesIndependentFourRoundCore :
    AesByteState AesByte × AesByteState AesByte × AesByteState AesByte →
      AesByteState AesByte → AesByteState AesByte :=
  aesStyleFourRoundCore (aesCoordinateSubBytes aesSboxEquiv) aesCoordinateShiftRows
    (aesCoordinateMixColumns aesMixColumnEquiv)

/-- `4r + 4` AES rounds with independent round keys, the final round without
MixColumns as in FIPS 197: the family of Corollary 2. The first and last round
keys are the whitening keys that `IsPairwiseIndependent` adds. -/
def aesIndependentRounds (r : ℕ) :
    RepeatedBlockKeys
        (AesByteState AesByte × AesByteState AesByte × AesByteState AesByte)
        (AesByteState AesByte) r →
      AesByteState AesByte → AesByteState AesByte :=
  aesStyleRounds (aesCoordinateSubBytes aesSboxEquiv) aesCoordinateShiftRows
    (aesCoordinateMixColumns aesMixColumnEquiv) r

end PairwiseIndependence
