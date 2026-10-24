import PairwiseIndependence.AES.Sbox

/-!
# AES inverse-table field certificate

This finite check is separate from the S-box permutation proof so Lean can
compile it within the project's memory cap. It verifies the inverse table
against the AES polynomial-basis multiplication, rather than treating the
table entries as a trusted definition of field inversion.
-/

namespace PairwiseIndependence

set_option maxHeartbeats 20000000

/-- Every nonzero inverse-table entry multiplies its input to the field unit. -/
theorem aesFieldInverse_mul (x : AesByte) (hx : x ≠ 0) :
    aesByteMul x (aesFieldInverse x) = aesByteOfNat 1 := by
  have h : ∀ x : AesByte, x ≠ 0 →
      aesByteMul x (aesFieldInverse x) = aesByteOfNat 1 := by
    set_option maxRecDepth 8192 in decide
  exact h x hx

end PairwiseIndependence
