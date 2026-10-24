import PairwiseIndependence.AES.Sbox

/-!
# Numeric byte encoding

The bijection between `Fin 256` and the bit representation `AesByte`, used by
the lookup tables of the reference implementation and the finite certificates.
-/

namespace PairwiseIndependence

/-- Numeric XOR of bytes is addition in the concrete Lean byte group. -/
theorem aesByteOfNat_xor (x y : Fin 256) :
    aesByteOfNat (Nat.xor x.val y.val) =
      aesByteOfNat x.val + aesByteOfNat y.val := by
  have h : ∀ x y : Fin 256,
      aesByteOfNat (Nat.xor x.val y.val) =
        aesByteOfNat x.val + aesByteOfNat y.val := by
    native_decide
  exact h x y

/-- The numeric byte encoding enumerates every concrete AES byte once. -/
theorem aesByteOfNat_toNat (x : AesByte) :
    aesByteOfNat (aesByteToNat x) = x := by
  have h : ∀ x : AesByte, aesByteOfNat (aesByteToNat x) = x := by
    native_decide
  exact h x

theorem aesByteToNat_ofNat (x : Fin 256) :
    aesByteToNat (aesByteOfNat x.val) = x.val := by
  have h : ∀ x : Fin 256,
      aesByteToNat (aesByteOfNat x.val) = x.val := by
    native_decide
  exact h x

theorem aesByteToNat_lt (x : AesByte) : aesByteToNat x < 256 := by
  have h : ∀ x : AesByte, aesByteToNat x < 256 := by native_decide
  exact h x

/-- The numeric encoding used by the finite certificate is an exact
enumeration of the concrete Lean AES byte type. -/
def aesByteFinEquiv : Fin 256 ≃ AesByte where
  toFun x := aesByteOfNat x.val
  invFun x := ⟨aesByteToNat x, aesByteToNat_lt x⟩
  left_inv x := Fin.ext (aesByteToNat_ofNat x)
  right_inv := aesByteOfNat_toNat

end PairwiseIndependence
