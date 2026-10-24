import PairwiseIndependence.AES.AES
import PairwiseIndependence.AES.Coordinates

/-!
# Concrete AES byte arithmetic and MixColumns

The bit coordinates are little-endian. Addition is bytewise XOR. The
`aesXtime` formula uses the AES reduction polynomial and `aesMixColumn` uses
the coefficients of FIPS 197, Section 5.1.3. The explicit inverse in Section
5.3.3 certifies that this concrete MixColumns map is an additive equivalence.
Its MDS branch-number property is proved in `AES/MDS.lean`.
-/

namespace PairwiseIndependence

theorem aesByte_card : Fintype.card AesByte = 2 ^ 8 := by
  simp [AesByte]

/-- Multiplication by `x` modulo the AES polynomial
`x⁸ + x⁴ + x³ + x + 1`, in little-endian bit coordinates. -/
def aesXtime (x : AesByte) : AesByte :=
  ![x 7, x 0 + x 7, x 1, x 2 + x 7,
    x 3 + x 7, x 4, x 5, x 6]

theorem aesXtime_add (x y : AesByte) :
    aesXtime (x + y) = aesXtime x + aesXtime y := by
  funext i
  fin_cases i <;> simp [aesXtime, Pi.add_apply, add_assoc, add_left_comm, add_comm]

def aesXtimeHom : AesByte →+ AesByte where
  toFun := aesXtime
  map_zero' := by funext i; fin_cases i <;> simp [aesXtime]
  map_add' := aesXtime_add

/-- Multiplication by 03 in the AES byte field. -/
def aesMul3 (x : AesByte) : AesByte := aesXtime x + x

/-- The standardized AES MixColumns transformation on one column. -/
def aesMixColumn (x : State AesByte 4) : State AesByte 4 :=
  ![aesXtime (x 0) + aesMul3 (x 1) + x 2 + x 3,
    x 0 + aesXtime (x 1) + aesMul3 (x 2) + x 3,
    x 0 + x 1 + aesXtime (x 2) + aesMul3 (x 3),
    aesMul3 (x 0) + x 1 + x 2 + aesXtime (x 3)]

theorem aesMixColumn_add (x y : State AesByte 4) :
    aesMixColumn (x + y) = aesMixColumn x + aesMixColumn y := by
  funext i
  fin_cases i <;> simp [aesMixColumn, aesMul3, aesXtime_add, Pi.add_apply] <;> abel

def aesMul9 (x : AesByte) : AesByte :=
  aesXtime (aesXtime (aesXtime x)) + x

def aesMul11 (x : AesByte) : AesByte :=
  aesXtime (aesXtime (aesXtime x)) + aesXtime x + x

def aesMul13 (x : AesByte) : AesByte :=
  aesXtime (aesXtime (aesXtime x)) + aesXtime (aesXtime x) + x

def aesMul14 (x : AesByte) : AesByte :=
  aesXtime (aesXtime (aesXtime x)) + aesXtime (aesXtime x) + aesXtime x

/-- The FIPS 197 inverse MixColumns matrix, used to certify bijectivity. -/
def aesInvMixColumn (x : State AesByte 4) : State AesByte 4 :=
  ![aesMul14 (x 0) + aesMul11 (x 1) + aesMul13 (x 2) + aesMul9 (x 3),
    aesMul9 (x 0) + aesMul14 (x 1) + aesMul11 (x 2) + aesMul13 (x 3),
    aesMul13 (x 0) + aesMul9 (x 1) + aesMul14 (x 2) + aesMul11 (x 3),
    aesMul11 (x 0) + aesMul13 (x 1) + aesMul9 (x 2) + aesMul14 (x 3)]

private theorem aesByte_two_eq_zero : (2 : AesByte) = 0 := by
  funext i
  change (2 : ZMod 2) = 0
  decide

private theorem aesByte_three_eq_one : (3 : AesByte) = 1 := by
  funext i
  change (3 : ZMod 2) = 1
  decide

private theorem aesByte_four_eq_zero : (4 : AesByte) = 0 := by
  funext i
  change (4 : ZMod 2) = 0
  decide

theorem aesInvMixColumn_mix (x : State AesByte 4) :
    aesInvMixColumn (aesMixColumn x) = x := by
  funext i
  fin_cases i <;>
    simp [aesInvMixColumn, aesMixColumn, aesMul14, aesMul13,
      aesMul11, aesMul9, aesMul3, aesXtime_add] <;>
    ring_nf <;> simp [aesByte_two_eq_zero, aesByte_three_eq_one,
      aesByte_four_eq_zero]

theorem aesMixColumn_invMix (x : State AesByte 4) :
    aesMixColumn (aesInvMixColumn x) = x := by
  funext i
  fin_cases i <;>
    simp [aesInvMixColumn, aesMixColumn, aesMul14, aesMul13,
      aesMul11, aesMul9, aesMul3, aesXtime_add] <;>
    ring_nf <;> simp [aesByte_two_eq_zero, aesByte_three_eq_one,
      aesByte_four_eq_zero]

def aesMixColumnEquiv : State AesByte 4 ≃+ State AesByte 4 where
  toFun := aesMixColumn
  invFun := aesInvMixColumn
  left_inv := aesInvMixColumn_mix
  right_inv := aesMixColumn_invMix
  map_add' := aesMixColumn_add

/-- FIPS 197, Section 4.2, example: `02 · 57 = ae`. -/
theorem aesXtime_fipsExample :
    aesXtime (aesByteOfNat 0x57) = aesByteOfNat 0xae := by
  funext i
  fin_cases i <;> decide

/-- FIPS 197, Appendix B, first-round MixColumns first column. -/
theorem aesMixColumn_fipsExample :
    aesMixColumn ![aesByteOfNat 0xd4, aesByteOfNat 0xbf,
      aesByteOfNat 0x5d, aesByteOfNat 0x30] =
    ![aesByteOfNat 0x04, aesByteOfNat 0x66,
      aesByteOfNat 0x81, aesByteOfNat 0xe5] := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The AES `03` multiplier has no nonzero kernel element. This finite
certificate checks all 256 byte values in the explicit bit representation. -/
theorem aesMul3_kernel_trivial :
    ∀ x : AesByte, aesMul3 x = 0 → x = 0 := by
  set_option maxRecDepth 4096 in
    decide

theorem aesMul3_add (x y : AesByte) :
    aesMul3 (x + y) = aesMul3 x + aesMul3 y := by
  simp [aesMul3, aesXtime_add]
  abel

end PairwiseIndependence
