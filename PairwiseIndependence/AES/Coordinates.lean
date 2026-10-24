import PairwiseIndependence.AES.Rounds

/-!
# AES-style 4×4 byte coordinates

States are indexed by column, then row. The generic byte permutation and
columnwise additive equivalence give coordinatewise SubBytes and MixColumns;
ShiftRows rotates row `r` by `r` columns. This module proves the superbox
factorization, SubBytes/ShiftRows commutation, and the lift from byte-level
MixColumns MDS to MDS on four 32-bit words. Concrete AES byte arithmetic and
MixColumns coefficients are in `AES/Byte.lean`, and the concrete S-box is in
`AES/Sbox.lean`.
-/

namespace PairwiseIndependence

variable {B : Type*} [AddCommGroup B]

/-- AES state coordinates: outer index is the column, inner index the row. -/
abbrev AesByteState (B : Type*) := State (State B 4) 4

/-- SubBytes applies the same byte permutation to all 16 positions. -/
def aesCoordinateSubBytes (s : B ≃ B) :
    AesByteState B ≃ AesByteState B where
  toFun x := fun c r => s (x c r)
  invFun x := fun c r => s.symm (x c r)
  left_inv := by intro x; funext c r; simp
  right_inv := by intro x; funext c r; simp

/-- ShiftRows rotates row `r` to the left by `r` columns. -/
def aesCoordinateShiftRows :
    AesByteState B ≃+ AesByteState B where
  toFun x := fun c r => x (c + r) r
  invFun x := fun c r => x (c - r) r
  left_inv := by intro x; funext c r; simp
  right_inv := by intro x; funext c r; simp
  map_add' := by intro x y; funext c r; rfl

/-- MixColumns applies a byte-column linear equivalence independently. -/
def aesCoordinateMixColumns (m : State B 4 ≃+ State B 4) :
    AesByteState B ≃+ AesByteState B where
  toFun x := fun c => m (x c)
  invFun x := fun c => m.symm (x c)
  left_inv := by intro x; funext c r; simp
  right_inv := by intro x; funext c r; simp
  map_add' := by intro x y; funext c r; simp

/-- A single independently keyed 4-byte superbox. -/
def aesCoordinateSuperbox (s : B ≃ B)
    (m : State B 4 ≃+ State B 4) (key : State B 4) :
    State B 4 ≃ State B 4 where
  toFun x := fun r => s (m (fun i => s (x i)) r + key r)
  invFun y := fun r => s.symm
    ((m.symm (fun i => s.symm (y i) - key i)) r)
  left_inv := by intro x; funext r; simp
  right_inv := by intro y; funext r; simp

theorem aesCoordinateShiftRows_subBytes_commute (s : B ≃ B)
    (x : AesByteState B) :
    aesCoordinateShiftRows (aesCoordinateSubBytes s x) =
      aesCoordinateSubBytes s (aesCoordinateShiftRows x) := by
  rfl

theorem aesCoordinateSuperbox_factorization (s : B ≃ B)
    (m : State B 4 ≃+ State B 4)
    (key x : AesByteState B) :
    aesStyleSuperbox (aesCoordinateSubBytes s)
      (aesCoordinateMixColumns m) key x =
    keyedSubstitute (aesCoordinateSuperbox s m) key x := by
  rfl

variable [DecidableEq B]

/-- In one intermediate column, ShiftRows can have no more active bytes than
the original state has active columns. -/
theorem aesCoordinateShiftRows_column_activity_le
    (x : AesByteState B) (c : Fin 4) :
    activeCoordinates (aesCoordinateShiftRows x c) ≤ activeCoordinates x := by
  classical
  unfold activeCoordinates
  apply Finset.card_le_card_of_injOn (fun r : Fin 4 => c + r)
  · intro r hr
    have hr' : aesCoordinateShiftRows x c r ≠ 0 := by simpa using hr
    have h : x (c + r) ≠ 0 := by
      intro hzero
      apply hr'
      exact congrArg (fun w : State B 4 => w r) hzero
    simpa using h
  · intro r _ s _ hrs
    exact add_left_cancel hrs

/-- Each active output byte of one intermediate MixColumns column reaches a
different final output word under ShiftRows. -/
theorem aesCoordinateShiftRows_outputColumn_activity_le
    (x : AesByteState B) (c : Fin 4) :
    activeCoordinates (x c) ≤ activeCoordinates (aesCoordinateShiftRows x) := by
  classical
  unfold activeCoordinates
  apply Finset.card_le_card_of_injOn (fun r : Fin 4 => c - r)
  · intro r hr
    have hr' : x c r ≠ 0 := by simpa using hr
    have h : aesCoordinateShiftRows x (c - r) ≠ 0 := by
      intro hzero
      apply hr'
      have hy := congrArg (fun w : State B 4 => w r) hzero
      simpa [aesCoordinateShiftRows] using hy
    simpa using h
  · intro r _ s _ hrs
    have h := congrArg (fun z : Fin 4 => c - z) hrs
    simpa using h

/-- Byte-level MDS of MixColumns implies word-level MDS of the middle layer
in Appendix B.1. -/
theorem aesCoordinateMiddle_isMDS
    (m : State B 4 ≃+ State B 4)
    (hm : IsMDS m) :
    IsMDS
      (aesStyleMiddleLinearLayer aesCoordinateShiftRows
        (aesCoordinateMixColumns m)) := by
  classical
  intro x hx
  let z := aesCoordinateShiftRows x
  let w := aesCoordinateMixColumns m z
  let y := aesCoordinateShiftRows w
  change 4 + 1 ≤ activeCoordinates x + activeCoordinates y
  by_contra hsmall
  have hsum : activeCoordinates x + activeCoordinates y ≤ 4 := by omega
  have hz (c : Fin 4) : z c = 0 := by
    by_contra hnonzero
    have hmds := hm (z c) hnonzero
    have hin : activeCoordinates (z c) ≤ activeCoordinates x :=
      aesCoordinateShiftRows_column_activity_le x c
    have hout : activeCoordinates (m (z c)) ≤ activeCoordinates y := by
      simpa only [w, aesCoordinateMixColumns] using
        aesCoordinateShiftRows_outputColumn_activity_le w c
    omega
  have hzall : z = 0 := by funext c; exact hz c
  have hxzero : x = 0 := aesCoordinateShiftRows.injective (by simpa [z] using hzall)
  exact hx hxzero

end PairwiseIndependence
