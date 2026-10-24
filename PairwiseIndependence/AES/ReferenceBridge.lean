import PairwiseIndependence.AES.Reference
import PairwiseIndependence.AES.Instances

/-!
# AES reference implementation and the paper's concrete AES maps

The correspondence below holds for every state and every explicit round key.
The scheduled-key specialization is an implementation identity; it makes no
independent-key probability claim. The paper's four-round core stops after the
fourth SubBytes, so its final ShiftRows/MixColumns/AddRoundKey completion is
exposed separately.
-/

namespace PairwiseIndependence

/-- Decode the FIPS column-major byte sequence into the paper's coordinates. -/
def aesReferenceDecode (x : AesReferenceBlock) : AesByteState AesByte :=
  fun c r => aesByteFinEquiv (x (aesReferenceIndex c r))

theorem aesReferenceDecode_injective : Function.Injective aesReferenceDecode := by
  intro x y h
  apply aesReferenceBytes_ext
  intro i
  apply aesByteFinEquiv.injective
  have hi := congrArg (fun z => z (aesReferenceColumn i) (aesReferenceRow i)) h
  simpa only [aesReferenceDecode, aesReferenceIndex_column_row] using hi

theorem aesReferenceMixColumn_byte (x : AesReferenceWord) (r : Fin 4) :
    aesByteFinEquiv (aesReferenceMixColumn x r) =
      aesMixColumn (fun j => aesByteFinEquiv (x j)) r := by
  fin_cases r <;> simp [aesReferenceMixColumn, aesReferenceMul3, aesMixColumn,
    aesMul3, aesReferenceXor_byte, aesReferenceXtime_byte]

theorem aesReferenceInverseMixColumn_byte (x : AesReferenceWord) (r : Fin 4) :
    aesByteFinEquiv (aesReferenceInverseMixColumn x r) =
      aesInvMixColumn (fun j => aesByteFinEquiv (x j)) r := by
  fin_cases r <;> simp [aesReferenceInverseMixColumn, aesReferenceMul9,
    aesReferenceMul11, aesReferenceMul13, aesReferenceMul14, aesInvMixColumn,
    aesMul9, aesMul11, aesMul13, aesMul14, aesReferenceXor_byte, aesReferenceXtime_byte]

@[simp] theorem aesReferenceSubBytes_decode (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceSubBytes x) =
      aesCoordinateSubBytes aesSboxEquiv (aesReferenceDecode x) := by
  funext c r
  simp [aesReferenceDecode, aesReferenceSubBytes, aesReferenceSbox_byte,
    aesCoordinateSubBytes]

@[simp] theorem aesReferenceInverseSubBytes_decode (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceInverseSubBytes x) =
      (aesCoordinateSubBytes aesSboxEquiv).symm (aesReferenceDecode x) := by
  funext c r
  simp [aesReferenceDecode, aesReferenceInverseSubBytes, aesReferenceInverseSbox_byte,
    aesCoordinateSubBytes]

@[simp] theorem aesReferenceShiftRows_decode (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceShiftRows x) =
      aesCoordinateShiftRows (aesReferenceDecode x) := by
  funext c r
  simp [aesReferenceDecode, aesReferenceShiftRows, aesCoordinateShiftRows]

@[simp] theorem aesReferenceInverseShiftRows_decode (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceInverseShiftRows x) =
      aesCoordinateShiftRows.symm (aesReferenceDecode x) := by
  funext c r
  simp [aesReferenceDecode, aesReferenceInverseShiftRows, aesCoordinateShiftRows]

@[simp] theorem aesReferenceMixColumns_decode (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceMixColumns x) =
      aesCoordinateMixColumns aesMixColumnEquiv (aesReferenceDecode x) := by
  funext c r
  simp [aesReferenceDecode, aesReferenceMixColumns, aesReferenceMixColumn_byte,
    aesCoordinateMixColumns, aesMixColumnEquiv]
  rfl

@[simp] theorem aesReferenceInverseMixColumns_decode (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceInverseMixColumns x) =
      (aesCoordinateMixColumns aesMixColumnEquiv).symm (aesReferenceDecode x) := by
  funext c r
  simp [aesReferenceDecode, aesReferenceInverseMixColumns, aesReferenceInverseMixColumn_byte,
    aesCoordinateMixColumns, aesMixColumnEquiv]
  rfl

@[simp] theorem aesReferenceAddRoundKey_decode (x key : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceAddRoundKey x key) =
      aesReferenceDecode x + aesReferenceDecode key := by
  funext c r
  simp [aesReferenceDecode, aesReferenceAddRoundKey, aesReferenceXor_byte]

@[simp] theorem aesReferenceRound_decode (key x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceRound key x) =
      aesStyleRound (aesCoordinateSubBytes aesSboxEquiv) aesCoordinateShiftRows
        (aesCoordinateMixColumns aesMixColumnEquiv)
        (aesReferenceDecode key) (aesReferenceDecode x) := by
  simp [aesReferenceRound, aesStyleRound]

@[simp] theorem aesReferenceFinalRound_decode (key x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceFinalRound key x) =
      aesCoordinateShiftRows (aesCoordinateSubBytes aesSboxEquiv (aesReferenceDecode x)) +
        aesReferenceDecode key := by
  simp [aesReferenceFinalRound]

@[simp] theorem aesReferenceInverseSubBytes_subBytes (x : AesReferenceBlock) :
    aesReferenceInverseSubBytes (aesReferenceSubBytes x) = x := by
  apply aesReferenceDecode_injective
  simp

@[simp] theorem aesReferenceSubBytes_inverseSubBytes (x : AesReferenceBlock) :
    aesReferenceSubBytes (aesReferenceInverseSubBytes x) = x := by
  apply aesReferenceDecode_injective
  simp

@[simp] theorem aesReferenceInverseShiftRows_shiftRows (x : AesReferenceBlock) :
    aesReferenceInverseShiftRows (aesReferenceShiftRows x) = x := by
  apply aesReferenceDecode_injective
  simp

@[simp] theorem aesReferenceShiftRows_inverseShiftRows (x : AesReferenceBlock) :
    aesReferenceShiftRows (aesReferenceInverseShiftRows x) = x := by
  apply aesReferenceDecode_injective
  simp

@[simp] theorem aesReferenceInverseMixColumns_mixColumns (x : AesReferenceBlock) :
    aesReferenceInverseMixColumns (aesReferenceMixColumns x) = x := by
  apply aesReferenceDecode_injective
  simp

@[simp] theorem aesReferenceMixColumns_inverseMixColumns (x : AesReferenceBlock) :
    aesReferenceMixColumns (aesReferenceInverseMixColumns x) = x := by
  apply aesReferenceDecode_injective
  simp

@[simp] theorem aesReferenceAddRoundKey_twice (x key : AesReferenceBlock) :
    aesReferenceAddRoundKey (aesReferenceAddRoundKey x key) key = x := by
  apply aesReferenceDecode_injective
  simp only [aesReferenceAddRoundKey_decode]
  funext c r bit
  change (aesReferenceDecode x c r bit + aesReferenceDecode key c r bit) +
    aesReferenceDecode key c r bit = aesReferenceDecode x c r bit
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

@[simp] theorem aesReferenceInverseRound_round (key x : AesReferenceBlock) :
    aesReferenceInverseRound key (aesReferenceRound key x) = x := by
  simp [aesReferenceInverseRound, aesReferenceRound]

@[simp] theorem aesReferenceRound_inverseRound (key x : AesReferenceBlock) :
    aesReferenceRound key (aesReferenceInverseRound key x) = x := by
  simp [aesReferenceInverseRound, aesReferenceRound]

@[simp] theorem aesReferenceInverseFinalRound_finalRound (key x : AesReferenceBlock) :
    aesReferenceInverseFinalRound key (aesReferenceFinalRound key x) = x := by
  simp [aesReferenceInverseFinalRound, aesReferenceFinalRound]

@[simp] theorem aesReferenceFinalRound_inverseFinalRound (key x : AesReferenceBlock) :
    aesReferenceFinalRound key (aesReferenceInverseFinalRound key x) = x := by
  simp [aesReferenceInverseFinalRound, aesReferenceFinalRound]

@[simp] theorem aesReferenceInverseFullRounds_fullRounds (w : Array AesReferenceWord)
    (n : Nat) (x : AesReferenceBlock) :
    aesReferenceInverseFullRounds w n (aesReferenceFullRounds w n x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [aesReferenceFullRounds, aesReferenceInverseFullRounds, ih]

@[simp] theorem aesReferenceFullRounds_inverseFullRounds (w : Array AesReferenceWord)
    (n : Nat) (x : AesReferenceBlock) :
    aesReferenceFullRounds w n (aesReferenceInverseFullRounds w n x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [aesReferenceFullRounds, aesReferenceInverseFullRounds, ih]

/-- Encryption followed by decryption restores every block, for every key size and key. -/
theorem aesReferenceDecrypt_encrypt (v : AesReferenceVariant) (key : AesReferenceKey v)
    (x : AesReferenceBlock) :
    aesReferenceDecrypt v key (aesReferenceEncrypt v key x) = x := by
  simp [aesReferenceDecrypt, aesReferenceEncrypt]

theorem aesReferenceEncrypt_decrypt (v : AesReferenceVariant) (key : AesReferenceKey v)
    (x : AesReferenceBlock) :
    aesReferenceEncrypt v key (aesReferenceDecrypt v key x) = x := by
  simp [aesReferenceDecrypt, aesReferenceEncrypt]

/-- Iterate the existing coordinate rounds using the reference expanded key. -/
def aesCoordinateScheduledFullRounds (w : Array AesReferenceWord) :
    Nat → AesByteState AesByte → AesByteState AesByte
  | 0, x => x
  | n + 1, x => aesStyleRound (aesCoordinateSubBytes aesSboxEquiv) aesCoordinateShiftRows
      (aesCoordinateMixColumns aesMixColumnEquiv)
      (aesReferenceDecode (aesReferenceRoundKey w (n + 1)))
      (aesCoordinateScheduledFullRounds w n x)

theorem aesReferenceFullRounds_decode (w : Array AesReferenceWord) (n : Nat)
    (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceFullRounds w n x) =
      aesCoordinateScheduledFullRounds w n (aesReferenceDecode x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [aesReferenceFullRounds, aesCoordinateScheduledFullRounds, ih]

def aesCoordinateScheduledEncrypt (v : AesReferenceVariant) (key : AesReferenceKey v)
    (x : AesByteState AesByte) : AesByteState AesByte :=
  let w := aesReferenceExpandedKey v key
  aesCoordinateShiftRows (aesCoordinateSubBytes aesSboxEquiv
    (aesCoordinateScheduledFullRounds w (v.rounds - 1)
      (x + aesReferenceDecode (aesReferenceRoundKey w 0)))) +
    aesReferenceDecode (aesReferenceRoundKey w v.rounds)

/-- The entire scheduled cipher uses exactly the concrete maps in Theorem 5. -/
theorem aesReferenceEncrypt_decode (v : AesReferenceVariant) (key : AesReferenceKey v)
    (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceEncrypt v key x) =
      aesCoordinateScheduledEncrypt v key (aesReferenceDecode x) := by
  simp [aesReferenceEncrypt, aesCoordinateScheduledEncrypt, aesReferenceFullRounds_decode]

/-- Appendix B.1's core: three full rounds followed by the fourth SubBytes. -/
def aesReferencePaperCore (keys : AesReferenceBlock × AesReferenceBlock × AesReferenceBlock)
    (x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceSubBytes (aesReferenceRound keys.2.2
    (aesReferenceRound keys.2.1 (aesReferenceRound keys.1 x)))

theorem aesReferencePaperCore_decode
    (keys : AesReferenceBlock × AesReferenceBlock × AesReferenceBlock)
    (x : AesReferenceBlock) :
    aesReferenceDecode (aesReferencePaperCore keys x) =
      aesIndependentFourRoundCore
        (aesReferenceDecode keys.1, aesReferenceDecode keys.2.1, aesReferenceDecode keys.2.2)
        (aesReferenceDecode x) := by
  simp [aesReferencePaperCore, aesIndependentFourRoundCore,
    aesStyleFourRoundCore]

/-- Restore the fourth round's omitted linear layers and round key. -/
theorem aesReferenceFourRounds_decode (k₁ k₂ k₃ k₄ x : AesReferenceBlock) :
    aesReferenceDecode (aesReferenceRound k₄
      (aesReferenceRound k₃ (aesReferenceRound k₂ (aesReferenceRound k₁ x)))) =
      aesCoordinateMixColumns aesMixColumnEquiv (aesCoordinateShiftRows
        (aesIndependentFourRoundCore
          (aesReferenceDecode k₁, aesReferenceDecode k₂, aesReferenceDecode k₃)
          (aesReferenceDecode x))) + aesReferenceDecode k₄ := by
  simp [aesStyleRound, aesIndependentFourRoundCore,
    aesStyleFourRoundCore]

def aesReferenceScheduledPaperCore (v : AesReferenceVariant) (key : AesReferenceKey v)
    (x : AesReferenceBlock) : AesReferenceBlock :=
  let w := aesReferenceExpandedKey v key
  aesReferenceSubBytes (aesReferenceFullRounds w 3
    (aesReferenceAddRoundKey x (aesReferenceRoundKey w 0)))

/-- The paper's core instantiated with the first three scheduled round keys,
after the standardized initial AddRoundKey. This is an all-key equality. -/
theorem aesReferenceScheduledPaperCore_decode (v : AesReferenceVariant)
    (key : AesReferenceKey v) (x : AesReferenceBlock) :
    let w := aesReferenceExpandedKey v key
    aesReferenceDecode (aesReferenceScheduledPaperCore v key x) =
      aesIndependentFourRoundCore
        (aesReferenceDecode (aesReferenceRoundKey w 1),
         aesReferenceDecode (aesReferenceRoundKey w 2),
         aesReferenceDecode (aesReferenceRoundKey w 3))
        (aesReferenceDecode x + aesReferenceDecode (aesReferenceRoundKey w 0)) := by
  simp [aesReferenceScheduledPaperCore, aesReferenceFullRounds,
    aesIndependentFourRoundCore, aesStyleFourRoundCore]

end PairwiseIndependence
