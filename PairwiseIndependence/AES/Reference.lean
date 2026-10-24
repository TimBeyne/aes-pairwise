import PairwiseIndependence.AES.ByteEncoding
import Mathlib.Data.Nat.Bitwise

/-!
# Scheduled-key AES reference implementation

FIPS 197, Sections 3.4, 5.1, 5.2 and 5.3. Numeric bytes are in `Fin 256`;
blocks are 16 bytes in the standard column-major order `4 * column + row`.
The implementation covers AES-128, AES-192 and AES-256. The final encryption
round omits MixColumns. Decryption regroups the inverse transformations as
the inverse of the final round, followed by inverses of the full rounds.

Intermediate bytes are materialized in arrays, avoiding repeated evaluation
of nested state functions. `AES/ReferenceBridge.lean` connects every round to
the existing concrete AES maps. Published vectors are theorems in
`AES/ReferenceVectors.lean`.

Source: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
-/

namespace PairwiseIndependence

inductive AesReferenceVariant where
  | aes128 | aes192 | aes256
  deriving DecidableEq, Repr

def AesReferenceVariant.keyWords : AesReferenceVariant → Nat
  | .aes128 => 4 | .aes192 => 6 | .aes256 => 8

def AesReferenceVariant.rounds : AesReferenceVariant → Nat
  | .aes128 => 10 | .aes192 => 12 | .aes256 => 14

abbrev AesReferenceWord := Vector (Fin 256) 4
abbrev AesReferenceBlock := Vector (Fin 256) 16
abbrev AesReferenceKey (v : AesReferenceVariant) := Vector (Fin 256) (4 * v.keyWords)

instance aesReferenceVectorCoeFun {n : Nat} :
    CoeFun (Vector (Fin 256) n) (fun _ => Fin n → Fin 256) where
  coe x := fun i => x[i.val]

/-- Store bytes eagerly; the mathematical function is unchanged. -/
def aesReferenceMaterialize {n : Nat} (x : Fin n → Fin 256) : Vector (Fin 256) n :=
  Vector.ofFn x

@[simp] theorem aesReferenceMaterialize_apply {n : Nat}
    (x : Fin n → Fin 256) (i : Fin n) : aesReferenceMaterialize x i = x i := by
  simp [aesReferenceMaterialize]

@[simp] theorem aesReferenceMaterialize_getElem {n : Nat}
    (x : Fin n → Fin 256) (i : Nat) (hi : i < n) :
    (aesReferenceMaterialize x)[i] = x ⟨i, hi⟩ := by
  simp [aesReferenceMaterialize]

theorem aesReferenceBytes_ext {n : Nat} {x y : Vector (Fin 256) n}
    (h : ∀ i : Fin n, x i = y i) : x = y := by
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

def aesReferenceXor (a b : Fin 256) : Fin 256 :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt⟩

theorem aesReferenceXor_byte (a b : Fin 256) :
    aesByteFinEquiv (aesReferenceXor a b) = aesByteFinEquiv a + aesByteFinEquiv b :=
  aesByteOfNat_xor a b

def aesReferenceXtime (a : Fin 256) : Fin 256 :=
  ⟨(if a.val < 128 then 2 * a.val else (2 * a.val - 256) ^^^ 0x1b) % 256,
    Nat.mod_lt _ (by omega)⟩

theorem aesReferenceXtime_byte : ∀ a : Fin 256,
    aesByteFinEquiv (aesReferenceXtime a) = aesXtime (aesByteFinEquiv a) := by
  native_decide

/-- FIPS 197 Table 4, indexed by the ordinary hexadecimal byte value. -/
def aesReferenceSboxTable : Array (Fin 256) := #[
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

def aesReferenceSbox (a : Fin 256) : Fin 256 := aesReferenceSboxTable[a.val]!

theorem aesReferenceSbox_byte : ∀ a : Fin 256,
    aesByteFinEquiv (aesReferenceSbox a) = aesSboxEquiv (aesByteFinEquiv a) := by
  native_decide

/-- Derive the inverse lookup from the forward table, without a second
independent transcription. Its connection to the inverse AES map is checked. -/
def aesReferenceInverseSboxTable : Array (Fin 256) :=
  Array.ofFn (fun b : Fin 256 =>
    ((List.finRange 256).find? (fun a => aesReferenceSbox a = b)).getD 0)

def aesReferenceInverseSbox (a : Fin 256) : Fin 256 :=
  aesReferenceInverseSboxTable[a.val]!

theorem aesReferenceInverseSbox_byte : ∀ a : Fin 256,
    aesByteFinEquiv (aesReferenceInverseSbox a) = aesSboxEquiv.symm (aesByteFinEquiv a) := by
  native_decide

def aesReferenceIndex (c r : Fin 4) : Fin 16 := ⟨4 * c.val + r.val, by omega⟩
def aesReferenceColumn (i : Fin 16) : Fin 4 := ⟨i.val / 4, by omega⟩
def aesReferenceRow (i : Fin 16) : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩

@[simp] theorem aesReferenceColumn_index (c r : Fin 4) :
    aesReferenceColumn (aesReferenceIndex c r) = c := by
  apply Fin.ext
  simp only [aesReferenceColumn, aesReferenceIndex]
  omega

@[simp] theorem aesReferenceRow_index (c r : Fin 4) :
    aesReferenceRow (aesReferenceIndex c r) = r := by
  apply Fin.ext
  simp only [aesReferenceRow, aesReferenceIndex]
  omega

@[simp] theorem aesReferenceIndex_column_row (i : Fin 16) :
    aesReferenceIndex (aesReferenceColumn i) (aesReferenceRow i) = i := by
  apply Fin.ext
  simp only [aesReferenceIndex, aesReferenceColumn, aesReferenceRow]
  omega

def aesReferenceSubBytes (x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i => aesReferenceSbox (x i))

def aesReferenceInverseSubBytes (x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i => aesReferenceInverseSbox (x i))

def aesReferenceShiftRows (x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i => x
    (aesReferenceIndex (aesReferenceColumn i + aesReferenceRow i) (aesReferenceRow i)))

def aesReferenceInverseShiftRows (x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i => x
    (aesReferenceIndex (aesReferenceColumn i - aesReferenceRow i) (aesReferenceRow i)))

def aesReferenceMul3 (a : Fin 256) : Fin 256 := aesReferenceXor (aesReferenceXtime a) a

def aesReferenceMixColumn (x : AesReferenceWord) : AesReferenceWord :=
  aesReferenceMaterialize ![aesReferenceXor (aesReferenceXor (aesReferenceXor (aesReferenceXtime (x 0))
      (aesReferenceMul3 (x 1))) (x 2)) (x 3),
    aesReferenceXor (aesReferenceXor (aesReferenceXor (x 0)
      (aesReferenceXtime (x 1))) (aesReferenceMul3 (x 2))) (x 3),
    aesReferenceXor (aesReferenceXor (aesReferenceXor (x 0) (x 1))
      (aesReferenceXtime (x 2))) (aesReferenceMul3 (x 3)),
    aesReferenceXor (aesReferenceXor (aesReferenceXor (aesReferenceMul3 (x 0))
      (x 1)) (x 2)) (aesReferenceXtime (x 3))]

def aesReferenceMul9 (a : Fin 256) : Fin 256 :=
  aesReferenceXor (aesReferenceXtime (aesReferenceXtime (aesReferenceXtime a))) a
def aesReferenceMul11 (a : Fin 256) : Fin 256 :=
  aesReferenceXor (aesReferenceXor
    (aesReferenceXtime (aesReferenceXtime (aesReferenceXtime a))) (aesReferenceXtime a)) a
def aesReferenceMul13 (a : Fin 256) : Fin 256 :=
  aesReferenceXor (aesReferenceXor
    (aesReferenceXtime (aesReferenceXtime (aesReferenceXtime a)))
    (aesReferenceXtime (aesReferenceXtime a))) a
def aesReferenceMul14 (a : Fin 256) : Fin 256 :=
  aesReferenceXor (aesReferenceXor
    (aesReferenceXtime (aesReferenceXtime (aesReferenceXtime a)))
    (aesReferenceXtime (aesReferenceXtime a))) (aesReferenceXtime a)

def aesReferenceInverseMixColumn (x : AesReferenceWord) : AesReferenceWord :=
  aesReferenceMaterialize ![aesReferenceXor (aesReferenceXor (aesReferenceXor (aesReferenceMul14 (x 0))
      (aesReferenceMul11 (x 1))) (aesReferenceMul13 (x 2))) (aesReferenceMul9 (x 3)),
    aesReferenceXor (aesReferenceXor (aesReferenceXor (aesReferenceMul9 (x 0))
      (aesReferenceMul14 (x 1))) (aesReferenceMul11 (x 2))) (aesReferenceMul13 (x 3)),
    aesReferenceXor (aesReferenceXor (aesReferenceXor (aesReferenceMul13 (x 0))
      (aesReferenceMul9 (x 1))) (aesReferenceMul14 (x 2))) (aesReferenceMul11 (x 3)),
    aesReferenceXor (aesReferenceXor (aesReferenceXor (aesReferenceMul11 (x 0))
      (aesReferenceMul13 (x 1))) (aesReferenceMul9 (x 2))) (aesReferenceMul14 (x 3))]

def aesReferenceMixColumns (x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i =>
    aesReferenceMixColumn (aesReferenceMaterialize
      (fun r => x (aesReferenceIndex (aesReferenceColumn i) r)))
      (aesReferenceRow i))

def aesReferenceInverseMixColumns (x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i =>
    aesReferenceInverseMixColumn (aesReferenceMaterialize
      (fun r => x (aesReferenceIndex (aesReferenceColumn i) r)))
      (aesReferenceRow i))

def aesReferenceAddRoundKey (x key : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i => aesReferenceXor (x i) (key i))

def aesReferenceRound (key x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceAddRoundKey
    (aesReferenceMixColumns (aesReferenceShiftRows (aesReferenceSubBytes x))) key

def aesReferenceFinalRound (key x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceAddRoundKey (aesReferenceShiftRows (aesReferenceSubBytes x)) key

def aesReferenceInverseRound (key x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceInverseSubBytes (aesReferenceInverseShiftRows
    (aesReferenceInverseMixColumns (aesReferenceAddRoundKey x key)))

def aesReferenceInverseFinalRound (key x : AesReferenceBlock) : AesReferenceBlock :=
  aesReferenceInverseSubBytes (aesReferenceInverseShiftRows (aesReferenceAddRoundKey x key))

def aesReferenceRotWord (w : AesReferenceWord) : AesReferenceWord :=
  aesReferenceMaterialize (fun r => w (r + 1))
def aesReferenceSubWord (w : AesReferenceWord) : AesReferenceWord :=
  aesReferenceMaterialize (fun r => aesReferenceSbox (w r))
def aesReferenceWordXor (w u : AesReferenceWord) : AesReferenceWord :=
  aesReferenceMaterialize (fun r => aesReferenceXor (w r) (u r))

/-- Round constants are one-indexed, as in FIPS 197 Table 5. -/
def aesReferenceRcon (i : Nat) : AesReferenceWord :=
  aesReferenceMaterialize ![(aesReferenceXtime^[i - 1]) 1, 0, 0, 0]

/-- One iteration of FIPS 197 Algorithm 2, including the AES-256-only
SubWord branch when `i mod Nk = 4`. -/
def aesReferenceExpandStep (nk : Nat) (w : Array AesReferenceWord) : Array AesReferenceWord :=
  let i := w.size
  let prev := w[i - 1]!
  let temp := if i % nk = 0 then
      aesReferenceWordXor (aesReferenceSubWord (aesReferenceRotWord prev))
        (aesReferenceRcon (i / nk))
    else if 6 < nk ∧ i % nk = 4 then aesReferenceSubWord prev else prev
  w.push (aesReferenceWordXor w[i - nk]! temp)

def aesReferenceExpandWords (nk : Nat) : Nat → Array AesReferenceWord → Array AesReferenceWord
  | 0, w => w
  | n + 1, w => aesReferenceExpandWords nk n (aesReferenceExpandStep nk w)

theorem aesReferenceExpandWords_size (nk n : Nat) (w : Array AesReferenceWord) :
    (aesReferenceExpandWords nk n w).size = w.size + n := by
  induction n generalizing w with
  | zero => simp [aesReferenceExpandWords]
  | succ n ih => simp [aesReferenceExpandWords, ih, aesReferenceExpandStep,
      Nat.add_assoc, Nat.add_comm]

def aesReferenceExpandedKey (v : AesReferenceVariant) (key : AesReferenceKey v) :
    Array AesReferenceWord :=
  let initial := Array.ofFn (fun c : Fin v.keyWords => aesReferenceMaterialize
    (fun r : Fin 4 => key ⟨4 * c.val + r.val, by omega⟩))
  aesReferenceExpandWords v.keyWords (4 * (v.rounds + 1) - v.keyWords) initial

theorem aesReferenceExpandedKey_size (v : AesReferenceVariant) (key : AesReferenceKey v) :
    (aesReferenceExpandedKey v key).size = 4 * (v.rounds + 1) := by
  cases v <;> simp [aesReferenceExpandedKey, aesReferenceExpandWords_size,
    AesReferenceVariant.keyWords, AesReferenceVariant.rounds]

def aesReferenceRoundKey (w : Array AesReferenceWord) (r : Nat) : AesReferenceBlock :=
  aesReferenceMaterialize (fun i => w[4 * r + (aesReferenceColumn i).val]!
    (aesReferenceRow i))

theorem aesReferenceRoundKey_in_bounds (v : AesReferenceVariant) (key : AesReferenceKey v)
    (r : Nat) (hr : r ≤ v.rounds) (i : Fin 16) :
    4 * r + (aesReferenceColumn i).val < (aesReferenceExpandedKey v key).size := by
  rw [aesReferenceExpandedKey_size]
  have h := (aesReferenceColumn i).isLt
  omega

/-- The first `n` full rounds, with schedule keys numbered from 1.
In standardized encryption this is used only for `n ≤ Nr - 1`. -/
def aesReferenceFullRounds (w : Array AesReferenceWord) : Nat → AesReferenceBlock → AesReferenceBlock
  | 0, x => x
  | n + 1, x => aesReferenceRound (aesReferenceRoundKey w (n + 1))
      (aesReferenceFullRounds w n x)

def aesReferenceInverseFullRounds (w : Array AesReferenceWord) :
    Nat → AesReferenceBlock → AesReferenceBlock
  | 0, x => x
  | n + 1, x => aesReferenceInverseFullRounds w n
      (aesReferenceInverseRound (aesReferenceRoundKey w (n + 1)) x)

/-- FIPS 197 CIPHER(): initial AddRoundKey, `Nr-1` full rounds, final
SubBytes/ShiftRows/AddRoundKey. -/
def aesReferenceEncrypt (v : AesReferenceVariant) (key : AesReferenceKey v)
    (input : AesReferenceBlock) : AesReferenceBlock :=
  let w := aesReferenceExpandedKey v key
  aesReferenceFinalRound (aesReferenceRoundKey w v.rounds)
    (aesReferenceFullRounds w (v.rounds - 1)
      (aesReferenceAddRoundKey input (aesReferenceRoundKey w 0)))

/-- The standard inverse cipher, grouped by inverse encryption rounds. -/
def aesReferenceDecrypt (v : AesReferenceVariant) (key : AesReferenceKey v)
    (input : AesReferenceBlock) : AesReferenceBlock :=
  let w := aesReferenceExpandedKey v key
  aesReferenceAddRoundKey
    (aesReferenceInverseFullRounds w (v.rounds - 1)
      (aesReferenceInverseFinalRound (aesReferenceRoundKey w v.rounds) input))
    (aesReferenceRoundKey w 0)

/-- Read a hexadecimal numeral as `n` bytes, most significant byte first.
Leading zero bytes are retained by the explicit length. -/
def aesReferenceBytesOfNat (n value : Nat) : Vector (Fin 256) n :=
  aesReferenceMaterialize
    (fun i => ⟨value / 256 ^ (n - 1 - i.val) % 256, Nat.mod_lt _ (by omega)⟩)
def aesReferenceBlockOfHex (value : Nat) : AesReferenceBlock := aesReferenceBytesOfNat 16 value
def aesReferenceKeyOfHex (v : AesReferenceVariant) (value : Nat) : AesReferenceKey v :=
  aesReferenceBytesOfNat (4 * v.keyWords) value

def aesReferenceWordValue (w : AesReferenceWord) : Nat :=
  ((w 0).val * 256 + (w 1).val) * 65536 + (w 2).val * 256 + (w 3).val

end PairwiseIndependence
