import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Data.Matrix.Notation

/-!
# AES

The AES round function of FIPS 197
(https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf), with
independent round keys. Together with `Pairwise/Definitions.lean`, this file
contains every definition that the statements of the main theorems depend on.

* A byte is eight bits; byte addition is bitwise XOR.
* SubBytes looks up each byte in the S-box table of FIPS 197.
* MixColumns multiplies each column by the matrix of FIPS 197, Section 5.1.3,
  over `GF(2⁸) = GF(2)[x] / (x⁸ + x⁴ + x³ + x + 1)`. The byte with bits
  `b₇ … b₀` is the field element `b₇ x⁷ + ⋯ + b₁ x + b₀`.
* ShiftRows rotates row `r` of the state to the left by `r` positions.
-/

open Polynomial
open scoped Matrix

namespace PairwiseIndependence

/-- A byte. Bit `i` has weight `2^i`; addition is bitwise XOR. -/
abbrev AesByte := Fin 8 → ZMod 2

/-- The byte with numerical value `n < 256`. -/
def aesByteOfNat (n : ℕ) : AesByte :=
  fun i => (n / 2 ^ i.val % 2 : ℕ)

/-- The numerical value of a byte. -/
def aesByteToNat (b : AesByte) : ℕ :=
  ∑ i : Fin 8, (b i).val * 2 ^ i.val

namespace AES

/-- The S-box of FIPS 197: the image of the byte with value `n` is entry `n`. -/
def sboxTable : Array ℕ := #[
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

/-- SubBytes on one byte. -/
def sbox (b : AesByte) : AesByte :=
  aesByteOfNat sboxTable[aesByteToNat b]!

/-- The AES polynomial `x⁸ + x⁴ + x³ + x + 1` over `GF(2)`. -/
noncomputable def modulus : (ZMod 2)[X] := X ^ 8 + X ^ 4 + X ^ 3 + X + 1

/-- The field `GF(2⁸) = GF(2)[x] / (x⁸ + x⁴ + x³ + x + 1)`. -/
abbrev GF := AdjoinRoot modulus

/-- The element `x` of `GF(2⁸)`, the byte `02` of FIPS 197. -/
noncomputable def x : GF := AdjoinRoot.root modulus

/-- The field element of a byte: `b ↦ b₇ x⁷ + ⋯ + b₁ x + b₀`. -/
noncomputable def byteToGF (b : AesByte) : GF :=
  ∑ i : Fin 8, AdjoinRoot.of modulus (b i) * x ^ i.val

theorem modulus_monic : modulus.Monic := by
  unfold modulus
  monicity!

/-- The byte of a field element: the coefficients of its representative of
degree less than 8. -/
noncomputable def gfToByte (a : GF) : AesByte :=
  fun i => (AdjoinRoot.modByMonicHom modulus_monic a).coeff i

/-- The MixColumns matrix, with `02 = x` and `03 = x + 1`. -/
noncomputable def mixColumnsMatrix : Matrix (Fin 4) (Fin 4) GF :=
  !![x,     x + 1, 1,     1;
     1,     x,     x + 1, 1;
     1,     1,     x,     x + 1;
     x + 1, 1,     1,     x]

/-- A column of the state: four bytes, indexed by row. -/
abbrev Column := Fin 4 → AesByte

/-- The state: four columns. `s c r` is the byte `s_{r,c}` of FIPS 197, in
row `r` and column `c`. -/
abbrev State := Fin 4 → Column

/-- MixColumns on one column. -/
noncomputable def mixColumn (c : Column) : Column :=
  fun r => gfToByte ((mixColumnsMatrix *ᵥ fun i => byteToGF (c i)) r)

/-- SubBytes. -/
def subBytes (s : State) : State :=
  fun c r => sbox (s c r)

/-- ShiftRows: `s'_{r,c} = s_{r,c+r}`, with column indices modulo 4. -/
def shiftRows (s : State) : State :=
  fun c r => s (c + r) r

/-- MixColumns. -/
noncomputable def mixColumns (s : State) : State :=
  fun c => mixColumn (s c)

/-- One AES round with round key `k`. -/
noncomputable def round (k s : State) : State :=
  mixColumns (shiftRows (subBytes s)) + k

/-- `N` AES rounds with round keys `k 0, …, k (N - 1)`. -/
noncomputable def rounds : (N : ℕ) → (Fin N → State) → State → State
  | 0, _, s => s
  | N + 1, k, s => round (k (Fin.last N)) (rounds N (fun i => k i.castSucc) s)

/-- `4r + 4` rounds of AES: `4r + 3` rounds, then a final round without
MixColumns, as in FIPS 197. The initial AddRoundKey and the final round key
are left out; they are the input and output whitening keys that
`IsPairwiseIndependent` adds. -/
noncomputable def cipher (r : ℕ) (k : Fin (4 * r + 3) → State) (s : State) : State :=
  shiftRows (subBytes (rounds (4 * r + 3) k s))

/-- The superbox with key `k`: SubBytes, MixColumns, AddRoundKey and SubBytes
on one column. -/
noncomputable def superbox (k c : Column) : Column :=
  fun r => sbox (mixColumn (fun i => sbox (c i)) r + k r)

end AES

end PairwiseIndependence
