import PairwiseIndependence.AES.AES
import PairwiseIndependence.AES.Instances

/-!
# The AES implementation agrees with `AES/AES.lean`

The proofs use a bit-level implementation of AES that suits finite
certificates: MixColumns through `xtime`, and the S-box as field inversion by
table followed by the affine map. This file proves that the implementation
equals the definitions in `AES/AES.lean`, map by map. It then proves the same
for the round structures used in the proofs: the superbox, four rounds, and
`4r + 4` rounds grouped into blocks of four.
-/

open Polynomial
open scoped Matrix

namespace PairwiseIndependence

namespace AES

/-! ### SubBytes -/

theorem sbox_eq (b : AesByte) : sbox b = aesSboxEquiv b := by
  have h : ∀ b : AesByte, sbox b = aesSbox b := by native_decide
  exact h b

/-! ### MixColumns -/

private theorem byteToGF_eq_mk (b : AesByte) :
    byteToGF b = AdjoinRoot.mk modulus (∑ i : Fin 8, C (b i) * X ^ i.val) := by
  rw [map_sum]
  simp only [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, byteToGF, x]

private theorem gfToByte_byteToGF (b : AesByte) : gfToByte (byteToGF b) = b := by
  funext i
  have hdeg : (∑ j : Fin 8, C (b j) * X ^ j.val).degree < modulus.degree := by
    have hm : modulus.degree = 8 := by unfold modulus; compute_degree!
    rw [hm]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe 8)]
    intro j _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      (by exact_mod_cast (show j.val < 8 from j.isLt))
  simp only [gfToByte, byteToGF_eq_mk, AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff modulus_monic).mpr hdeg,
    Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  simp [Fin.val_inj]

private theorem two_eq_zero : (2 : GF) = 0 := by
  have h : (2 : GF) = AdjoinRoot.of modulus 2 := (map_ofNat (AdjoinRoot.of modulus) 2).symm
  rw [h]
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [h2]

private theorem x_root : x ^ 8 + x ^ 4 + x ^ 3 + x + 1 = 0 := by
  have h : AdjoinRoot.mk modulus (X ^ 8 + X ^ 4 + X ^ 3 + X + 1) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact h

private theorem byteToGF_add (a b : AesByte) :
    byteToGF (a + b) = byteToGF a + byteToGF b := by
  simp [byteToGF, add_mul, Finset.sum_add_distrib]

/-- The implementation's `xtime` is multiplication by `x`. -/
private theorem byteToGF_xtime (b : AesByte) : byteToGF (aesXtime b) = x * byteToGF b := by
  simp only [byteToGF, aesXtime, Fin.sum_univ_eight]
  simp [map_add]
  linear_combination (AdjoinRoot.of modulus (b 7)) * x_root -
    (AdjoinRoot.of modulus (b 7) * x ^ 8) * two_eq_zero

private theorem byteToGF_mul3 (b : AesByte) :
    byteToGF (aesMul3 b) = (x + 1) * byteToGF b := by
  simp [aesMul3, byteToGF_add, byteToGF_xtime, add_mul]

theorem mixColumn_eq (c : Column) : mixColumn c = aesMixColumnEquiv c := by
  funext r
  have h : (mixColumnsMatrix *ᵥ fun i => byteToGF (c i)) r =
      byteToGF (aesMixColumn c r) := by
    fin_cases r <;>
      simp [mixColumnsMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, aesMixColumn,
        byteToGF_add, byteToGF_xtime, byteToGF_mul3]
  simp only [mixColumn, h, gfToByte_byteToGF]
  rfl

/-! ### Rounds -/

theorem subBytes_eq (s : State) : subBytes s = aesCoordinateSubBytes aesSboxEquiv s := by
  funext c r
  exact sbox_eq (s c r)

theorem shiftRows_eq (s : State) : shiftRows s = aesCoordinateShiftRows s := rfl

theorem mixColumns_eq (s : State) :
    mixColumns s = aesCoordinateMixColumns aesMixColumnEquiv s := by
  funext c
  exact mixColumn_eq (s c)

theorem round_eq (k s : State) :
    round k s = aesStyleRound (aesCoordinateSubBytes aesSboxEquiv) aesCoordinateShiftRows
      (aesCoordinateMixColumns aesMixColumnEquiv) k s := by
  simp only [round, aesStyleRound, subBytes_eq, shiftRows_eq, mixColumns_eq]

theorem superbox_eq (k c : Column) : superbox k c = aesIndependentSuperbox k c := by
  funext r
  simp only [superbox, sbox_eq, mixColumn_eq]
  rfl

/-- Four rounds are the four-round core followed by the fourth round's
ShiftRows, MixColumns and round key. -/
theorem rounds_four (k : Fin 4 → State) (s : State) :
    rounds 4 k s =
      (aesCoordinateShiftRows.trans (aesCoordinateMixColumns aesMixColumnEquiv))
        (aesIndependentFourRoundCore (k 0, k 1, k 2) s) + k 3 := by
  simp only [rounds, round_eq]
  rfl

/-- The round keys of four rounds, grouped as the core's keys and the last key. -/
def fourRoundKeys : (Fin 4 → State) ≃ (State × State × State) × State where
  toFun k := ((k 0, k 1, k 2), k 3)
  invFun p := ![p.1.1, p.1.2.1, p.1.2.2, p.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

/-- The round keys of `4r + 4` rounds, grouped as for `repeatedBlocks`: three
keys inside each four-round block and one key between consecutive blocks. -/
def blockKeys : (r : ℕ) → (Fin (4 * r + 3) → State) →
    RepeatedBlockKeys (State × State × State) State r
  | 0, k => (k 0, k 1, k 2)
  | r + 1, k =>
      (blockKeys r (fun i => k (Fin.castLE (by omega) i)),
        (k ⟨4 * r + 4, by omega⟩, k ⟨4 * r + 5, by omega⟩, k ⟨4 * r + 6, by omega⟩),
        k ⟨4 * r + 3, by omega⟩)

/-- The keys of one block: the key before it and the three keys inside it. -/
def lastFourKeys : (Fin 4 → State) ≃ (State × State × State) × State where
  toFun k := ((k 1, k 2, k 3), k 0)
  invFun p := ![p.2, p.1.1, p.1.2.1, p.1.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

/-- `blockKeys` as an equivalence. -/
def blockKeysEquiv : (r : ℕ) → (Fin (4 * r + 3) → State) ≃
    RepeatedBlockKeys (State × State × State) State r
  | 0 =>
    { toFun := fun k => (k 0, k 1, k 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun k => by funext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }
  | r + 1 => (Fin.appendEquiv (4 * r + 3) 4).symm.trans
      ((blockKeysEquiv r).prodCongr lastFourKeys)

theorem blockKeysEquiv_apply : ∀ (r : ℕ) (k : Fin (4 * r + 3) → State),
    blockKeysEquiv r k = blockKeys r k
  | 0, k => rfl
  | r + 1, k => by
      change ((blockKeysEquiv r) (fun i => k (Fin.castAdd 4 i)), _) = _
      rw [blockKeysEquiv_apply r]
      rfl

/-- After `4r + 3` rounds, the final round's SubBytes and ShiftRows and a
MixColumns, the result is `r + 1` complete four-round blocks. -/
theorem rounds_eq_repeatedBlocks : ∀ (r : ℕ) (k : Fin (4 * r + 3) → State) (s : State),
    aesCoordinateMixColumns aesMixColumnEquiv (shiftRows (subBytes (rounds (4 * r + 3) k s))) =
      repeatedBlocks (aesStyleFourRounds (aesCoordinateSubBytes aesSboxEquiv)
        aesCoordinateShiftRows (aesCoordinateMixColumns aesMixColumnEquiv)) r (blockKeys r k) s
  | 0, k, s => by
      simp only [rounds, round_eq, subBytes_eq, shiftRows_eq]
      rfl
  | r + 1, k, s => by
      have ih := rounds_eq_repeatedBlocks r (fun i => k (Fin.castLE (by omega) i)) s
      have hstep : rounds (4 * (r + 1) + 3) k s =
          round (k ⟨4 * r + 6, by omega⟩) (round (k ⟨4 * r + 5, by omega⟩)
            (round (k ⟨4 * r + 4, by omega⟩)
              (mixColumns (shiftRows (subBytes
                (rounds (4 * r + 3) (fun i => k (Fin.castLE (by omega) i)) s))) +
                k ⟨4 * r + 3, by omega⟩))) := rfl
      rw [hstep, mixColumns_eq, ih]
      simp only [round_eq, subBytes_eq, shiftRows_eq]
      rfl

/-- `4r + 4` rounds are the implementation's `r + 1` four-round blocks. -/
theorem cipher_eq (r : ℕ) (k : Fin (4 * r + 3) → State) (s : State) :
    cipher r k s = aesIndependentRounds r (blockKeys r k) s := by
  change cipher r k s = (aesCoordinateMixColumns aesMixColumnEquiv).symm
    (repeatedBlocks _ r (blockKeys r k) s)
  rw [← rounds_eq_repeatedBlocks]
  simp [cipher]

end AES

end PairwiseIndependence
