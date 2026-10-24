import PairwiseIndependence.Pairwise.RepeatedBlocks

/-!
# AES rounds and the superbox rearrangement

AES-style rounds over arbitrary SubBytes, ShiftRows and MixColumns maps: the
four-round core of Theorem 5, its Appendix B.1 superbox rearrangement, and the
`4r + 4`-round family of Corollary 2 with independent round keys. The
concrete FIPS 197 maps are substituted in `AES/Instances.lean`.
-/

namespace PairwiseIndependence

variable {A : Type*} [AddCommGroup A]

/-- A full AES-style round with explicit round key. -/
def aesStyleRound (subBytes : A ≃ A)
    (shiftRows mixColumns : A ≃+ A) (key x : A) : A :=
  mixColumns (shiftRows (subBytes x)) + key

/-- Three full rounds followed by the substitution layer of the fourth round,
as in the paper's four-round superbox decomposition. -/
def aesStyleFourRoundCore (subBytes : A ≃ A)
    (shiftRows mixColumns : A ≃+ A)
    (keys : A × A × A) (x : A) : A :=
  subBytes
    (aesStyleRound subBytes shiftRows mixColumns keys.2.2
      (aesStyleRound subBytes shiftRows mixColumns keys.2.1
        (aesStyleRound subBytes shiftRows mixColumns keys.1 x)))

/-- Every explicit AES-style round is a permutation. -/
theorem aesStyleRound_bijective
    (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A)
    (key : A) :
    Function.Bijective (aesStyleRound subBytes shiftRows mixColumns key) := by
  change Function.Bijective
    ((Equiv.addRight key) ∘ (fun x => mixColumns x) ∘
      (fun x => shiftRows x) ∘ (fun x => subBytes x))
  exact (Equiv.addRight key).bijective.comp
    (mixColumns.bijective.comp (shiftRows.bijective.comp subBytes.bijective))

/-- Every explicit four-round AES-style core is a permutation. -/
theorem aesStyleFourRoundCore_bijective
    (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A)
    (keys : A × A × A) :
    Function.Bijective (aesStyleFourRoundCore subBytes shiftRows mixColumns keys) := by
  change Function.Bijective
    ((fun x => subBytes x) ∘
      aesStyleRound subBytes shiftRows mixColumns keys.2.2 ∘
      aesStyleRound subBytes shiftRows mixColumns keys.2.1 ∘
      aesStyleRound subBytes shiftRows mixColumns keys.1)
  exact subBytes.bijective.comp
    ((aesStyleRound_bijective subBytes shiftRows mixColumns keys.2.2).comp
      ((aesStyleRound_bijective subBytes shiftRows mixColumns keys.2.1).comp
        (aesStyleRound_bijective subBytes shiftRows mixColumns keys.1)))

/-- One key-dependent superbox layer: substitution, MixColumns, key addition,
and substitution. For the concrete AES, this splits into four 32-bit boxes. -/
def aesStyleSuperbox (subBytes : A ≃ A)
    (mixColumns : A ≃+ A) (key x : A) : A :=
  subBytes (mixColumns (subBytes x) + key)

/-- The middle linear layer is `ShiftRows ∘ MixColumns ∘ ShiftRows`.
The middle key is reindexed by `ShiftRows`. -/
def aesStyleSuperboxMiddle (shiftRows mixColumns : A ≃+ A)
    (key x : A) : A :=
  shiftRows (mixColumns (shiftRows x)) + shiftRows key

/-- Appendix A's all-key, all-plaintext superbox identity. The hypothesis is
the coordinatewise commutation of SubBytes and ShiftRows. -/
theorem aesStyleFourRoundCore_eq_superbox
    (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A)
    (hcomm : ∀ x : A, shiftRows (subBytes x) = subBytes (shiftRows x))
    (keys : A × A × A) (x : A) :
    aesStyleFourRoundCore subBytes shiftRows mixColumns keys x =
      aesStyleSuperbox subBytes mixColumns keys.2.2
        (aesStyleSuperboxMiddle shiftRows mixColumns keys.2.1
          (aesStyleSuperbox subBytes mixColumns keys.1 (shiftRows x))) := by
  simp [aesStyleFourRoundCore, aesStyleRound, aesStyleSuperbox,
    aesStyleSuperboxMiddle, ← hcomm]
  rw [hcomm, map_add]

/-- The middle linear layer `ShiftRows ∘ MixColumns ∘ ShiftRows` of
Appendix B.1, as an additive permutation. -/
def aesStyleMiddleLinearLayer {W : Type*} [AddCommGroup W]
    (shiftRows mixColumns : State W 4 ≃+ State W 4) :
    State W 4 ≃+ State W 4 :=
  (shiftRows.trans mixColumns).trans shiftRows

/-- Four complete AES-style rounds (SubBytes, ShiftRows, MixColumns,
AddRoundKey), without the key of the fourth round. With independent round
keys, that key is the fresh key between blocks in `repeatedBlocks`, or the
output whitening key of `IsPairwiseIndependent` after the last block.
Theorem 5 concerns `aesStyleFourRoundCore`, which stops after the fourth
SubBytes; the missing ShiftRows and MixColumns are appended here. -/
def aesStyleFourRounds (subBytes : A ≃ A)
    (shiftRows mixColumns : A ≃+ A) (keys : A × A × A) (x : A) : A :=
  mixColumns (shiftRows (aesStyleFourRoundCore subBytes shiftRows mixColumns keys x))

/-- Adding the fourth round key gives exactly four full AES-style rounds. -/
theorem aesStyleFourRounds_add_key (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A)
    (keys : A × A × A) (key x : A) :
    aesStyleFourRounds subBytes shiftRows mixColumns keys x + key =
      aesStyleRound subBytes shiftRows mixColumns key
        (aesStyleRound subBytes shiftRows mixColumns keys.2.2
          (aesStyleRound subBytes shiftRows mixColumns keys.2.1
            (aesStyleRound subBytes shiftRows mixColumns keys.1 x))) := rfl

theorem aesStyleFourRounds_bijective
    (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A) (keys : A × A × A) :
    Function.Bijective (aesStyleFourRounds subBytes shiftRows mixColumns keys) :=
  mixColumns.bijective.comp (shiftRows.bijective.comp
    (aesStyleFourRoundCore_bijective subBytes shiftRows mixColumns keys))

/-- `4r + 4` AES-style rounds with independent round keys. As in FIPS 197,
the last round omits MixColumns. The initial and final round keys are not
part of this family: `IsPairwiseIndependent` adds them as its independent
uniform input and output whitening keys. -/
def aesStyleRounds (subBytes : A ≃ A)
    (shiftRows mixColumns : A ≃+ A) (r : ℕ)
    (key : RepeatedBlockKeys (A × A × A) A r) (x : A) : A :=
  mixColumns.symm
    (repeatedBlocks (aesStyleFourRounds subBytes shiftRows mixColumns) r key x)

/-- Four rounds: three full rounds, then SubBytes and ShiftRows. -/
theorem aesStyleRounds_zero (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A)
    (keys : RepeatedBlockKeys (A × A × A) A 0) (x : A) :
    aesStyleRounds subBytes shiftRows mixColumns 0 keys x =
      shiftRows (aesStyleFourRoundCore subBytes shiftRows mixColumns keys x) := by
  simp [aesStyleRounds, aesStyleFourRounds, repeatedBlocks]

/-- Four more rounds: MixColumns and a fresh round key complete the previous
final round, followed by the next three full rounds, SubBytes and ShiftRows. -/
theorem aesStyleRounds_succ (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A) (r : ℕ)
    (key : RepeatedBlockKeys (A × A × A) A (r + 1)) (x : A) :
    aesStyleRounds subBytes shiftRows mixColumns (r + 1) key x =
      shiftRows (aesStyleFourRoundCore subBytes shiftRows mixColumns key.2.1
        (mixColumns (aesStyleRounds subBytes shiftRows mixColumns r key.1 x) +
          key.2.2)) := by
  simp [aesStyleRounds, aesStyleFourRounds, repeatedBlocks]

end PairwiseIndependence
