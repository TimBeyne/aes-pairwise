import PairwiseIndependence.AesBounds.FourRoundBound
import PairwiseIndependence.KeliherSui.UpperBound
import PairwiseIndependence.Pairwise.IteratedBlocks
import PairwiseIndependence.Corollary2
import PairwiseIndependence.AES.Equivalence

/-!
# Corollary 2 for the implementation's rounds

`4r + 4` rounds of AES with independent uniform round keys are
`2^14 · 2^(-39r)`-pairwise independent. The four-round difference-distribution
estimates are Theorem 5 and the Keliher–Sui bound `(53 · 2^(-34))^4 ≤ 2^(-113)`,
which is proved in `KeliherSui/`. Lemmas 4 and 6 turn them into the
pairwise-independence bound (`Pairwise/IteratedBlocks.lean`).
`Corollary2.lean` restates the result for the definitions in `AES/AES.lean`.
-/

namespace PairwiseIndependence

universe u

/-- Removing the final MixColumns does not change pairwise independence, so
the `4r + 4`-round family may be analyzed as repeated complete four-round
blocks. -/
theorem isPairwiseIndependent_aesStyleRounds_iff
    {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (subBytes : A ≃ A) (shiftRows mixColumns : A ≃+ A) (r : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsPairwiseIndependent (aesStyleRounds subBytes shiftRows mixColumns r) ε ↔
      IsPairwiseIndependent
        (repeatedBlocks (fun key x => (shiftRows.trans mixColumns)
          (aesStyleFourRoundCore subBytes shiftRows mixColumns key x)) r) ε :=
  isPairwiseIndependent_addEquiv_comp_iff
    (repeatedBlocks (fun key x => (shiftRows.trans mixColumns)
      (aesStyleFourRoundCore subBytes shiftRows mixColumns key x)) r)
    (fun key => (repeatedBlocks_bijective _
      (aesStyleFourRounds_bijective subBytes shiftRows mixColumns) r key).1)
    mixColumns.symm ε hε

-- Keep the recursive key-space instance visible while `r` is a variable.
local instance (r : ℕ) : Fintype
    (RepeatedBlockKeys
      (AesByteState AesByte × AesByteState AesByte × AesByteState AesByte)
      (AesByteState AesByte) r) :=
  instFintypeRepeatedBlockKeys r

/-- Corollary 2 for `aesIndependentRounds`, the implementation's `4r + 4`
rounds grouped into four-round blocks. -/
theorem corollary2_aesIndependentRoundKeys_sharp (r : ℕ) :
    IsPairwiseIndependent (aesIndependentRounds r)
      ((2 : ℝ) ^ 14 * (1 / (2 : ℝ) ^ 39) ^ r) :=
  (isPairwiseIndependent_aesStyleRounds_iff (aesCoordinateSubBytes aesSboxEquiv)
    aesCoordinateShiftRows (aesCoordinateMixColumns aesMixColumnEquiv) r _
    (by positivity)).mpr
    (corollary2_of_fourRoundCore_estimates aesIndependentFourRoundCore
      (aesStyleFourRoundCore_bijective _ _ _)
      (aesCoordinateShiftRows.trans (aesCoordinateMixColumns aesMixColumnEquiv))
      (by simp [AesByteState, State])
      theorem5_aesIndependentRoundKeys
      (KeliherSuiFourRoundEstimate.le_paper
        (KeliherSuiTwoRoundEstimate.fourRound keliherSui_twoRoundEstimate))
      r)

/-- Corollary 2 of the paper; the statement is in `Corollary2.lean`. The rounds
and round keys of `AES.cipher r` are regrouped into `r + 1` four-round blocks. -/
theorem corollary2_aesCipher : Corollary2 := by
  intro r
  rw [show AES.cipher r = fun k => aesIndependentRounds r (AES.blockKeysEquiv r k) by
    funext k s
    rw [AES.cipher_eq, AES.blockKeysEquiv_apply]]
  have hinj (key : RepeatedBlockKeys (AES.State × AES.State × AES.State) AES.State r) :
      Function.Injective (aesIndependentRounds r key) :=
    (aesCoordinateMixColumns aesMixColumnEquiv).symm.injective.comp
      (repeatedBlocks_bijective _ (aesStyleFourRounds_bijective _ _ _) r key).1
  rw [isPairwiseIndependent_key_reindex (AES.blockKeysEquiv r) _ hinj _ (by positivity)]
  exact corollary2_aesIndependentRoundKeys_sharp r

end PairwiseIndependence
