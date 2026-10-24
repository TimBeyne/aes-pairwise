import PairwiseIndependence.AES.Rounds
import PairwiseIndependence.Pairwise.KeyedShark
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# From AES-style rounds to independently keyed SHARK

Appendix B.1's rearrangement is made into an exact all-key identity and an
equality of spectral-bias norms. The only premise about the concrete maps is
the factorization of a keyed column superbox into independent 32-bit word
permutations, proved in `AES/Coordinates.lean`. Uniform reindexing of the
keys and the initial ShiftRows permutation are both handled explicitly.
-/

namespace PairwiseIndependence

variable {W : Type*} [AddCommGroup W]

/-- Appendix B.1 as an exact keyed SHARK identity, conditional only on the
columnwise superbox factorization. -/
theorem aesStyleFourRoundCore_eq_keyedShark_preShiftRows
    (subBytes : State W 4 ≃ State W 4)
    (shiftRows mixColumns : State W 4 ≃+ State W 4)
    (S : W → W ≃ W)
    (hcomm : ∀ x : State W 4,
      shiftRows (subBytes x) = subBytes (shiftRows x))
    (hSuperbox : ∀ key x : State W 4,
      aesStyleSuperbox subBytes mixColumns key x = keyedSubstitute S key x)
    (keys : State W 4 × State W 4 × State W 4) (x : State W 4) :
    aesStyleFourRoundCore subBytes shiftRows mixColumns keys x =
      keyedSharkTwoCore S (aesStyleMiddleLinearLayer shiftRows mixColumns)
        (keys.1, keys.2.2,
          (aesStyleMiddleLinearLayer shiftRows mixColumns).symm
            (shiftRows keys.2.1)) (shiftRows x) := by
  rw [aesStyleFourRoundCore_eq_superbox subBytes shiftRows mixColumns hcomm]
  rw [hSuperbox, hSuperbox]
  simp [aesStyleSuperboxMiddle, aesStyleMiddleLinearLayer,
    keyedSharkTwoCore, map_add]

/-- Reindex the three independent AES-style round keys to the two superbox
keys and the middle SHARK key. -/
def aesStyleKeyToSharkKey
    (shiftRows mixColumns : State W 4 ≃+ State W 4) :
    (State W 4 × State W 4 × State W 4) ≃
      (State W 4 × State W 4 × State W 4) where
  toFun keys :=
    (keys.1, keys.2.2,
      (aesStyleMiddleLinearLayer shiftRows mixColumns).symm (shiftRows keys.2.1))
  invFun key :=
    (key.1,
      shiftRows.symm ((aesStyleMiddleLinearLayer shiftRows mixColumns) key.2.2),
      key.2.1)
  left_inv := by
    intro ⟨k₁, k₂, k₃⟩
    simp
  right_inv := by
    intro ⟨k₁, k₂, k₃⟩
    simp

variable [Fintype W]

/-- The averaged four-round AES-style matrix is the keyed SHARK matrix with
its input-difference columns permuted by the initial ShiftRows. -/
theorem aesStyleFourRoundCore_differenceDistributionMatrix_eq_keyedShark_preShiftRows
    (subBytes : State W 4 ≃ State W 4)
    (shiftRows mixColumns : State W 4 ≃+ State W 4)
    (S : W → W ≃ W)
    (hcomm : ∀ x : State W 4,
      shiftRows (subBytes x) = subBytes (shiftRows x))
    (hSuperbox : ∀ key x : State W 4,
      aesStyleSuperbox subBytes mixColumns key x = keyedSubstitute S key x) :
    differenceDistributionMatrix
        (aesStyleFourRoundCore subBytes shiftRows mixColumns) =
      differenceDistributionMatrix
        (fun key : State W 4 × State W 4 × State W 4 =>
          fun x => keyedSharkTwoCore S
            (aesStyleMiddleLinearLayer shiftRows mixColumns) key (shiftRows x)) := by
  let e := aesStyleKeyToSharkKey shiftRows mixColumns
  have hfun : aesStyleFourRoundCore subBytes shiftRows mixColumns =
      (fun keys x => keyedSharkTwoCore S
        (aesStyleMiddleLinearLayer shiftRows mixColumns) (e keys) (shiftRows x)) := by
    funext keys x
    exact aesStyleFourRoundCore_eq_keyedShark_preShiftRows
      subBytes shiftRows mixColumns S hcomm hSuperbox keys x
  rw [hfun]
  exact differenceDistributionMatrix_key_reindex e
    (fun key : State W 4 × State W 4 × State W 4 =>
      fun x => keyedSharkTwoCore S
        (aesStyleMiddleLinearLayer shiftRows mixColumns) key (shiftRows x))

open scoped Matrix.Norms.L2Operator in
theorem deterministicDifferenceDistributionMatrix_addEquiv_eq_permMatrix
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (L : A ≃+ A) :
    deterministicDifferenceDistributionMatrix (fun x : A => L x) =
      Equiv.Perm.permMatrix ℝ L.toEquiv.symm := by
  ext b a
  change deterministicDifferenceDistributionMatrix
    (fun x : A => L.toAddMonoidHom x) b a = _
  rw [deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_some_iff]
  by_cases h : L a = b
  · have h' : L.symm b = a := by simpa using (congrArg L.symm h).symm
    simp [h, h']
  · have h' : L.symm b ≠ a := by
      intro heq
      apply h
      simpa using (congrArg L heq).symm
    simp [h, h']

open scoped Matrix.Norms.L2Operator in
theorem matrix_norm_mul_addEquiv_differenceDistributionMatrix_eq
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (L : A ≃+ A) (M : Matrix A A ℝ) :
    ‖M * deterministicDifferenceDistributionMatrix (fun x : A => L x)‖ = ‖M‖ := by
  let P : Matrix A A ℝ := Equiv.Perm.permMatrix ℝ L.toEquiv.symm
  let Q : Matrix A A ℝ := Equiv.Perm.permMatrix ℝ L.toEquiv
  have hPQ : (M * P) * Q = M := by
    simp [P, Q, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  have hPnorm : ‖P‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le _
  have hQnorm : ‖Q‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le _
  rw [deterministicDifferenceDistributionMatrix_addEquiv_eq_permMatrix]
  apply le_antisymm
  · calc
      ‖M * P‖ ≤ ‖M‖ * ‖P‖ := norm_mul_le M P
      _ ≤ ‖M‖ * 1 := mul_le_mul_of_nonneg_left hPnorm (norm_nonneg M)
      _ = ‖M‖ := mul_one _
  · calc
      ‖M‖ = ‖(M * P) * Q‖ := by rw [hPQ]
      _ ≤ ‖M * P‖ * ‖Q‖ := norm_mul_le (M * P) Q
      _ ≤ ‖M * P‖ * 1 :=
        mul_le_mul_of_nonneg_left hQnorm (norm_nonneg (M * P))
      _ = ‖M * P‖ := mul_one _

/-- The uniform benchmark is invariant under a permutation of input
differences induced by an additive equivalence. -/
theorem uniformDifferenceDistributionMatrix_mul_addEquiv_eq
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (L : A ≃+ A) :
    uniformDifferenceDistributionMatrix A *
      deterministicDifferenceDistributionMatrix (fun x : A => L x) =
        uniformDifferenceDistributionMatrix A := by
  rw [deterministicDifferenceDistributionMatrix_addEquiv_eq_permMatrix]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext b a
  change uniformDifferenceDistributionMatrix A b (L a) =
    uniformDifferenceDistributionMatrix A b a
  simp [uniformDifferenceDistributionMatrix_apply]

open scoped Matrix.Norms.L2Operator
/-- The paper's spectral-bias norm is unchanged by a fixed additive
permutation of the input differences. -/
theorem differenceDistributionMatrix_family_comp_addEquiv_spectralBias_eq
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] (f : κ → A → A) (L : A ≃+ A) :
    ‖differenceDistributionMatrix (fun key x => f key (L x)) -
      uniformDifferenceDistributionMatrix A‖ =
      ‖differenceDistributionMatrix f -
        uniformDifferenceDistributionMatrix A‖ := by
  rw [differenceDistributionMatrix_family_comp_addEquiv]
  have hmatrix : differenceDistributionMatrix f *
      deterministicDifferenceDistributionMatrix (fun x : A => L x) -
        uniformDifferenceDistributionMatrix A =
      (differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A) *
        deterministicDifferenceDistributionMatrix (fun x : A => L x) := by
    rw [sub_mul, uniformDifferenceDistributionMatrix_mul_addEquiv_eq]
  rw [hmatrix, matrix_norm_mul_addEquiv_differenceDistributionMatrix_eq]

variable [DecidableEq W]

/-- Under the superbox factorization, the four-round AES-style family has
exactly the same spectral bias as the independently keyed SHARK core. -/
theorem aesStyleFourRoundCore_spectralBias_eq_keyedShark
    (subBytes : State W 4 ≃ State W 4)
    (shiftRows mixColumns : State W 4 ≃+ State W 4)
    (S : W → W ≃ W)
    (hcomm : ∀ x : State W 4,
      shiftRows (subBytes x) = subBytes (shiftRows x))
    (hSuperbox : ∀ key x : State W 4,
      aesStyleSuperbox subBytes mixColumns key x = keyedSubstitute S key x) :
    ‖differenceDistributionMatrix
        (aesStyleFourRoundCore subBytes shiftRows mixColumns) -
      uniformDifferenceDistributionMatrix (State W 4)‖ =
    ‖differenceDistributionMatrix
        (keyedSharkTwoCore S (aesStyleMiddleLinearLayer shiftRows mixColumns)) -
      uniformDifferenceDistributionMatrix (State W 4)‖ := by
  rw [aesStyleFourRoundCore_differenceDistributionMatrix_eq_keyedShark_preShiftRows
    subBytes shiftRows mixColumns S hcomm hSuperbox]
  exact differenceDistributionMatrix_family_comp_addEquiv_spectralBias_eq
    (keyedSharkTwoCore S (aesStyleMiddleLinearLayer shiftRows mixColumns)) shiftRows

end PairwiseIndependence
