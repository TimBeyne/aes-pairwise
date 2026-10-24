import PairwiseIndependence.AesBounds.SboxAffineBridge
import PairwiseIndependence.AesBounds.SboxCyclicIdentification
import PairwiseIndependence.AesBounds.Superbox
import PairwiseIndependence.KeliherSui.WideTrail

/-!
# A maximal two-round AES superbox differential

Daemen and Rijmen exhibit a differential with input `(75, 0, 0, 0)` and
output `(41/2, 41, 41, 41/3)` (hexadecimal, with field division) when the
second S-box's output affine map is omitted. Here the corresponding inverse
S-box differences are `ad, 41, 41, 3f`. The concrete AES S-box has the
output affine map in both rounds, so its output differences are the affine
images `f7, d8, d8, b7`.

The finite certificate below checks the numerator of the exact trail sum.
It provides the attained `53 / 2^34` value, separate from the global
Keliher--Sui upper-bound search.

Source: J. Daemen and V. Rijmen, *Two-Round AES Differentials*, Section 6.2,
Cryptology ePrint 2006/039.
-/

namespace PairwiseIndependence

/-- The count of first-round AES S-box solutions for input difference `75`
and output difference `t`. The affine output map permutes the inverse-byte
count table's columns. -/
def keliherSuiWitnessFirstCount (t : Fin 256) : Nat :=
  (aesInverseDifferenceCountTable[0x75]!)[
    aesByteToNat (aesAffineLinearEquiv.symm (aesByteOfNat t.val))]!

/-- The integer product of the five active byte difference counts along an
inner trail. The four second-round input differences are `(2t,t,t,3t)` under
the first column of MixColumns. -/
def keliherSuiWitnessTrailCount (t : Fin 256) : Nat :=
  let x := aesByteOfNat t.val
  keliherSuiWitnessFirstCount t *
    (aesInverseDifferenceCountTable[aesByteToNat (aesXtime x)]!)[0xad]! *
    (aesInverseDifferenceCountTable[t.val]!)[0x41]! ^ 2 *
    (aesInverseDifferenceCountTable[aesByteToNat (aesMul3 x)]!)[0x3f]!

/-- Zero contributes zero, so the 256-byte sum is equivalent to the 255
possible nonzero inner trails. -/
def keliherSuiWitnessNumerator : Nat :=
  ∑ t : Fin 256, keliherSuiWitnessTrailCount t

/-- Exact finite count for one maximal two-round AES differential:
`3392 / 256^5 = 53 / 2^34`. -/
theorem keliherSuiWitnessNumerator_eq :
    keliherSuiWitnessNumerator = 3392 := by
  native_decide

theorem keliherSuiWitnessNumerator_normalized :
    (keliherSuiWitnessNumerator : ℝ) / 256 ^ 5 =
      (53 : ℝ) / 2 ^ 34 := by
  rw [keliherSuiWitnessNumerator_eq]
  norm_num

/-- The AES one-byte difference-distribution entry, expressed as an integer
count from the certified inverse table. -/
theorem aesSbox_differenceDistributionMatrix_eq_count (a b : AesByte) :
    deterministicDifferenceDistributionMatrix aesSbox b a =
      ((aesInverseDifferenceCountTable[aesByteToNat a]!)[
        aesByteToNat (aesAffineLinearEquiv.symm b)]! : ℝ) / 256 := by
  let aa : Fin 256 := ⟨aesByteToNat a, aesByteToNat_lt a⟩
  let bb : Fin 256 :=
    ⟨aesByteToNat (aesAffineLinearEquiv.symm b),
      aesByteToNat_lt (aesAffineLinearEquiv.symm b)⟩
  rw [aesSbox_differenceDistributionMatrix_rowPermuted]
  have h := aesFieldInverse_differenceDistributionMatrix_entry aa bb
  rw [aesByteOfNat_toNat a,
      aesByteOfNat_toNat (aesAffineLinearEquiv.symm b)] at h
  exact h

/-- The actual five-factor differential trail sum for the exhibited
one-active-byte input. The second-round output differences are the affine
images of the inverse-byte differences from Daemen--Rijmen. -/
noncomputable def keliherSuiWitnessTrailSum : ℝ :=
  ∑ t : Fin 256,
    let x := aesByteOfNat t.val
    deterministicDifferenceDistributionMatrix aesSbox x (aesByteOfNat 0x75) *
      deterministicDifferenceDistributionMatrix aesSbox
        (aesAffineLinearEquiv (aesByteOfNat 0xad)) (aesXtime x) *
      (deterministicDifferenceDistributionMatrix aesSbox
        (aesAffineLinearEquiv (aesByteOfNat 0x41)) x) ^ 2 *
      deterministicDifferenceDistributionMatrix aesSbox
        (aesAffineLinearEquiv (aesByteOfNat 0x3f)) (aesMul3 x)

/-- The exhibited trail sum attains `53/2^34`. This is the lower-bound
half of the exact Keliher--Sui value. -/
theorem keliherSuiWitnessTrailSum_eq :
    keliherSuiWitnessTrailSum = (53 : ℝ) / 2 ^ 34 := by
  have hpoint (t : Fin 256) :
      let x := aesByteOfNat t.val
      deterministicDifferenceDistributionMatrix aesSbox x (aesByteOfNat 0x75) *
        deterministicDifferenceDistributionMatrix aesSbox
          (aesAffineLinearEquiv (aesByteOfNat 0xad)) (aesXtime x) *
        (deterministicDifferenceDistributionMatrix aesSbox
          (aesAffineLinearEquiv (aesByteOfNat 0x41)) x) ^ 2 *
        deterministicDifferenceDistributionMatrix aesSbox
          (aesAffineLinearEquiv (aesByteOfNat 0x3f)) (aesMul3 x) =
      (keliherSuiWitnessTrailCount t : ℝ) / 256 ^ 5 := by
    dsimp only
    rw [aesSbox_differenceDistributionMatrix_eq_count,
      aesSbox_differenceDistributionMatrix_eq_count,
      aesSbox_differenceDistributionMatrix_eq_count,
      aesSbox_differenceDistributionMatrix_eq_count]
    simp only [aesAffineLinearEquiv.symm_apply_apply, aesByteToNat_ofNat]
    norm_num only [show aesByteToNat (aesByteOfNat 0x75) = 0x75 by decide,
      show aesByteToNat (aesByteOfNat 0xad) = 0xad by decide,
      show aesByteToNat (aesByteOfNat 0x41) = 0x41 by decide,
      show aesByteToNat (aesByteOfNat 0x3f) = 0x3f by decide]
    dsimp only [keliherSuiWitnessTrailCount, keliherSuiWitnessFirstCount]
    push_cast
    ring
  calc
    keliherSuiWitnessTrailSum =
        (keliherSuiWitnessNumerator : ℝ) / 256 ^ 5 := by
      unfold keliherSuiWitnessTrailSum keliherSuiWitnessNumerator
      simp_rw [hpoint]
      rw [← Finset.sum_div]
      simp only [Nat.cast_sum]
    _ = (53 : ℝ) / 2 ^ 34 := keliherSuiWitnessNumerator_normalized

/-- The independent-middle-key two-round SHARK matrix entry is the exact
sum of products of its eight constituent one-byte differential entries.
This version uses a fixed S-box, as in the AES superbox. -/
theorem sharkTwoCore_differenceDistributionMatrix_apply_eq_graphProduct
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (S : A ≃ A) (L : State A 4 ≃+ State A 4) (a b : State A 4) :
    differenceDistributionMatrix (sharkTwoCore S L) b a =
      ∑ x : State A 4,
        ∏ j : Sum (Fin 4) (Fin 4),
          (Sum.elim
            (fun i z => deterministicDifferenceDistributionMatrix S z (a i))
            (fun i z => deterministicDifferenceDistributionMatrix S (b i) z)
            j) (mdsGraphCoordinate L x j) := by
  classical
  rw [sharkTwoCore_differenceDistributionMatrix,
    substitute_differenceDistributionMatrix_eq_tensorWordMatrix]
  have hM (y x : State A 4) :
      deterministicDifferenceDistributionMatrix (fun z : State A 4 => L z) y x =
        if L x = y then 1 else 0 :=
    deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom y x
  simp only [Matrix.mul_apply]
  simp_rw [hM]
  simp [tensorWordMatrix, mdsGraphCoordinate, Fintype.prod_sum_type, mul_comm]

private theorem sum_onehot_four
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (F : State A 4 → ℝ) :
    (∑ x : State A 4,
      if x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 then F x else 0) =
      ∑ t : A, F ![t, 0, 0, 0] := by
  classical
  let e : State A 4 ≃ A × A × A × A :=
    { toFun := fun x => (x 0, x 1, x 2, x 3)
      invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
      left_inv := by
        intro x
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro p
        rcases p with ⟨a, b, c, d⟩
        rfl }
  calc
    _ = ∑ p : A × A × A × A,
        if p.2.1 = 0 ∧ p.2.2.1 = 0 ∧ p.2.2.2 = 0
        then F (e.symm p) else 0 := by
          apply Fintype.sum_equiv e
          intro x
          have hv : ![x 0, x 1, x 2, x 3] = x := by
            funext i
            fin_cases i <;> rfl
          simp [e, hv]
    _ = ∑ t : A, F ![t, 0, 0, 0] := by
          simp [Fintype.sum_prod_type, ite_and, e]

/-- With only the first input byte active, the superbox's intermediate
difference has the form `(t,0,0,0)`. Thus the 32-bit matrix entry reduces
exactly to a 256-term sum. -/
theorem sharkTwoCore_differenceDistributionMatrix_onehot
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (S : A ≃ A) (L : State A 4 ≃+ State A 4)
    (u : A) (b : State A 4) :
    differenceDistributionMatrix (sharkTwoCore S L) b ![u, 0, 0, 0] =
      ∑ t : A,
        deterministicDifferenceDistributionMatrix S t u *
          ∏ i : Fin 4,
            deterministicDifferenceDistributionMatrix S (b i)
              (L ![t, 0, 0, 0] i) := by
  classical
  rw [sharkTwoCore_differenceDistributionMatrix_apply_eq_graphProduct]
  have hzero (z : A) :
      deterministicDifferenceDistributionMatrix S z 0 =
        if z = 0 then 1 else 0 := by
    simpa only [deterministicDifferenceDistributionMatrix] using
      (differenceDistributionMatrix_zero_input
        (fun _ : Unit => fun x : A => S x) z)
  have hterm (x : State A 4) :
      (∏ j : Sum (Fin 4) (Fin 4),
        (Sum.elim
          (fun i z => deterministicDifferenceDistributionMatrix S z (![u, 0, 0, 0] i))
          (fun i z => deterministicDifferenceDistributionMatrix S (b i) z)
          j) (mdsGraphCoordinate L x j)) =
        if x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 then
          deterministicDifferenceDistributionMatrix S (x 0) u *
            ∏ i : Fin 4,
              deterministicDifferenceDistributionMatrix S (b i) (L x i)
        else 0 := by
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four,
      mdsGraphCoordinate, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [show (![u, 0, 0, 0] : State A 4) 2 = 0 by rfl,
      show (![u, 0, 0, 0] : State A 4) 3 = 0 by rfl]
    simp only [hzero]
    by_cases h1 : x 1 = 0 <;> by_cases h2 : x 2 = 0 <;>
      by_cases h3 : x 3 = 0 <;> simp only [h1, h2, h3, ite_true,
        ite_false, and_true, and_false, mul_one, mul_zero,
        zero_mul]
  simp_rw [hterm]
  exact sum_onehot_four _

/-- Daemen--Rijmen's maximal input difference, in the byte order of this
formalization. -/
def keliherSuiWitnessInput : State AesByte 4 :=
  ![aesByteOfNat 0x75, 0, 0, 0]

/-- The corresponding output difference for the full AES S-box in the
second round. The published inverse-only output differences are transformed
by the affine output layer. -/
def keliherSuiWitnessOutput : State AesByte 4 :=
  ![aesAffineLinearEquiv (aesByteOfNat 0xad),
    aesAffineLinearEquiv (aesByteOfNat 0x41),
    aesAffineLinearEquiv (aesByteOfNat 0x41),
    aesAffineLinearEquiv (aesByteOfNat 0x3f)]

theorem keliherSuiWitnessInput_ne_zero : keliherSuiWitnessInput ≠ 0 := by
  native_decide

private theorem aesMixColumn_onehot (t : AesByte) :
    aesMixColumnEquiv ![t, 0, 0, 0] =
      ![aesXtime t, t, t, aesMul3 t] := by
  funext i
  have htwo : aesXtime (0 : AesByte) = 0 := by decide
  have hthree : aesMul3 (0 : AesByte) = 0 := by simp [aesMul3, htwo]
  fin_cases i <;> simp [aesMixColumnEquiv, aesMixColumn, htwo, hthree]

/-- The concrete independently keyed AES superbox attains the claimed
two-round value. This establishes the lower bound; the global upper bound
over all input/output differences remains the Keliher--Sui search problem. -/
theorem keliherSui_twoRoundEstimate_attained :
    differenceDistributionMatrix
      (fun key : State AesByte 4 => fun x => aesIndependentSuperbox key x)
      keliherSuiWitnessOutput keliherSuiWitnessInput =
        (53 : ℝ) / 2 ^ 34 := by
  rw [aesIndependentSuperbox_differenceDistributionMatrix_eq_sharkTwoCore]
  unfold keliherSuiWitnessInput keliherSuiWitnessOutput
  rw [sharkTwoCore_differenceDistributionMatrix_onehot]
  calc
    (∑ t : AesByte,
        deterministicDifferenceDistributionMatrix aesSboxEquiv t
            (aesByteOfNat 0x75) *
          ∏ i : Fin 4,
            deterministicDifferenceDistributionMatrix aesSboxEquiv
              (![aesAffineLinearEquiv (aesByteOfNat 0xad),
                aesAffineLinearEquiv (aesByteOfNat 0x41),
                aesAffineLinearEquiv (aesByteOfNat 0x41),
                aesAffineLinearEquiv (aesByteOfNat 0x3f)] i)
              (aesMixColumnEquiv ![t, 0, 0, 0] i)) =
        keliherSuiWitnessTrailSum := by
          unfold keliherSuiWitnessTrailSum
          symm
          apply Fintype.sum_equiv aesByteFinEquiv
          intro t
          simp only [aesByteFinEquiv, Equiv.coe_fn_mk,
            aesMixColumn_onehot, Fin.prod_univ_four]
          simp [aesSboxEquiv]
          ring
    _ = (53 : ℝ) / 2 ^ 34 := keliherSuiWitnessTrailSum_eq

end PairwiseIndependence
