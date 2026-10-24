import PairwiseIndependence.Pairwise.Probability
import PairwiseIndependence.Pairwise.Conversion
import PairwiseIndependence.Pairwise.RepeatedBlocks

/-!
# Pairwise independence of iterated blocks

The final step of Corollary 2 for any keyed block: a two-norm bound and a
bound on the nonzero-input entries of its difference-distribution matrix give
pairwise independence of `r + 1` independently keyed copies, by Lemmas 4 and 6.
A fixed linear layer after each block changes neither bound.
The matrix-power identity is proved in `Pairwise/RepeatedBlocks.lean`.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

/-- The Lemma 4/Lemma 6 deduction behind Corollary 2 for `r + 1` repeated
independently keyed blocks, each a complete block including its last linear
layer. The bound is `2^14 * 2^(-39r)`. For the paper's Theorem 5 core, which
stops after SubBytes, use `corollary2_of_fourRoundCore_estimates`. -/
theorem corollary2_of_fourRoundAES_estimates
    {A κ : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (fourRoundAES : κ → A → A)
    (hfour : ∀ key, Function.Bijective (fourRoundAES key))
    (hcard : Fintype.card A = 2 ^ 128)
    (hTheorem5 :
      ‖differenceDistributionMatrix fourRoundAES -
        uniformDifferenceDistributionMatrix A‖ ≤ 1 / (2 : ℝ) ^ 39)
    (hKeliherSui :
      ∀ a b : A, a ≠ 0 →
        differenceDistributionMatrix fourRoundAES b a ≤ 1 / (2 : ℝ) ^ 113)
    (r : ℕ) :
    IsPairwiseIndependent (repeatedBlocks fourRoundAES r)
      ((2 : ℝ) ^ 14 * (1 / (2 : ℝ) ^ 39) ^ r) := by
  have hε : 0 ≤ (2 : ℝ) ^ 14 * (1 / (2 : ℝ) ^ 39) ^ r := by positivity
  apply (lemma4_pairwiseIndependence_iff_matrixOneNorm
    (repeatedBlocks fourRoundAES r)
    (fun key => (repeatedBlocks_bijective fourRoundAES hfour r key).1)
    _ hε).mpr
  rw [repeatedBlocks_differenceDistributionMatrix]
  have hbound := conversion_power fourRoundAES hfour
    (1 / (2 : ℝ) ^ 113) (1 / (2 : ℝ) ^ 39)
    (by positivity) hKeliherSui hTheorem5 r
  have hnum : (Fintype.card A : ℝ) * (1 / (2 : ℝ) ^ 113) =
      (2 : ℝ) ^ 15 := by
    rw [hcard]
    norm_num
  rw [hnum] at hbound
  convert hbound using 1; ring

/-! ### Linear layers between blocks

A four-round AES block in the paper's Theorem 5 ends after SubBytes. The
remaining linear layer of its fourth round must be inserted before the next
block. The following statements show that such a layer leaves both
estimates and pairwise independence unchanged. -/

section LinearLayer

variable {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] [Fintype κ]

/-- An additive permutation after a keyed family permutes the output-difference
rows of its difference-distribution matrix. -/
theorem differenceDistributionMatrix_addEquiv_comp_apply
    (f : κ → A → A) (L : A ≃+ A) (b a : A) :
    differenceDistributionMatrix (fun key x => L (f key x)) b a =
      differenceDistributionMatrix f (L.symm b) a := by
  rw [differenceDistributionMatrix_eq_count, differenceDistributionMatrix_eq_count]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  unfold differenceCount
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hb : L (f k x) + b = L (f k x + L.symm b) := by
    rw [map_add, L.apply_symm_apply]
  have hiff : L (f k (x + a)) = L (f k x) + b ↔ f k (x + a) = f k x + L.symm b := by
    rw [hb]
    exact L.injective.eq_iff
  by_cases h : f k (x + a) = f k x + L.symm b
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- The uniform benchmark has the same output-difference rows after an additive
permutation, because the permutation fixes zero. -/
theorem uniformDifferenceDistributionMatrix_symm_apply (L : A ≃+ A) (b a : A) :
    uniformDifferenceDistributionMatrix A (L.symm b) a =
      uniformDifferenceDistributionMatrix A b a := by
  have hb : L.symm b = 0 ↔ b = 0 := by
    constructor
    · intro h
      simpa using congrArg L h
    · intro h
      simp [h]
  by_cases ha : a = 0 <;> by_cases hb0 : b = 0 <;>
    simp [uniformDifferenceDistributionMatrix_apply, ha, hb0, hb]

/-- The centered matrix after an additive permutation is the row-permuted
centered matrix. -/
theorem differenceDistributionMatrix_addEquiv_comp_sub_uniform_apply
    (f : κ → A → A) (L : A ≃+ A) (b a : A) :
    (differenceDistributionMatrix (fun key x => L (f key x)) -
        uniformDifferenceDistributionMatrix A) b a =
      (differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A)
        (L.symm b) a := by
  rw [Matrix.sub_apply, Matrix.sub_apply,
    differenceDistributionMatrix_addEquiv_comp_apply,
    uniformDifferenceDistributionMatrix_symm_apply]

omit [AddCommGroup A] in
/-- Row permutations preserve the Euclidean operator norm. -/
theorem matrix_norm_submatrix_row_equiv (M : Matrix A A ℝ) (e : A ≃ A) :
    ‖M.submatrix e id‖ = ‖M‖ := by
  let P : Matrix A A ℝ := e.toPEquiv.toMatrix
  let Q : Matrix A A ℝ := e.symm.toPEquiv.toMatrix
  have hP : P * M = M.submatrix e id := PEquiv.toMatrix_toPEquiv_mul e M
  have hQP : Q * (P * M) = M := by
    rw [hP]
    simp [Q, PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_submatrix]
  have hPnorm : ‖P‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le e
  have hQnorm : ‖Q‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le e.symm
  rw [← hP]
  apply le_antisymm
  · calc
      ‖P * M‖ ≤ ‖P‖ * ‖M‖ := norm_mul_le P M
      _ ≤ 1 * ‖M‖ := mul_le_mul_of_nonneg_right hPnorm (norm_nonneg M)
      _ = ‖M‖ := one_mul _
  · calc
      ‖M‖ = ‖Q * (P * M)‖ := by rw [hQP]
      _ ≤ ‖Q‖ * ‖P * M‖ := norm_mul_le Q (P * M)
      _ ≤ 1 * ‖P * M‖ := mul_le_mul_of_nonneg_right hQnorm (norm_nonneg _)
      _ = ‖P * M‖ := one_mul _

/-- The paper's two-norm `‖D − U‖` is unchanged by an additive permutation
after the family. -/
theorem differenceDistributionMatrix_addEquiv_comp_spectralBias_eq
    (f : κ → A → A) (L : A ≃+ A) :
    ‖differenceDistributionMatrix (fun key x => L (f key x)) -
        uniformDifferenceDistributionMatrix A‖ =
      ‖differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A‖ := by
  have hmatrix :
      differenceDistributionMatrix (fun key x => L (f key x)) -
          uniformDifferenceDistributionMatrix A =
        (differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A).submatrix
          L.symm.toEquiv id := by
    ext b a
    exact differenceDistributionMatrix_addEquiv_comp_sub_uniform_apply f L b a
  rw [hmatrix, matrix_norm_submatrix_row_equiv]

omit [DecidableEq A] in
/-- Row permutations preserve the matrix one norm. -/
theorem matrixOneNorm_eq_of_row_equiv (M N : Matrix A A ℝ) (e : A ≃ A)
    (h : ∀ b a, N b a = M (e b) a) :
    matrixOneNorm N = matrixOneNorm M := by
  have hcol (a : A) : (∑ b : A, |N b a|) = ∑ b : A, |M b a| := by
    simp only [h]
    exact Fintype.sum_equiv e _ _ (fun b => rfl)
  apply le_antisymm
  · rw [matrixOneNorm_le_iff]
    intro a
    rw [hcol]
    exact (matrixOneNorm_le_iff M _).mp le_rfl a
  · rw [matrixOneNorm_le_iff]
    intro a
    rw [← hcol]
    exact (matrixOneNorm_le_iff N _).mp le_rfl a

/-- Pairwise independence with output whitening is unchanged by a fixed
additive permutation of the output. -/
theorem isPairwiseIndependent_addEquiv_comp_iff [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Injective (f key))
    (L : A ≃+ A) (ε : ℝ) (hε : 0 ≤ ε) :
    IsPairwiseIndependent (fun key x => L (f key x)) ε ↔
      IsPairwiseIndependent f ε := by
  rw [lemma4_pairwiseIndependence_iff_matrixOneNorm (fun key x => L (f key x))
      (fun key => L.injective.comp (hf key)) ε hε,
    lemma4_pairwiseIndependence_iff_matrixOneNorm f hf ε hε,
    matrixOneNorm_eq_of_row_equiv _ _ L.symm.toEquiv
      (differenceDistributionMatrix_addEquiv_comp_sub_uniform_apply f L)]

/-- An independent uniform key added to the output does not change the
difference-distribution matrix. -/
theorem differenceDistributionMatrix_add_key (f : κ → A → A) :
    differenceDistributionMatrix (fun (key : κ × A) x => f key.1 x + key.2) =
      differenceDistributionMatrix f := by
  ext b a
  rw [differenceDistributionMatrix_eq_count, differenceDistributionMatrix_eq_count]
  have hcount (key : κ × A) :
      differenceCount (fun x => f key.1 x + key.2) b a = differenceCount (f key.1) b a := by
    unfold differenceCount
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hiff : f key.1 (x + a) + key.2 = f key.1 x + key.2 + b ↔
        f key.1 (x + a) = f key.1 x + b := by
      rw [add_right_comm (f key.1 x) key.2 b]
      exact add_left_inj _
    by_cases h : f key.1 (x + a) = f key.1 x + b
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  simp_rw [hcount]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
    Nat.cast_mul, ← Finset.mul_sum]
  have hA : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_comm ((Fintype.card κ : ℝ) * Fintype.card A) (Fintype.card A : ℝ),
    mul_div_mul_left _ _ hA]

/-- Pairwise independence depends on the key only through its uniform
distribution, so a bijective regrouping of the keys does not change it. -/
theorem isPairwiseIndependent_key_reindex {ι : Type*} [Fintype ι] [Nonempty ι]
    [Nonempty κ] (e : κ ≃ ι) (f : ι → A → A) (hf : ∀ key, Function.Injective (f key))
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsPairwiseIndependent (fun key => f (e key)) ε ↔ IsPairwiseIndependent f ε := by
  rw [lemma4_pairwiseIndependence_iff_matrixOneNorm (fun key => f (e key))
      (fun key => hf (e key)) ε hε,
    lemma4_pairwiseIndependence_iff_matrixOneNorm f hf ε hε,
    differenceDistributionMatrix_key_reindex]

end LinearLayer

/-- Corollary 2's deduction when each repeated block is a four-round core
followed by the linear layer `L` of its last round. Both hypotheses concern
the core, as in Theorem 5 and the Keliher--Sui estimate. -/
theorem corollary2_of_fourRoundCore_estimates
    {A κ : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (core : κ → A → A)
    (hcore : ∀ key, Function.Bijective (core key))
    (L : A ≃+ A)
    (hcard : Fintype.card A = 2 ^ 128)
    (hTheorem5 :
      ‖differenceDistributionMatrix core -
        uniformDifferenceDistributionMatrix A‖ ≤ 1 / (2 : ℝ) ^ 39)
    (hKeliherSui :
      ∀ a b : A, a ≠ 0 →
        differenceDistributionMatrix core b a ≤ 1 / (2 : ℝ) ^ 113)
    (r : ℕ) :
    IsPairwiseIndependent (repeatedBlocks (fun key x => L (core key x)) r)
      ((2 : ℝ) ^ 14 * (1 / (2 : ℝ) ^ 39) ^ r) :=
  corollary2_of_fourRoundAES_estimates (fun key x => L (core key x))
    (fun key => L.bijective.comp (hcore key)) hcard
    (by rw [differenceDistributionMatrix_addEquiv_comp_spectralBias_eq]; exact hTheorem5)
    (fun a b ha => by
      rw [differenceDistributionMatrix_addEquiv_comp_apply]
      exact hKeliherSui a _ ha)
    r

end PairwiseIndependence
