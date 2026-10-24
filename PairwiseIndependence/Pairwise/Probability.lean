import PairwiseIndependence.Pairwise.Composition

/-!
# From difference-distribution matrices to pairwise independence

This module contains the probability statements. The spectral estimates for
SHARK and AES belong in the linear-algebra modules; Lemmas 4 and 6 bridge them
to pairwise independence here.
-/

namespace PairwiseIndependence

variable {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
  [Fintype κ]

private theorem sum_output_whitening_key (p q y₁ y₂ : A) :
    (∑ v : A, if p + v = y₁ ∧ q + v = y₂ then 1 else 0) =
      if q = p + (y₂ - y₁) then 1 else 0 := by
  classical
  have hp (v : A) : p + v = y₁ ↔ v = y₁ - p := by
    constructor
    · intro h
      have h' := congrArg (fun z : A => z - p) h
      simpa [add_sub_assoc, add_comm] using h'
    · intro h
      rw [h]
      abel
  have heq : q + (y₁ - p) = y₂ ↔ q = p + (y₂ - y₁) := by
    constructor
    · intro h
      calc
        q = q + (y₁ - p) + (p - y₁) := by abel
        _ = p + (y₂ - y₁) := by rw [h]; abel
    · intro h
      rw [h]
      abel
  simp_rw [hp]
  calc
    (∑ v : A, if v = y₁ - p ∧ q + v = y₂ then 1 else 0) =
        ∑ v : A, if v = y₁ - p then
          (if q + (y₁ - p) = y₂ then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v = y₁ - p
      · subst v
        simp
      · simp [hv]
    _ = if q + (y₁ - p) = y₂ then 1 else 0 := by simp
    _ = _ := by simp only [heq]

private theorem sum_input_whitening_key
    (f : A → A) (x₁ x₂ b : A) :
    (∑ u : A, if f (x₂ + u) = f (x₁ + u) + b then 1 else 0) =
      differenceCount f b (x₂ - x₁) := by
  classical
  unfold differenceCount
  exact Fintype.sum_equiv (Equiv.addLeft x₁) _ _ (fun u => by
    have h : x₂ + u = (x₁ + u) + (x₂ - x₁) := by abel
    rw [h]
    rfl)

/-- The count of two output constraints after input and output whitening is
exactly the count represented by the difference-distribution matrix. -/
theorem whitenedCipher_jointCount (f : κ → A → A) (x₁ x₂ y₁ y₂ : A) :
    (∑ key : κ × A × A,
      if whitenedCipher f key x₁ = y₁ ∧ whitenedCipher f key x₂ = y₂
      then 1 else 0) =
      ∑ k : κ, differenceCount (f k) (y₂ - y₁) (x₂ - x₁) := by
  classical
  simp only [Fintype.sum_prod_type, whitenedCipher]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ u : A, ∑ v : A,
      if f k (x₁ + u) + v = y₁ ∧ f k (x₂ + u) + v = y₂
      then 1 else 0) =
        ∑ u : A,
          if f k (x₂ + u) = f k (x₁ + u) + (y₂ - y₁) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      exact sum_output_whitening_key (f k (x₁ + u)) (f k (x₂ + u)) y₁ y₂
    _ = _ := sum_input_whitening_key (f k) x₁ x₂ (y₂ - y₁)

/-- A joint output event after independent whitening is one state-size factor
times the corresponding difference-distribution entry. This is the counting
step in Lemma 4 of the paper. -/
theorem jointOutputProbability_eq_differenceDistributionMatrix
    (f : κ → A → A) (x₁ x₂ y₁ y₂ : A) :
    jointOutputProbability f x₁ x₂ y₁ y₂ =
      differenceDistributionMatrix f (y₂ - y₁) (x₂ - x₁) /
        Fintype.card A := by
  rw [differenceDistributionMatrix_eq_count]
  unfold jointOutputProbability
  simp only [Nat.cast_mul]
  have hcount :
      (∑ key : κ × A × A,
        if whitenedCipher f key x₁ = y₁ ∧ whitenedCipher f key x₂ = y₂
        then (1 : ℝ) else 0) =
      ∑ k : κ, (differenceCount (f k) (y₂ - y₁) (x₂ - x₁) : ℝ) := by
    exact_mod_cast whitenedCipher_jointCount f x₁ x₂ y₁ y₂
  rw [hcount]
  ring

private theorem pairwiseDistance_term
    (f : κ → A → A) (hf : ∀ key, Function.Injective (f key))
    (x₁ x₂ y₁ y₂ : A) (ha : x₂ - x₁ ≠ 0) :
    (if y₁ = y₂ then 0 else
      |jointOutputProbability f x₁ x₂ y₁ y₂ -
        1 / ((Fintype.card A : ℝ) * (Fintype.card A - 1))|) =
      |differenceDistributionMatrix f (y₂ - y₁) (x₂ - x₁) -
        uniformDifferenceDistributionMatrix A (y₂ - y₁) (x₂ - x₁)| /
          Fintype.card A := by
  have hcard : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨0⟩
  have hNpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast hcard
  have hNm1 : ((Fintype.card A - 1 : ℕ) : ℝ) =
      (Fintype.card A : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcard))
  by_cases hy : y₁ = y₂
  · subst y₂
    have hz : differenceDistributionMatrix f 0 (x₂ - x₁) = 0 :=
      differenceDistributionMatrix_zero_output f hf ha
    simp [hz, uniformDifferenceDistributionMatrix_apply, ha]
  · have hb : y₂ - y₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    rw [if_neg hy, jointOutputProbability_eq_differenceDistributionMatrix]
    simp only [uniformDifferenceDistributionMatrix_apply, if_neg ha, if_neg hb, hNm1]
    have halg (z : ℝ) :
        z / (Fintype.card A : ℝ) -
          1 / ((Fintype.card A : ℝ) * (Fintype.card A - 1)) =
        (z - 1 / ((Fintype.card A : ℝ) - 1)) / Fintype.card A := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [halg, abs_div, abs_of_pos hNpos]

/-- The distance for a fixed input pair is half of the corresponding column
sum of the difference-distribution matrix minus the uniform matrix. -/
theorem pairwiseDistance_eq_differenceDistributionColumn
    (f : κ → A → A) (hf : ∀ key, Function.Injective (f key))
    {x₁ x₂ : A} (hx : x₁ ≠ x₂) :
    pairwiseDistance f x₁ x₂ =
      (1 / 2 : ℝ) * ∑ b : A,
        |differenceDistributionMatrix f b (x₂ - x₁) -
          uniformDifferenceDistributionMatrix A b (x₂ - x₁)| := by
  have ha : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hN : (Fintype.card A : ℝ) ≠ 0 := by
    have hc : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast (Nat.ne_of_gt hc)
  unfold pairwiseDistance
  simp_rw [pairwiseDistance_term f hf x₁ x₂ _ _ ha]
  have hsum (y₁ : A) :
      (∑ y₂ : A,
        |differenceDistributionMatrix f (y₂ - y₁) (x₂ - x₁) -
          uniformDifferenceDistributionMatrix A (y₂ - y₁) (x₂ - x₁)| /
            Fintype.card A) =
        ∑ b : A,
          |differenceDistributionMatrix f b (x₂ - x₁) -
            uniformDifferenceDistributionMatrix A b (x₂ - x₁)| /
              Fintype.card A := by
    exact Fintype.sum_equiv (Equiv.subRight y₁) _ _ (fun y₂ => rfl)
  simp_rw [hsum]
  rw [← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hN]

private theorem differenceDistributionMatrix_sub_uniform_zero_input
    [Nonempty κ]
    (f : κ → A → A) (b : A) :
    (differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A) b 0 = 0 := by
  rw [Matrix.sub_apply, differenceDistributionMatrix_zero_input]
  by_cases hb : b = 0 <;> simp [uniformDifferenceDistributionMatrix_apply, hb]

/-- Lemma 4 of the paper. The random keyed family is assumed to consist of
permutations; the input and output whitening keys are independent and uniform.
The one norm is the maximum absolute column sum. -/
theorem lemma4_pairwiseIndependence_iff_matrixOneNorm
    [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Injective (f key))
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsPairwiseIndependent f ε ↔
      matrixOneNorm
        (differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A) ≤
          2 * ε := by
  rw [matrixOneNorm_le_iff]
  constructor
  · intro h a
    by_cases ha : a = 0
    · subst a
      have hz :
          (∑ b : A,
            |(differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A) b 0|) =
              0 := by
        apply Finset.sum_eq_zero
        intro b _
        rw [differenceDistributionMatrix_sub_uniform_zero_input]
        simp
      rw [hz]
      nlinarith
    · have hpair := h 0 a (Ne.symm ha)
      rw [pairwiseDistance_eq_differenceDistributionColumn f hf (Ne.symm ha)] at hpair
      simp only [sub_zero] at hpair
      simp only [Matrix.sub_apply]
      nlinarith
  · intro h x₁ x₂ hx
    have hsum := h (x₂ - x₁)
    rw [pairwiseDistance_eq_differenceDistributionColumn f hf hx]
    simp only [Matrix.sub_apply] at hsum
    nlinarith

end PairwiseIndependence
