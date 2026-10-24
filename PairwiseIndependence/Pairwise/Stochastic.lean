import PairwiseIndependence.Pairwise.Composition
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Stochastic identities for difference-distribution matrices

These identities hold for keyed permutations and justify centering a product
around the difference-distribution matrix of a uniform permutation.
-/

namespace PairwiseIndependence

open scoped Matrix.Norms.L2Operator

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

private theorem differenceCount_column_sum (f : A → A) (a : A) :
    (∑ b : A, differenceCount f b a) = Fintype.card A := by
  classical
  simp only [differenceCount]
  rw [Finset.sum_comm]
  have hsingle (x : A) :
      (∑ b : A, if f (x + a) = f x + b then 1 else 0) = 1 := by
    have hp (b : A) : f (x + a) = f x + b ↔ b = f (x + a) - f x := by
      constructor
      · intro h
        rw [h]
        simp
      · intro h
        rw [h]
        simp
    simp [hp]
  simp_rw [hsingle]
  simp

private theorem differenceCount_row_sum (f : A → A)
    (hf : Function.Bijective f) (b : A) :
    (∑ a : A, differenceCount f b a) = Fintype.card A := by
  classical
  simp only [differenceCount]
  rw [Finset.sum_comm]
  have hsingle (x : A) :
      (∑ a : A, if f (x + a) = f x + b then 1 else 0) = 1 := by
    let e : A ≃ A := (Equiv.addLeft x).trans (Equiv.ofBijective f hf)
    calc
      _ = ∑ y : A, if y = f x + b then 1 else 0 :=
        Fintype.sum_equiv e _ _ (fun a => rfl)
      _ = 1 := by simp
  simp_rw [hsingle]
  simp

/-- Every input-difference column sums to one, even for non-bijective maps. -/
theorem differenceDistributionMatrix_column_sum
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (a : A) :
    (∑ b : A, differenceDistributionMatrix f b a) = 1 := by
  simp_rw [differenceDistributionMatrix_eq_count]
  rw [← Finset.sum_div, Finset.sum_comm]
  have hcount (key : κ) :
      (∑ b : A, (differenceCount (f key) b a : ℝ)) = Fintype.card A := by
    exact_mod_cast differenceCount_column_sum (f key) a
  simp_rw [hcount]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hκ : (Fintype.card κ : ℝ) ≠ 0 := by
    have hc : 0 < Fintype.card κ := Fintype.card_pos
    exact_mod_cast (Nat.ne_of_gt hc)
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    have hc : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast (Nat.ne_of_gt hc)
  field_simp [hκ, hA]

/-- For a family of permutations, every output-difference row also sums to one. -/
theorem differenceDistributionMatrix_row_sum
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key)) (b : A) :
    (∑ a : A, differenceDistributionMatrix f b a) = 1 := by
  simp_rw [differenceDistributionMatrix_eq_count]
  rw [← Finset.sum_div, Finset.sum_comm]
  have hcount (key : κ) :
      (∑ a : A, (differenceCount (f key) b a : ℝ)) = Fintype.card A := by
    exact_mod_cast differenceCount_row_sum (f key) (hf key) b
  simp_rw [hcount]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hκ : (Fintype.card κ : ℝ) ≠ 0 := by
    have hc : 0 < Fintype.card κ := Fintype.card_pos
    exact_mod_cast (Nat.ne_of_gt hc)
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    have hc : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast (Nat.ne_of_gt hc)
  field_simp [hκ, hA]

/-- A keyed family of permutations has a doubly stochastic
difference-distribution matrix. -/
theorem differenceDistributionMatrix_mem_doublyStochastic
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key)) :
    differenceDistributionMatrix f ∈ doublyStochastic ℝ A := by
  classical
  rw [mem_doublyStochastic_iff_sum]
  exact ⟨differenceDistributionMatrix_nonneg f,
    differenceDistributionMatrix_row_sum f hf,
    differenceDistributionMatrix_column_sum f⟩

/-- The Euclidean operator norm of a permutation family's
difference-distribution matrix is at most one. -/
theorem differenceDistributionMatrix_norm_le_one
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key)) :
    ‖differenceDistributionMatrix f‖ ≤ 1 :=
  Matrix.l2_opNorm_le_one_of_mem_doublyStochastic
    (differenceDistributionMatrix_mem_doublyStochastic f hf)

/-- Split a finite sum into its zero and nonzero indices. -/
theorem sum_except_zero (v : A → ℝ) :
    (∑ x : A, if x = 0 then 0 else v x) = (∑ x : A, v x) - v 0 := by
  have h : (∑ x : A, if x = 0 then 0 else v x) + v 0 = ∑ x : A, v x := by
    calc
      _ = (∑ x : A, if x = 0 then 0 else v x) +
          ∑ x : A, if x = 0 then v 0 else 0 := by simp
      _ = ∑ x : A,
          ((if x = 0 then 0 else v x) +
            (if x = 0 then v 0 else 0)) := by rw [Finset.sum_add_distrib]
      _ = ∑ x : A, v x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = 0 <;> simp [hx]
  linarith

private theorem matrix_mul_uniform_of_row_sum
    (D : Matrix A A ℝ)
    (hzero : ∀ b : A, D b 0 = if b = 0 then 1 else 0)
    (hrow : ∀ b : A, (∑ a : A, D b a) = 1) :
    D * uniformDifferenceDistributionMatrix A = uniformDifferenceDistributionMatrix A := by
  ext b a
  rw [Matrix.mul_apply]
  by_cases ha : a = 0
  · subst a
    simp [uniformDifferenceDistributionMatrix_apply, hzero b]
  · have hterm (d : A) :
        D b d * uniformDifferenceDistributionMatrix A d a =
          if d = 0 then 0 else
            D b d / ((Fintype.card A - 1 : ℕ) : ℝ) := by
      by_cases hd : d = 0 <;> simp [uniformDifferenceDistributionMatrix_apply, ha, hd,
        div_eq_mul_inv]
    simp_rw [hterm]
    rw [sum_except_zero, ← Finset.sum_div, hrow b]
    by_cases hb : b = 0
    · subst b
      simp [hzero, uniformDifferenceDistributionMatrix_apply, ha]
    · simp [hzero b, hb, uniformDifferenceDistributionMatrix_apply, ha]

private theorem uniform_mul_matrix_of_column_sum
    (D : Matrix A A ℝ)
    (hzero : ∀ a : A, D 0 a = if a = 0 then 1 else 0)
    (hcol : ∀ a : A, (∑ b : A, D b a) = 1) :
    uniformDifferenceDistributionMatrix A * D = uniformDifferenceDistributionMatrix A := by
  ext b a
  rw [Matrix.mul_apply]
  by_cases hb : b = 0
  · subst b
    simp [uniformDifferenceDistributionMatrix_apply, hzero a]
  · have hterm (d : A) :
        uniformDifferenceDistributionMatrix A b d * D d a =
          if d = 0 then 0 else
            D d a / ((Fintype.card A - 1 : ℕ) : ℝ) := by
      by_cases hd : d = 0 <;> simp [uniformDifferenceDistributionMatrix_apply, hb, hd,
        div_eq_mul_inv, mul_comm]
    simp_rw [hterm]
    rw [sum_except_zero, ← Finset.sum_div, hcol a]
    by_cases ha : a = 0
    · subst a
      simp [hzero, uniformDifferenceDistributionMatrix_apply, hb]
    · simp [hzero a, ha, uniformDifferenceDistributionMatrix_apply, hb]

private theorem uniformDifferenceDistributionMatrix_row_sum (b : A) :
    (∑ a : A, uniformDifferenceDistributionMatrix A b a) = 1 := by
  by_cases hb : b = 0
  · subst b
    simp [uniformDifferenceDistributionMatrix_apply]
  · have hterm (a : A) :
        uniformDifferenceDistributionMatrix A b a =
          if a = 0 then 0 else
            1 / ((Fintype.card A - 1 : ℕ) : ℝ) := by
      by_cases ha : a = 0 <;> simp [uniformDifferenceDistributionMatrix_apply, hb, ha]
    simp_rw [hterm]
    rw [sum_except_zero]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : 1 < Fintype.card A :=
      Fintype.one_lt_card_iff.mpr ⟨0, b, Ne.symm hb⟩
    have hm : ((Fintype.card A - 1 : ℕ) : ℝ) =
        (Fintype.card A : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub (Nat.le_of_lt hcard)
    have hmne : ((Fintype.card A : ℝ) - 1) ≠ 0 := by
      have hr : (1 : ℝ) < Fintype.card A := by exact_mod_cast hcard
      linarith
    rw [hm]
    field_simp [hmne]

/-- The uniform difference-distribution matrix is a projection. -/
theorem uniformDifferenceDistributionMatrix_mul_self :
    uniformDifferenceDistributionMatrix A * uniformDifferenceDistributionMatrix A =
      uniformDifferenceDistributionMatrix A := by
  apply matrix_mul_uniform_of_row_sum
  · intro b
    simp [uniformDifferenceDistributionMatrix_apply]
  · exact uniformDifferenceDistributionMatrix_row_sum

/-- The uniform difference-distribution matrix is stationary on the right of
the difference-distribution matrix of a keyed permutation family. -/
theorem differenceDistributionMatrix_mul_uniform
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key)) :
    differenceDistributionMatrix f * uniformDifferenceDistributionMatrix A =
      uniformDifferenceDistributionMatrix A := by
  apply matrix_mul_uniform_of_row_sum
  · intro b
    exact differenceDistributionMatrix_zero_input f b
  · exact differenceDistributionMatrix_row_sum f hf

/-- The uniform difference-distribution matrix is stationary on the left of
the difference-distribution matrix of a keyed permutation family. -/
theorem uniform_mul_differenceDistributionMatrix
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key)) :
    uniformDifferenceDistributionMatrix A * differenceDistributionMatrix f =
      uniformDifferenceDistributionMatrix A := by
  apply uniform_mul_matrix_of_column_sum
  · intro a
    by_cases ha : a = 0
    · subst a
      simp [differenceDistributionMatrix_zero_input]
    · simp [ha, differenceDistributionMatrix_zero_output f
        (fun key => (hf key).1) ha]
  · exact differenceDistributionMatrix_column_sum f

/-- Centering a product of difference-distribution matrices factors the
product into centered matrices. -/
theorem differenceDistributionMatrix_product_centering
    {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (f : κ → A → A) (g : ι → A → A)
    (hf : ∀ key, Function.Bijective (f key))
    (hg : ∀ key, Function.Bijective (g key)) :
    differenceDistributionMatrix g * differenceDistributionMatrix f -
        uniformDifferenceDistributionMatrix A =
      (differenceDistributionMatrix g - uniformDifferenceDistributionMatrix A) *
        (differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A) := by
  have h1 := differenceDistributionMatrix_mul_uniform g hg
  have h2 := uniform_mul_differenceDistributionMatrix f hf
  have h3 := uniformDifferenceDistributionMatrix_mul_self (A := A)
  rw [sub_mul, mul_sub, mul_sub, h1, h2, h3]
  abel

private theorem uniform_nonzero_entry_le_maxDifferenceProbability
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key))
    (p : ℝ)
    (hmax : ∀ a b : A, a ≠ 0 → differenceDistributionMatrix f b a ≤ p)
    {a : A} (ha : a ≠ 0) :
    1 / ((Fintype.card A - 1 : ℕ) : ℝ) ≤ p := by
  have hcol := differenceDistributionMatrix_column_sum f a
  have hzero := differenceDistributionMatrix_zero_output f
    (fun key => (hf key).1) ha
  have hbound :
      (∑ b : A, differenceDistributionMatrix f b a) ≤
        ∑ b : A, if b = 0 then (0 : ℝ) else p := by
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : b = 0
    · subst b
      simp [hzero]
    · simpa [hb] using hmax a b ha
  rw [hcol, sum_except_zero] at hbound
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hbound
  have hcard : 1 < Fintype.card A :=
    Fintype.one_lt_card_iff.mpr ⟨0, a, Ne.symm ha⟩
  have hm : ((Fintype.card A - 1 : ℕ) : ℝ) =
      (Fintype.card A : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (Nat.le_of_lt hcard)
  have hmpos : (0 : ℝ) < ((Fintype.card A - 1 : ℕ) : ℝ) := by
    rw [hm]
    have hc : (1 : ℝ) < Fintype.card A := by exact_mod_cast hcard
    linarith
  apply (div_le_iff₀ hmpos).mpr
  rw [hm]
  nlinarith

/-- If `p` bounds every nonzero input-difference transition, it also bounds
each entry of the centered difference-distribution matrix. -/
theorem centeredDifferenceDistributionMatrix_entry_bound
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (hf : ∀ key, Function.Bijective (f key))
    (p : ℝ) (hp : 0 ≤ p)
    (hmax : ∀ a b : A, a ≠ 0 → differenceDistributionMatrix f b a ≤ p)
    (b a : A) :
    |(differenceDistributionMatrix f - uniformDifferenceDistributionMatrix A) b a| ≤ p := by
  rw [Matrix.sub_apply]
  by_cases ha : a = 0
  · subst a
    rw [differenceDistributionMatrix_zero_input]
    by_cases hb : b = 0 <;>
      simp [uniformDifferenceDistributionMatrix_apply, hb, hp]
  · by_cases hb : b = 0
    · subst b
      rw [differenceDistributionMatrix_zero_output f
        (fun key => (hf key).1) ha]
      simp [uniformDifferenceDistributionMatrix_apply, ha, hp]
    · have hU : uniformDifferenceDistributionMatrix A b a =
          1 / ((Fintype.card A - 1 : ℕ) : ℝ) := by
        simp [uniformDifferenceDistributionMatrix_apply, ha, hb]
      rw [hU]
      have hDnonneg := differenceDistributionMatrix_nonneg f b a
      have hDle := hmax a b ha
      have hUle := uniform_nonzero_entry_le_maxDifferenceProbability
        f hf p hmax ha
      have hUpos : (0 : ℝ) ≤
          1 / ((Fintype.card A - 1 : ℕ) : ℝ) := by positivity
      apply abs_le.mpr
      constructor <;> linarith

end PairwiseIndependence
