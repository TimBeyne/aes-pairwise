import PairwiseIndependence.Pairwise.Activity

/-!
# Theorem 4: numerical assembly of the AES superbox estimates

This file formalizes the last step of the paper's Theorem 4. Its four block
estimates from Sections 5 and 6 are explicit hypotheses. The bound uses the
sharp two-by-two block comparison and exact rational certificates.
-/

namespace PairwiseIndependence
open scoped Matrix.Norms.L2Operator

private theorem theorem4_scalar_rational_bound (a b : ℝ) :
    ((9571 : ℝ) / 100000000 * a + 43161 / 100000000 * b) ^ 2 +
      (43161 / 100000000 * a + 64519 / 100000000 * b) ^ 2 ≤
        (88250 / 100000000 : ℝ) ^ 2 * (a ^ 2 + b ^ 2) := by
  have hmain : 0 ≤ (5833586538 : ℝ) * a ^ 2 -
      2 * 3197798490 * a * b + 1762489218 * b ^ 2 := by
    have h1 : 0 ≤ ((5833586538 : ℝ) * a - 3197798490 * b) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (55718192848667184 : ℝ) * b ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg b)
    nlinarith
  nlinarith

open scoped Matrix.Norms.L2Operator in
theorem theorem4_superbox_of_rational_block_bounds
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {n : ℕ}
    (D : Matrix (State A n) (State A n) ℝ)
    (h₀₀ : ‖activityTruncatedOperator
      (D - uniformDifferenceDistributionMatrix (State A n))‖ ≤
        (9571 : ℝ) / 100000000)
    (h₀₁ : ‖activityComplementToActivityOperator
      (D - uniformDifferenceDistributionMatrix (State A n))‖ ≤
        (43161 : ℝ) / 100000000)
    (h₁₀ : ‖activityToComplementOperator
      (D - uniformDifferenceDistributionMatrix (State A n))‖ ≤
        (43161 : ℝ) / 100000000)
    (h₁₁ : ‖activityComplementOperator
      (D - uniformDifferenceDistributionMatrix (State A n))‖ ≤
        (64519 : ℝ) / 100000000) :
    ‖D - uniformDifferenceDistributionMatrix (State A n)‖ ≤
      (88250 : ℝ) / 100000000 := by
  let M := D - uniformDifferenceDistributionMatrix (State A n)
  apply activity_fourBlock_norm_le_of_quadratic_bound M
    ((88250 : ℝ) / 100000000) (by norm_num)
  intro a b ha hb
  have hrow₀ :
      ‖activityTruncatedOperator M‖ * a +
        ‖activityComplementToActivityOperator M‖ * b ≤
      (9571 : ℝ) / 100000000 * a + 43161 / 100000000 * b := by
    exact add_le_add
      (mul_le_mul_of_nonneg_right h₀₀ ha)
      (mul_le_mul_of_nonneg_right h₀₁ hb)
  have hrow₁ :
      ‖activityToComplementOperator M‖ * a +
        ‖activityComplementOperator M‖ * b ≤
      (43161 : ℝ) / 100000000 * a + 64519 / 100000000 * b := by
    exact add_le_add
      (mul_le_mul_of_nonneg_right h₁₀ ha)
      (mul_le_mul_of_nonneg_right h₁₁ hb)
  have hleft₀ : 0 ≤ ‖activityTruncatedOperator M‖ * a +
      ‖activityComplementToActivityOperator M‖ * b := by positivity
  have hleft₁ : 0 ≤ ‖activityToComplementOperator M‖ * a +
      ‖activityComplementOperator M‖ * b := by positivity
  have hright₀ : 0 ≤ (9571 : ℝ) / 100000000 * a +
      43161 / 100000000 * b := by positivity
  have hright₁ : 0 ≤ (43161 : ℝ) / 100000000 * a +
      64519 / 100000000 * b := by positivity
  calc
    (‖activityTruncatedOperator M‖ * a +
      ‖activityComplementToActivityOperator M‖ * b) ^ 2 +
        (‖activityToComplementOperator M‖ * a +
          ‖activityComplementOperator M‖ * b) ^ 2 ≤
      ((9571 : ℝ) / 100000000 * a + 43161 / 100000000 * b) ^ 2 +
        (43161 / 100000000 * a + 64519 / 100000000 * b) ^ 2 :=
      add_le_add ((sq_le_sq₀ hleft₀ hright₀).2 hrow₀)
        ((sq_le_sq₀ hleft₁ hright₁).2 hrow₁)
    _ ≤ ((88250 : ℝ) / 100000000) ^ 2 * (a ^ 2 + b ^ 2) :=
      theorem4_scalar_rational_bound a b

theorem theorem4_rational_le_paper_decimal :
    (88250 : ℝ) / 100000000 ≤ (2 : ℝ) ^ (-(10.146 : ℝ)) := by
  have hnum : (2 : ℝ) ^ (5073 : ℕ) * (353 : ℝ) ^ (500 : ℕ) ≤
      (400000 : ℝ) ^ (500 : ℕ) := by norm_num
  have hpow : ((2 : ℝ) ^ ((5073 : ℝ) / 500)) ^ (500 : ℝ) ≤
      ((400000 : ℝ) / 353) ^ (500 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (2 : ℝ) ^ ((5073 : ℝ) / 500 * 500) = (2 : ℝ) ^ (5073 : ℕ) := by
        norm_num
      _ ≤ (400000 : ℝ) ^ (500 : ℕ) / (353 : ℝ) ^ (500 : ℕ) :=
        (le_div_iff₀ (by positivity)).2 hnum
      _ = ((400000 : ℝ) / 353) ^ (500 : ℝ) := by
        norm_num [Real.rpow_natCast, div_pow]
  have hbase : (2 : ℝ) ^ ((5073 : ℝ) / 500) ≤
      (400000 : ℝ) / 353 :=
    (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _)
      (by norm_num) (by norm_num : (0 : ℝ) < 500)).mp hpow
  have hpos : 0 < (2 : ℝ) ^ ((5073 : ℝ) / 500) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrecip : ((400000 : ℝ) / 353)⁻¹ ≤
      ((2 : ℝ) ^ ((5073 : ℝ) / 500))⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le hpos hbase
  convert hrecip using 1
  · norm_num
  · rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

private theorem paper_decimal_le_rational_of_power
    (u v m k : ℕ) (hu : 0 < u) (hv : 0 < v) (hk : 0 < k)
    (hnum : (v : ℝ) ^ k ≤ (u : ℝ) ^ k * (2 : ℝ) ^ m) :
    (2 : ℝ) ^ (-((m : ℝ) / k)) ≤ (u : ℝ) / v := by
  have hpow : ((v : ℝ) / u) ^ (k : ℝ) ≤
      ((2 : ℝ) ^ ((m : ℝ) / k)) ^ (k : ℝ) := by
    rw [Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : (m : ℝ) / k * k = m := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr hk)]
    rw [he, Real.rpow_natCast, div_pow]
    exact (div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hu) _)).2
      (by simpa only [mul_comm] using hnum)
  have hbase : (v : ℝ) / u ≤ (2 : ℝ) ^ ((m : ℝ) / k) :=
    (Real.rpow_le_rpow_iff
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
      (Nat.cast_pos.mpr hk)).mp hpow
  have hpos : 0 < (v : ℝ) / u := div_pos
    (Nat.cast_pos.mpr hv) (Nat.cast_pos.mpr hu)
  have hrecip : (((2 : ℝ) ^ ((m : ℝ) / k)))⁻¹ ≤
      ((v : ℝ) / u)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hpos hbase
  convert hrecip using 1
  · rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  · field_simp [ne_of_gt (Nat.cast_pos.mpr hv),
      ne_of_gt (Nat.cast_pos.mpr hu)]

private theorem theorem4_first_decimal_le_rational :
    (2 : ℝ) ^ (-(13.351 : ℝ)) ≤ (9571 : ℝ) / 100000000 := by
  have hnum : (100000000 : ℝ) ^ (1000 : ℕ) ≤
      (9571 : ℝ) ^ (1000 : ℕ) * (2 : ℝ) ^ (13351 : ℕ) := by norm_num
  convert paper_decimal_le_rational_of_power
    9571 100000000 13351 1000 (by omega) (by omega) (by omega) hnum using 1;
    norm_num

private theorem theorem4_mixed_decimal_le_rational :
    (2 : ℝ) ^ (-(11.178 : ℝ)) ≤ (43161 : ℝ) / 100000000 := by
  have hnum : (100000000 : ℝ) ^ (1000 : ℕ) ≤
      (43161 : ℝ) ^ (1000 : ℕ) * (2 : ℝ) ^ (11178 : ℕ) := by norm_num
  convert paper_decimal_le_rational_of_power
    43161 100000000 11178 1000 (by omega) (by omega) (by omega) hnum using 1;
    norm_num

private theorem theorem4_complement_decimal_le_rational :
    (2 : ℝ) ^ (-(10.598 : ℝ)) ≤ (64519 : ℝ) / 100000000 := by
  have hnum : (100000000 : ℝ) ^ (1000 : ℕ) ≤
      (64519 : ℝ) ^ (1000 : ℕ) * (2 : ℝ) ^ (10598 : ℕ) := by norm_num
  convert paper_decimal_le_rational_of_power
    64519 100000000 10598 1000 (by omega) (by omega) (by omega) hnum using 1;
    norm_num

/-- Theorem 4's final numerical step for a 4-byte superbox. The four block
bounds are precisely the estimates supplied by Sections 5 and 6 of the paper;
for AES they are proved in `ActivityFiniteCertificate` and `SpectralBlocks`. -/
theorem theorem4_superbox_of_paper_block_bounds
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (_hcard : Fintype.card A = 2 ^ 8)
    (D : Matrix (State A 4) (State A 4) ℝ)
    (h₀₀ : ‖activityTruncatedOperator
      (D - uniformDifferenceDistributionMatrix (State A 4))‖ ≤
        (2 : ℝ) ^ (-(13.351 : ℝ)))
    (h₀₁ : ‖activityComplementToActivityOperator
      (D - uniformDifferenceDistributionMatrix (State A 4))‖ ≤
        (2 : ℝ) ^ (-(11.178 : ℝ)))
    (h₁₀ : ‖activityToComplementOperator
      (D - uniformDifferenceDistributionMatrix (State A 4))‖ ≤
        (2 : ℝ) ^ (-(11.178 : ℝ)))
    (h₁₁ : ‖activityComplementOperator
      (D - uniformDifferenceDistributionMatrix (State A 4))‖ ≤
        (2 : ℝ) ^ (-(10.598 : ℝ))) :
    ‖D - uniformDifferenceDistributionMatrix (State A 4)‖ ≤
      (2 : ℝ) ^ (-(10.146 : ℝ)) := by
  exact (theorem4_superbox_of_rational_block_bounds D
    (h₀₀.trans theorem4_first_decimal_le_rational)
    (h₀₁.trans theorem4_mixed_decimal_le_rational)
    (h₁₀.trans theorem4_mixed_decimal_le_rational)
    (h₁₁.trans theorem4_complement_decimal_le_rational)).trans
      theorem4_rational_le_paper_decimal

end PairwiseIndependence
