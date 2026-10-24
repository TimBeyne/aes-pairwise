import PairwiseIndependence.AesBounds.Theorem4Assembly

/-!
# The paper's Section 6 numerical spectral bounds at AES parameters

These are the final arithmetic comparisons in the paper's proof of
Theorem 4. The spectral operator inequalities are proved separately in
`AesBounds/SpectralBlocks.lean`.
The concrete one-byte S-box norm bound is proved in `AesBounds/SboxAffineBridge.lean`.
-/

namespace PairwiseIndependence

/-! The bounds below take the AES S-box parameter `σ ≤ 0.070315`, which is
slightly larger than the paper's `9/128`. With `q = 2^8` and `n = 4`, Remark 1
gives `σ⁶ + (q − 2) σ⁴ / (√q − 1)^(2n−2) · C(n,2) · C(2n−2,n−1)` for the mixed
blocks and `2σ⁶ + (q − 2) σ⁴ / (√q − 1)^(2n−2) · n² · C(2n−2,n−1)` for the
complementary block. -/

private theorem aesMixedSpectralSquaredBound_cyclic_le_rational :
    (70315 / 1000000 : ℝ) ^ 6 + 254 * 6 * 20 / 15 ^ 6 * (70315 / 1000000 : ℝ) ^ 4 ≤ ((4316 : ℝ) / 10000000) ^ 2 := by
  norm_num

private theorem aesComplementSpectralSquaredBound_cyclic_le_rational :
    2 * (70315 / 1000000 : ℝ) ^ 6 + 254 * 16 * 20 / 15 ^ 6 * (70315 / 1000000 : ℝ) ^ 4 ≤ ((64515 : ℝ) / 100000000) ^ 2 := by
  norm_num

private theorem aesMixed_cyclic_rational_le_paper :
    (4316 : ℝ) / 10000000 ≤ (2 : ℝ) ^ (-(11.178 : ℝ)) := by
  apply (Real.rpow_le_rpow_iff
    (by norm_num : (0 : ℝ) ≤ 4316 / 10000000)
    (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) < 500)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : (-(11.178 : ℝ)) * (500 : ℝ) = -(5589 : ℝ) := by norm_num
  rw [hexp]
  norm_num

private theorem aesComplement_cyclic_rational_le_paper :
    (64515 : ℝ) / 100000000 ≤ (2 : ℝ) ^ (-(10.598 : ℝ)) := by
  apply (Real.rpow_le_rpow_iff
    (by norm_num : (0 : ℝ) ≤ 64515 / 100000000)
    (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) < 500)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : (-(10.598 : ℝ)) * (500 : ℝ) = -(5299 : ℝ) := by norm_num
  rw [hexp]
  norm_num

/-- The refined Section 6 mixed-block arithmetic also works with the
slightly larger rational threshold of the cyclic Gram certificate. This
does not prove that the actual AES S-box has that threshold. -/
theorem aesMixedSpectralSquaredBound_cyclic_le_paper :
    (70315 / 1000000 : ℝ) ^ 6 + 254 * 6 * 20 / 15 ^ 6 * (70315 / 1000000 : ℝ) ^ 4 ≤
      ((2 : ℝ) ^ (-(11.178 : ℝ))) ^ 2 :=
  aesMixedSpectralSquaredBound_cyclic_le_rational.trans
    (pow_le_pow_left₀ (by norm_num) aesMixed_cyclic_rational_le_paper 2)

/-- The refined Section 6 complementary-block arithmetic also works with
the cyclic certificate's rational threshold. -/
theorem aesComplementSpectralSquaredBound_cyclic_le_paper :
    2 * (70315 / 1000000 : ℝ) ^ 6 + 254 * 16 * 20 / 15 ^ 6 * (70315 / 1000000 : ℝ) ^ 4 ≤
      ((2 : ℝ) ^ (-(10.598 : ℝ))) ^ 2 :=
  aesComplementSpectralSquaredBound_cyclic_le_rational.trans
    (pow_le_pow_left₀ (by norm_num) aesComplement_cyclic_rational_le_paper 2)

end PairwiseIndependence
