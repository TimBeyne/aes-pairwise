import PairwiseIndependence.Pairwise.SpectralWeightTwoFiber

/-!
# Remark 1's refined Frobenius sum

At total spectral weight two, only the graph-zero count `k=n-1` can
contribute. The fixed-position equality in `Pairwise/SpectralWeightTwoFiber.lean` therefore
replaces the generic `2(q−1)` fiber term by the paper's exact `q−2` term.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

/-- The paper's refined squared-entry sum after fixing only the two
complementary-position sets, at total spectral weight two. -/
theorem IsMDS.spectralBasisMatrix_fixedComplementPositions_sum_squares_le_weightTwo
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ) (hsum : l₁ + l₂ = 2) (hn : 0 < n)
    (c : SpectralBasisIndex (A := A) (n := n) l₁)
    (d : SpectralBasisIndex (A := A) (n := n) l₂) :
    spectralBasisMatrix_fixedComplementPositions_sum_squares L l₁ l₂ c d ≤
      (Nat.choose (2 * n - 2) (n - 1) : ℝ) *
        ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
          ((Fintype.card A : ℝ) - 2) := by
  classical
  let P := (({i : Fin n // i ∉ d.1.1} → Bool) ×
       ({i : Fin n // i ∉ c.1.1} → Bool))
  let count : P → ℕ := fun p =>
    (spectralBasisGraphZeroPositions l₁ l₂
      (spectralBasisIndex_withActivityChoices l₁ c p.2)
      (spectralBasisIndex_withActivityChoices l₂ d p.1)).card
  let T : ℝ := ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
      ((Fintype.card A : ℝ) - 2)
  let F : ℕ → ℝ := fun k => if k + 1 = n then T else 0
  let entrySum : P → ℝ := fun p =>
    ∑ g : {i : Fin n // i ∈ d.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
      ∑ f : {i : Fin n // i ∈ c.1.1} →
        Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ),
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂)
            (spectralBasisIndex_withComplementChoices l₁
              (spectralBasisIndex_withActivityChoices l₁ c p.2) f)
            (spectralBasisIndex_withComplementChoices l₂
              (spectralBasisIndex_withActivityChoices l₂ d p.1) g)) ^ 2)
  have hpoint (p : P) : entrySum p ≤ F (count p) := by
    let cp := spectralBasisIndex_withActivityChoices l₁ c p.2
    let dp := spectralBasisIndex_withActivityChoices l₂ d p.1
    by_cases hvalid : count p + 1 = n
    · have hI : (spectralBasisGraphComplementPositions l₁ l₂ cp dp).card = 2 := by
        rw [spectralBasisGraphComplementPositions_card, hsum]
      have hb :=
        hMDS.spectralBasisMatrix_fixedActivity_sum_squares_eq_weightTwo_normalized
          L hcard l₁ l₂ cp dp (by simpa only [count] using hvalid) hI
      have he : 2 * n - count p - (l₁ + l₂) = n - 1 := by omega
      dsimp only at hb
      rw [he] at hb
      simpa only [F, if_pos hvalid, T, entrySum, count, cp, dp] using hb.le
    · have hbad : n ≤ count p ∨ count p + l₁ + l₂ ≤ n := by omega
      have hzero (g : {i : Fin n // i ∈ d.1.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ))
          (f : {i : Fin n // i ∈ c.1.1} →
          Fin (Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ)) :
          ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
            deterministicDifferenceDistributionMatrix
              (fun a : State A n => L a) *
            spectralBasisMatrix (A := A) (n := n) l₂)
              (spectralBasisIndex_withComplementChoices l₁ cp f)
              (spectralBasisIndex_withComplementChoices l₂ dp g))) = 0 := by
        rcases hbad with hhigh | hlow
        · apply spectralBasisMatrix_linear_innerProduct_zero_of_manyZeros
            L hMDS l₁ l₂ (by omega)
          rw [spectralBasisGraphZeroPositions_withChoices]
          exact hhigh
        · apply spectralBasisMatrix_linear_innerProduct_zero_of_fewConstraints
            L hMDS l₁ l₂ (by omega)
          rw [spectralBasisGraphZeroPositions_withChoices]
          exact hlow
      have hentry : entrySum p = 0 := by
        dsimp only [entrySum]
        apply Finset.sum_eq_zero
        intro g hg
        apply Finset.sum_eq_zero
        intro f hf
        rw [hzero g f]
        norm_num
      rw [hentry]
      simp [F, hvalid]
  have hsumCount :
      spectralBasisMatrix_fixedComplementPositions_sum_squares L l₁ l₂ c d ≤
        ∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
          (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) * F k := by
    calc
      spectralBasisMatrix_fixedComplementPositions_sum_squares L l₁ l₂ c d =
          ∑ p : P, entrySum p := rfl
      _ ≤ ∑ p : P, F (count p) := Finset.sum_le_sum (by
        intro p hp
        exact hpoint p)
      _ = _ := spectralBasisGraphActivityChoices_sum_by_zeroCount l₁ l₂ c d F
  have htarget : n - 1 ∈ Finset.range (2 * n - 2 + 1) := by
    simp only [Finset.mem_range]
    omega
  have hsumEval :
      (∑ k ∈ Finset.range (2 * n - (l₁ + l₂) + 1),
        (Nat.choose (2 * n - (l₁ + l₂)) k : ℝ) * F k) =
      (Nat.choose (2 * n - 2) (n - 1) : ℝ) * T := by
    rw [hsum]
    have hiff (k : ℕ) : k + 1 = n ↔ k = n - 1 := by omega
    simp only [F, hiff, mul_ite, mul_zero]
    simp [htarget]
  simpa only [hsumEval, T, mul_assoc] using hsumCount

/-- Remark 1's full squared Frobenius-entry bound for the raw spectral
matrix `Bₗ₁ᵀ D_L Bₗ₂`, including both `choose n lᵢ` position factors. -/
theorem IsMDS.spectralBasisMatrix_fullFrobenius_sum_squares_le_weightTwo
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ) (hsum : l₁ + l₂ = 2) (hn : 0 < n)
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ) :
    (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂,
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂) c d) ^ 2)) ≤
      (Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
        ((Nat.choose (2 * n - 2) (n - 1) : ℝ) *
          ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
            ((Fintype.card A : ℝ) - 2)) := by
  classical
  let B : ℝ := (Nat.choose (2 * n - 2) (n - 1) : ℝ) *
    ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
      ((Fintype.card A : ℝ) - 2)
  calc
    (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂,
        ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
          deterministicDifferenceDistributionMatrix
            (fun a : State A n => L a) *
          spectralBasisMatrix (A := A) (n := n) l₂) c d) ^ 2)) =
      ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ I₂ : {I : Finset (Fin n) // I.card = l₂},
          spectralBasisIndex_fixedPositionSet_sum l₁ l₂
            (fun c d => ((((spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
              deterministicDifferenceDistributionMatrix
                (fun a : State A n => L a) *
              spectralBasisMatrix (A := A) (n := n) l₂) c d) ^ 2)) I₁ I₂ :=
        spectralBasisIndex_pair_sum_by_positionSets l₁ l₂ _
    _ = ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ I₂ : {I : Finset (Fin n) // I.card = l₂},
          spectralBasisMatrix_fixedComplementPositions_sum_squares L l₁ l₂
            (spectralBasisIndex_default hd l₁ I₁)
            (spectralBasisIndex_default hd l₂ I₂) := by
        apply Finset.sum_congr rfl
        intro I₁ hI₁
        apply Finset.sum_congr rfl
        intro I₂ hI₂
        exact spectralBasisIndex_fixedPositionSet_sum_eq_fixedComplementPositions_sum_squares
          L l₁ l₂ hd I₁ I₂
    _ ≤ ∑ I₁ : {I : Finset (Fin n) // I.card = l₁},
        ∑ I₂ : {I : Finset (Fin n) // I.card = l₂}, B := by
        apply Finset.sum_le_sum
        intro I₁ hI₁
        apply Finset.sum_le_sum
        intro I₂ hI₂
        exact hMDS.spectralBasisMatrix_fixedComplementPositions_sum_squares_le_weightTwo
          L hcard l₁ l₂ hsum hn
            (spectralBasisIndex_default hd l₁ I₁)
            (spectralBasisIndex_default hd l₂ I₂)
    _ = (Nat.choose n l₁ * Nat.choose n l₂ : ℕ) * B := by
      simp [mul_assoc]

/-- The refined Frobenius sum bounds the raw rectangular spectral matrix's
Euclidean operator norm at total spectral weight two. -/
theorem spectralBasisMatrix_linear_twoNorm_le_weightTwo
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ) (hsum : l₁ + l₂ = 2) (hn : 0 < n)
    (hd : 0 < Module.finrank ℝ (wordActivityHilbertSubspace (A := A))ᗮ) :
    ‖(spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂‖ ≤
      Real.sqrt ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
        ((Nat.choose (2 * n - 2) (n - 1) : ℝ) *
          ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
            ((Fintype.card A : ℝ) - 2))) := by
  let M := (spectralBasisMatrix (A := A) (n := n) l₁)ᵀ *
      deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a) *
      spectralBasisMatrix (A := A) (n := n) l₂
  calc
    ‖M‖ ≤ Real.sqrt (∑ c : SpectralBasisIndex (A := A) (n := n) l₁,
      ∑ d : SpectralBasisIndex (A := A) (n := n) l₂, (M c d) ^ 2) :=
        matrixTwoNorm_le_sqrt_sum_entries_sq_rectangular M
    _ ≤ _ := Real.sqrt_le_sqrt
      (hMDS.spectralBasisMatrix_fullFrobenius_sum_squares_le_weightTwo
        L hcard l₁ l₂ hsum hn hd)

/-- Remark 1's refined bound for the actual projected linear-layer block,
including the paper's two inverse-Gram losses. -/
theorem spectralWeightBlockOperator_linear_twoNorm_le_weightTwo
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ) (hsum : l₁ + l₂ = 2) (hn : 0 < n) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ≤
      Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹) *
        Real.sqrt ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
          ((Nat.choose (2 * n - 2) (n - 1) : ℝ) *
            ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
              ((Fintype.card A : ℝ) - 2))) *
        Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) := by
  let M := deterministicDifferenceDistributionMatrix
    (fun a : State A n => L a)
  calc
    ‖spectralWeightBlockOperator (n := n) l₁ l₂ M‖ ≤
      ‖(spectralOrthonormalBasisMatrix (n := n) l₁ u hu)ᵀ * M *
        spectralOrthonormalBasisMatrix (n := n) l₂ u hu‖ :=
      spectralWeightBlockOperator_norm_le_compression l₁ l₂ u hu M
    _ ≤ Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹) *
      ‖(spectralBasisMatrix (A := A) (n := n) l₁)ᵀ * M *
        spectralBasisMatrix (A := A) (n := n) l₂‖ *
      Real.sqrt (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) :=
        spectralOrthonormalBasisMatrix_compression_twoNorm_le_gramBound
          l₁ l₂ u hu M
    _ ≤ _ := by
      gcongr
      exact spectralBasisMatrix_linear_twoNorm_le_weightTwo
        L hMDS hcard l₁ l₂ hsum hn
          (wordActivityOrthogonal_finrank_pos_of_card_ge_three hcard)

/-- Squared form of Remark 1's projected linear-layer estimate, keeping the
two inverse-Gram factors explicit for later numerical specialization. -/
theorem spectralWeightBlockOperator_linear_sq_le_weightTwo
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    {n : ℕ} (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ) (hsum : l₁ + l₂ = 2) (hn : 0 < n) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ^ 2 ≤
      (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹) *
        ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
          ((Nat.choose (2 * n - 2) (n - 1) : ℝ) *
            ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
              ((Fintype.card A : ℝ) - 2))) *
        (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) := by
  let G₁ : ℝ := (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^
    (n - l₁))⁻¹)
  let G₂ : ℝ := (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^
    (n - l₂))⁻¹)
  let B : ℝ := (Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
    ((Nat.choose (2 * n - 2) (n - 1) : ℝ) *
      ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
        ((Fintype.card A : ℝ) - 2))
  have hG₁ : 0 ≤ G₁ :=
    (norm_nonneg _).trans
      (spectralBasisMatrix_gram_inverse_twoNorm_le (n := n) l₁ u hu)
  have hG₂ : 0 ≤ G₂ :=
    (norm_nonneg _).trans
      (spectralBasisMatrix_gram_inverse_twoNorm_le (n := n) l₂ u hu)
  have hB : 0 ≤ B := by
    have hqnat : 2 ≤ Fintype.card A := by omega
    have hq : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hqnat
    have hqinv : 0 ≤ (Fintype.card A : ℝ)⁻¹ := by positivity
    have hq2 : 0 ≤ (Fintype.card A : ℝ) - 2 := sub_nonneg.mpr hq
    dsimp [B]
    exact mul_nonneg (Nat.cast_nonneg _) <|
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hqinv _)) hq2
  have h := spectralWeightBlockOperator_linear_twoNorm_le_weightTwo
    u hu L hMDS hcard l₁ l₂ hsum hn
  change ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ≤
      Real.sqrt G₁ * Real.sqrt B * Real.sqrt G₂ at h
  have hroot : 0 ≤ Real.sqrt G₁ * Real.sqrt B * Real.sqrt G₂ := by
    positivity
  let T := spectralWeightBlockOperator (n := n) l₁ l₂
    (deterministicDifferenceDistributionMatrix
      (fun a : State A n => L a))
  have hsq := (sq_le_sq₀ (norm_nonneg T) hroot).mpr h
  change ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ^ 2 ≤ G₁ * B * G₂
  calc
    _ ≤ (Real.sqrt G₁ * Real.sqrt B * Real.sqrt G₂) ^ 2 := hsq
    _ = G₁ * B * G₂ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hG₁,
        Real.sq_sqrt hB, Real.sq_sqrt hG₂]

end PairwiseIndependence
