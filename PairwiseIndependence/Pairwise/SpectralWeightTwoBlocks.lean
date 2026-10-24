import PairwiseIndependence.Pairwise.SpectralWeightTwoFrobenius
import PairwiseIndependence.Pairwise.SharkBound

/-!
# Remark 1 in the SHARK spectral blocks

At `l=2`, the `W₁` mixed block vanishes, the `W₂` block uses the refined
`q−2` Frobenius estimate, and the high-weight tail contributes `σ⁶`.
The statements are for independently keyed S-boxes; a fixed S-box is the
case of a one-element key space.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

variable {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
  [Fintype κ] [Nonempty κ] {n : ℕ}

/-- Remark 1 for the SHARK matrix: a total-weight-two spectral block. -/
theorem keyedSharkTwoCore_spectralWeightBlock_sq_le_weightTwo
    (u : A) (hu : u ≠ 0)
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A)
    (l₁ l₂ : ℕ) (hsum : l₁ + l₂ = 2) (hn : 0 < n) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ 4 *
        (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₁))⁻¹ *
          ((Nat.choose n l₁ * Nat.choose n l₂ : ℕ) *
            ((Nat.choose (2 * n - 2) (n - 1) : ℝ) * ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
              ((Fintype.card A : ℝ) - 2))) *
          ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - l₂))⁻¹) := by
  let σ := ‖keyedSboxActivityComplementOperator S‖
  let B := spectralWeightBlockOperator (n := n) l₁ l₂
    (deterministicDifferenceDistributionMatrix (fun a : State A n => L a))
  let P := spectralWeightBlockOperator (n := n) l₁ l₂
    (differenceDistributionMatrix (keyedSharkTwoCore S L))
  have hfirst : ‖P‖ ≤ σ ^ (l₁ + l₂) * ‖B‖ := by
    dsimp only [P, B, σ]
    rw [keyedSharkTwoCore_differenceDistributionMatrix,
      ← keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix]
    exact keyedSpectralWeightBlock_sandwich_norm_le S _ l₁ l₂
  have hlin := spectralWeightBlockOperator_linear_sq_le_weightTwo
    u hu L hMDS hcard l₁ l₂ hsum hn
  have hσ : 0 ≤ σ := norm_nonneg (keyedSboxActivityComplementOperator S)
  have hsq := (sq_le_sq₀ (norm_nonneg P) (by positivity)).mpr hfirst
  change ‖P‖ ^ 2 ≤ σ ^ 4 * _
  calc
    ‖P‖ ^ 2 ≤ (σ ^ (l₁ + l₂) * ‖B‖) ^ 2 := hsq
    _ = σ ^ 4 * ‖B‖ ^ 2 := by rw [hsum, mul_pow]; ring
    _ ≤ σ ^ 4 * _ := mul_le_mul_of_nonneg_left hlin (pow_nonneg hσ _)

/-- The paper's refined `l=2` bound on the mixed block `V → V⊥`. -/
theorem keyedSharkTwoCore_activityToComplement_sq_le_weightTwo
    (u : A) (hu : u ≠ 0)
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A) (hn : 2 ≤ n) :
    ‖activityToComplementOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ 6 +
        ‖keyedSboxActivityComplementOperator S‖ ^ 4 *
          (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - 2))⁻¹ *
            ((Nat.choose n 2 * Nat.choose n 0 : ℕ) *
              ((Nat.choose (2 * n - 2) (n - 1) : ℝ) * ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
                ((Fintype.card A : ℝ) - 2))) *
            ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - 0))⁻¹) := by
  classical
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let σ := ‖keyedSboxActivityComplementOperator S‖
  let R := activityToHighWeightOperator (n := n) 2 D
  let f (i : ℕ) : ℝ :=
    ‖(spectralWeightHilbertSubspace (A := A) (n := n) i).orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
        (activityHilbertSubspace (A := A) (n := n)).subtypeL‖ ^ 2
  have hbase := activityToComplementOperator_norm_sq_le_low_add_tail
    (A := A) (n := n) 2 (by omega) D
  change ‖activityToComplementOperator D‖ ^ 2 ≤
    (∑ i : {i : ℕ // i ∈ Finset.Icc 1 2}, f i.1) + ‖R‖ ^ 2 at hbase
  -- The `W₁` block vanishes by Lemma 12.
  have hzero : f 1 = 0 := by
    have h := keyedSharkTwoCore_activity_to_spectralWeight_sq_le
      u hu S L hMDS 1 (by omega) (by omega) hcard
    have hle : f 1 ≤ 0 := by
      simpa only [f, sharkBlockCoefficient_one_zero, zero_div, mul_zero] using h
    exact le_antisymm hle (sq_nonneg _)
  have hsum : (∑ i : {i : ℕ // i ∈ Finset.Icc 1 2}, f i.1) = f 2 := by
    rw [finiteIntervalSubtypeSum_erase_one f 2 (by omega) hzero]
    change (∑ i ∈ (Finset.Icc 2 2).attach, f i.1) = f 2
    rw [Finset.sum_attach]
    simp
  -- Remark 1 bounds the `W₂` block.
  have hW := keyedSharkTwoCore_spectralWeightBlock_sq_le_weightTwo
    u hu S L hMDS hcard 2 0 (by omega) (by omega)
  let F (U : Submodule ℝ (EuclideanSpace ℝ (State A n))) : ℝ :=
    ‖(spectralWeightHilbertSubspace (A := A) (n := n) 2).orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L U.subtypeL‖
  have hnorm : ‖spectralWeightBlockOperator (n := n) 2 0 D‖ =
      F (activityHilbertSubspace (A := A) (n := n)) := by
    change F (spectralWeightHilbertSubspace (A := A) (n := n) 0) = _
    exact congrArg F spectralWeightZeroHilbert_eq_activity
  rw [hnorm] at hW
  change f 2 ≤ σ ^ 4 * _ at hW
  have htailSq : ‖R‖ ^ 2 ≤ σ ^ 6 := by
    have hsq := (sq_le_sq₀ (norm_nonneg R) (by positivity)).mpr
      (keyedSharkTwoCore_activityToHighWeight_norm_le S L 2)
    simpa only [← pow_mul] using hsq
  calc
    ‖activityToComplementOperator D‖ ^ 2 ≤ f 2 + ‖R‖ ^ 2 := by
      simpa only [hsum] using hbase
    _ ≤ σ ^ 4 * _ + σ ^ 6 :=
      add_le_add hW htailSq
    _ = _ := by ring

/-- The reverse mixed block `V⊥ → V` has the same refined `l=2` bound, by
transposing the SHARK matrix. -/
theorem keyedSharkTwoCore_activityComplementToActivity_sq_le_weightTwo
    (u : A) (hu : u ≠ 0)
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A) (hn : 2 ≤ n) :
    ‖activityComplementToActivityOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ 6 +
        ‖keyedSboxActivityComplementOperator S‖ ^ 4 *
          (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - 2))⁻¹ *
            ((Nat.choose n 2 * Nat.choose n 0 : ℕ) *
              ((Nat.choose (2 * n - 2) (n - 1) : ℝ) * ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
                ((Fintype.card A : ℝ) - 2))) *
            ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - 0))⁻¹) := by
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let Dinv := differenceDistributionMatrix
    (keyedSharkTwoCore (fun key => (S key).symm) L.symm)
  have htranspose : Dinv = Dᵀ :=
    keyedSharkTwoCore_symm_differenceDistributionMatrix_eq_transpose S L
  have hnorm : ‖activityComplementToActivityOperator D‖ =
      ‖activityToComplementOperator Dinv‖ := by
    have h := activityComplementToActivityOperator_transpose_eq_adjoint Dinv
    rw [htranspose, Matrix.transpose_transpose] at h
    rw [h, ContinuousLinearMap.adjoint.norm_map, ← htranspose]
  have h := keyedSharkTwoCore_activityToComplement_sq_le_weightTwo
    u hu (fun key => (S key).symm) L.symm (IsMDS.symm L hMDS) hcard hn
  rw [keyedSboxActivityComplementOperator_symm_norm_eq] at h
  change ‖activityComplementToActivityOperator D‖ ^ 2 ≤ _
  rwa [hnorm]

/-- The paper's refined `l=2` bound on the block `V⊥ → V⊥`. The only
interior pair is `W₁ → W₁`; the two high-weight tails contribute `2σ⁶`. -/
theorem keyedSharkTwoCore_activityComplement_sq_le_weightTwo
    (u : A) (hu : u ≠ 0)
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hcard : 3 ≤ Fintype.card A) (hn : 2 ≤ n) :
    ‖activityComplementOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      2 * ‖keyedSboxActivityComplementOperator S‖ ^ 6 +
        ‖keyedSboxActivityComplementOperator S‖ ^ 4 *
          (((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - 1))⁻¹ *
            ((Nat.choose n 1 * Nat.choose n 1 : ℕ) *
              ((Nat.choose (2 * n - 2) (n - 1) : ℝ) * ((Fintype.card A : ℝ)⁻¹) ^ (n - 1) *
                ((Fintype.card A : ℝ) - 2))) *
            ((1 - (Real.sqrt (Fintype.card A : ℝ))⁻¹) ^ (n - 1))⁻¹) := by
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let σ := ‖keyedSboxActivityComplementOperator S‖
  have hbase := keyedSharkTwoCore_activityComplement_paperInteriorTail_le
    S L 2 (by omega) (by omega)
  have hsum :
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (2 - 1)},
        ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (2 - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1 D‖ ^ 2) =
      ‖spectralWeightBlockOperator (n := n) 1 1 D‖ ^ 2 := by
    let i₀ : {i : ℕ // i ∈ Finset.Icc 1 1} := ⟨1, by simp⟩
    haveI : Unique {i : ℕ // i ∈ Finset.Icc 1 1} := {
      default := i₀
      uniq i := by
        apply Subtype.ext
        change i.1 = 1
        have hi := Finset.mem_Icc.mp i.2
        omega
    }
    simp only [Fintype.sum_unique]
    have hdefault : (default : {i : ℕ // i ∈ Finset.Icc 1 1}) = i₀ :=
      Subsingleton.elim _ _
    rw [hdefault]
    change (∑ j : {j : ℕ // j ∈ Finset.Icc 1 1},
      ‖spectralWeightBlockOperator (n := n) 1 j.1 D‖ ^ 2) = _
    simp
    rw [hdefault]
  have hW := keyedSharkTwoCore_spectralWeightBlock_sq_le_weightTwo
    u hu S L hMDS hcard 1 1 (by omega) (by omega : 0 < n)
  change ‖activityComplementOperator D‖ ^ 2 ≤
    (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (2 - 1)},
      ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (2 - i.1)},
        ‖spectralWeightBlockOperator (n := n) i.1 j.1 D‖ ^ 2) +
      (2 : ℝ) * σ ^ 6 at hbase
  rw [hsum] at hbase
  change ‖spectralWeightBlockOperator (n := n) 1 1 D‖ ^ 2 ≤
    σ ^ 4 * _ at hW
  linarith

end PairwiseIndependence
