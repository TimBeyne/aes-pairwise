import PairwiseIndependence.Pairwise.OneWordSpectralBias
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Vandermonde
import PairwiseIndependence.Theorem3
import PairwiseIndependence.Pairwise.KeyedShark

/-!
# Theorems 3 and 7 for independently keyed SHARK

`sharkCoefficient q n k` is the coefficient `C(n, k)` of Theorems 3 and 7.
Theorem 7 is `keyedSharkSpectralTerms_general`. Theorem 3 for independently
keyed S-boxes is `theorem3_keyed_of_spectralBias_le`; it combines Theorem 6
(`Pairwise/Activity.lean`) for the block `V → V` with Theorem 7 for the other
three blocks. The proof works with the norm of the one-word activity-complement
operator, which `Pairwise/OneWordSpectralBias.lean` bounds by `‖Dˢ − U‖`.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

/-- The coefficient `C(n, k)` of Theorems 3 and 7, with the field size `q`
explicit. -/
noncomputable def sharkCoefficient (q n k : ℕ) : ℝ :=
  (1 + 1 / (Real.sqrt (q : ℝ) - 1)) ^ k *
    (Nat.choose (2 * n) k : ℝ) *
      ∑ i ∈ Finset.Icc 1 (k - 1),
        (Nat.choose (2 * n - k) (n - i) : ℝ) * (2 : ℝ) ^ i

/-- The coefficient of one spectral block in the paper's notation. -/
noncomputable def sharkBlockCoefficient (q n l₁ l₂ : ℕ) : ℝ :=
  (1 + 1 / (Real.sqrt (q : ℝ) - 1)) ^ (l₁ + l₂) *
    ((Nat.choose n l₁ : ℝ) * (Nat.choose n l₂ : ℝ)) *
      ∑ i ∈ Finset.Icc 1 (l₁ + l₂ - 1),
        (Nat.choose (2 * n - (l₁ + l₂)) (n - i) : ℝ) * (2 : ℝ) ^ i

theorem choose_total_vandermonde (n k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
      (Nat.choose n i : ℝ) * (Nat.choose n (k - i) : ℝ)) =
      (Nat.choose (2 * n) k : ℝ) := by
  have hv := Nat.add_choose_eq n n k
  have hv' : (∑ i ∈ Finset.range (k + 1),
      n.choose i * n.choose (k - i)) = (2 * n).choose k := by
    calc
      _ = ∑ ij ∈ Finset.antidiagonal k,
        n.choose ij.1 * n.choose ij.2 :=
          (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => n.choose i * n.choose j) k).symm
      _ = _ := by simpa [two_mul] using hv.symm
  exact_mod_cast hv'

/-- Summing every `Wₗ₁ → Wₗ₂` coefficient of total weight `k` yields the exact `C(n,k)` in Theorem 3. -/
theorem sharkBlockCoefficient_sum_eq_sharkCoefficient
    (q n k : ℕ) :
    (∑ l₁ ∈ Finset.range (k + 1),
      sharkBlockCoefficient q n l₁ (k - l₁)) =
      sharkCoefficient q n k := by
  let a : ℝ := (1 + 1 / (Real.sqrt (q : ℝ) - 1)) ^ k
  let S : ℝ := ∑ i ∈ Finset.Icc 1 (k - 1),
    (Nat.choose (2 * n - k) (n - i) : ℝ) * (2 : ℝ) ^ i
  have hterm (l₁ : ℕ) (hl : l₁ ∈ Finset.range (k + 1)) :
      sharkBlockCoefficient q n l₁ (k - l₁) =
        a * ((Nat.choose n l₁ : ℝ) * (Nat.choose n (k - l₁) : ℝ)) * S := by
    have hle : l₁ ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    simp only [sharkBlockCoefficient, Nat.add_sub_of_le hle, a, S]
  calc
    (∑ l₁ ∈ Finset.range (k + 1),
      sharkBlockCoefficient q n l₁ (k - l₁)) =
      ∑ l₁ ∈ Finset.range (k + 1),
        a * ((Nat.choose n l₁ : ℝ) * (Nat.choose n (k - l₁) : ℝ)) * S := by
          apply Finset.sum_congr rfl
          intro l₁ hl
          exact hterm l₁ hl
    _ = a * (∑ l₁ ∈ Finset.range (k + 1),
        (Nat.choose n l₁ : ℝ) * (Nat.choose n (k - l₁) : ℝ)) * S := by
          calc
            (∑ l₁ ∈ Finset.range (k + 1),
              a * ((Nat.choose n l₁ : ℝ) * (Nat.choose n (k - l₁) : ℝ)) * S) =
              (∑ l₁ ∈ Finset.range (k + 1),
                a * ((Nat.choose n l₁ : ℝ) * (Nat.choose n (k - l₁) : ℝ))) * S := by
                  conv_lhs => rw [← Finset.sum_mul]
            _ = a * (∑ l₁ ∈ Finset.range (k + 1),
              (Nat.choose n l₁ : ℝ) * (Nat.choose n (k - l₁) : ℝ)) * S := by
                congr 1
                rw [Finset.mul_sum]
    _ = a * (Nat.choose (2 * n) k : ℝ) * S := by
      rw [choose_total_vandermonde]
    _ = sharkCoefficient q n k := rfl

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {n : ℕ}

/-- The paper's projected `Wₗ₂ → Wₗ₁` lemma stated directly with the block coefficient used to assemble Theorem 3. -/
theorem spectralFrobeniusBound_sharkBlockCoefficient
    (u : A) (hu : u ≠ 0)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hl : l₁ + l₂ ≤ n) (hq : 3 ≤ Fintype.card A) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (deterministicDifferenceDistributionMatrix
        (fun a : State A n => L a))‖ ^ 2 ≤
      sharkBlockCoefficient (Fintype.card A) n l₁ l₂ /
        (Real.sqrt (Fintype.card A : ℝ) - 1) ^
          (2 * n - 2 * (l₁ + l₂)) := by
  simpa only [sharkBlockCoefficient, mul_assoc, Nat.cast_mul] using
    (spectralFrobeniusBound_paper u hu L hMDS l₁ l₂ hpos hl hq)

/-- The paper's MDS spectral Frobenius block estimate after independently
keyed word substitutions. The `σ` here belongs to the averaged one-word
difference-distribution matrix. -/
theorem keyedSharkTwoCore_spectralWeightBlock_sq_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (u : A) (hu : u ≠ 0) (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l₁ l₂ : ℕ) (hpos : 0 < l₁ + l₂)
    (hl : l₁ + l₂ ≤ n) (hq : 3 ≤ Fintype.card A) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l₁ + l₂)) *
        (sharkBlockCoefficient (Fintype.card A) n l₁ l₂ /
          (Real.sqrt (Fintype.card A : ℝ) - 1) ^
            (2 * n - 2 * (l₁ + l₂))) := by
  let σ := ‖keyedSboxActivityComplementOperator S‖
  let M := deterministicDifferenceDistributionMatrix
    (fun a : State A n => L a)
  let B := spectralWeightBlockOperator (n := n) l₁ l₂ M
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let P := spectralWeightBlockOperator (n := n) l₁ l₂ D
  let c := sharkBlockCoefficient (Fintype.card A) n l₁ l₂ /
    (Real.sqrt (Fintype.card A : ℝ) - 1) ^
      (2 * n - 2 * (l₁ + l₂))
  have hfirst : ‖P‖ ≤ σ ^ (l₁ + l₂) * ‖B‖ := by
    dsimp only [P, D, B, M, σ]
    rw [keyedSharkTwoCore_differenceDistributionMatrix]
    rw [← keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix]
    exact keyedSpectralWeightBlock_sandwich_norm_le S _ l₁ l₂
  have hlin : ‖B‖ ^ 2 ≤ c :=
    spectralFrobeniusBound_sharkBlockCoefficient u hu L hMDS l₁ l₂ hpos hl hq
  have hs : 0 ≤ σ := by
    dsimp [σ]
    exact norm_nonneg (keyedSboxActivityComplementOperator S)
  have hnonneg : 0 ≤ σ ^ (l₁ + l₂) * ‖B‖ :=
    mul_nonneg (pow_nonneg hs _) (norm_nonneg B)
  have hsq := (sq_le_sq₀ (norm_nonneg P) hnonneg).2 hfirst
  have hmul := mul_le_mul_of_nonneg_left hlin (pow_nonneg hs (2 * (l₁ + l₂)))
  change ‖P‖ ^ 2 ≤ σ ^ (2 * (l₁ + l₂)) * c
  calc
    ‖P‖ ^ 2 ≤ (σ ^ (l₁ + l₂) * ‖B‖) ^ 2 := hsq
    _ = σ ^ (2 * (l₁ + l₂)) * ‖B‖ ^ 2 := by
      rw [mul_pow, ← pow_mul]
      ring
    _ ≤ σ ^ (2 * (l₁ + l₂)) * c := hmul

/-- The keyed mixed block from the paper's activity space to one spectral
weight has the same MDS coefficient as the fixed-S-box SHARK construction. -/
theorem keyedSharkTwoCore_activity_to_spectralWeight_sq_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (u : A) (hu : u ≠ 0) (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (i : ℕ) (hi : 0 < i) (hin : i ≤ n)
    (hq : 3 ≤ Fintype.card A) :
    ‖(spectralWeightHilbertSubspace (A := A) (n := n) i).orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
        (differenceDistributionMatrix (keyedSharkTwoCore S L)) ∘L
      (activityHilbertSubspace (A := A) (n := n)).subtypeL‖ ^ 2 ≤
    ‖keyedSboxActivityComplementOperator S‖ ^ (2 * i) *
      (sharkBlockCoefficient (Fintype.card A) n i 0 /
        (Real.sqrt (Fintype.card A : ℝ) - 1) ^
          (2 * n - 2 * i)) := by
  have h := keyedSharkTwoCore_spectralWeightBlock_sq_le
    u hu S L hMDS i 0 (by omega) (by omega) hq
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let f (U : Submodule ℝ (EuclideanSpace ℝ (State A n))) : ℝ :=
    ‖(spectralWeightHilbertSubspace (A := A) (n := n) i).orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L U.subtypeL‖
  have hnorm : ‖spectralWeightBlockOperator (n := n) i 0 D‖ =
      f (activityHilbertSubspace (A := A) (n := n)) := by
    change f (spectralWeightHilbertSubspace (A := A) (n := n) 0) = _
    exact congrArg f spectralWeightZeroHilbert_eq_activity
  rw [hnorm] at h
  simpa only [add_zero, f, D] using h

/-- The first keyed mixed spectral term has the paper's finite low-weight
sum and one high-weight tail. -/
theorem keyedSharkTwoCore_activityToComplement_lowTail_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (u : A) (hu : u ≠ 0) (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hl : l ≤ n) (hq : 3 ≤ Fintype.card A) :
    ‖activityToComplementOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖keyedSboxActivityComplementOperator S‖ ^ (2 * i.1) *
          (sharkBlockCoefficient (Fintype.card A) n i.1 0 /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^
              (2 * n - 2 * i.1))) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
  classical
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let σ := ‖keyedSboxActivityComplementOperator S‖
  let R := activityToHighWeightOperator (A := A) (n := n) l D
  have hbase := activityToComplementOperator_norm_sq_le_low_add_tail l hl D
  have hsum :
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
          (activityHilbertSubspace (A := A) (n := n)).subtypeL‖ ^ 2) ≤
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        σ ^ (2 * i.1) *
          (sharkBlockCoefficient (Fintype.card A) n i.1 0 /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^
              (2 * n - 2 * i.1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_Icc.mp i.2
    exact keyedSharkTwoCore_activity_to_spectralWeight_sq_le
      u hu S L hMDS i.1 hi'.1 (hi'.2.trans hl) hq
  have htail := keyedSharkTwoCore_activityToHighWeight_norm_le S L l
  have htailSq : ‖R‖ ^ 2 ≤ σ ^ (2 * (l + 1)) := by
    have h : ‖R‖ ^ 2 ≤ (σ ^ (l + 1)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg R)
        (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)).2 htail
    calc
      ‖R‖ ^ 2 ≤ (σ ^ (l + 1)) ^ 2 := h
      _ = σ ^ (2 * (l + 1)) := by
        rw [← pow_mul]
        congr 1
        omega
  calc
    ‖activityToComplementOperator D‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
          (activityHilbertSubspace (A := A) (n := n)).subtypeL‖ ^ 2) +
      ‖R‖ ^ 2 := hbase
    _ ≤ (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        σ ^ (2 * i.1) *
          (sharkBlockCoefficient (Fintype.card A) n i.1 0 /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^
              (2 * n - 2 * i.1))) + ‖R‖ ^ 2 :=
        add_le_add_right hsum _
    _ ≤ _ := add_le_add_left htailSq _

/-- The reverse keyed mixed term has the same finite sum and tail bound
because inversion transposes its difference-distribution matrix. -/
theorem keyedSharkTwoCore_activityComplementToActivity_lowTail_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (u : A) (hu : u ≠ 0) (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hl : l ≤ n) (hq : 3 ≤ Fintype.card A) :
    ‖activityComplementToActivityOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l},
        ‖keyedSboxActivityComplementOperator S‖ ^ (2 * i.1) *
          (sharkBlockCoefficient (Fintype.card A) n i.1 0 /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^
              (2 * n - 2 * i.1))) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
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
  have h := keyedSharkTwoCore_activityToComplement_lowTail_le
    u hu (fun key => (S key).symm) L.symm (IsMDS.symm L hMDS) l hl hq
  rw [keyedSboxActivityComplementOperator_symm_norm_eq] at h
  change ‖activityToComplementOperator Dinv‖ ^ 2 ≤ _ at h
  change ‖activityComplementToActivityOperator D‖ ^ 2 ≤ _
  rwa [hnorm]

/-- The paper’s closed-form coefficient vanishes for the exceptional mixed `W₁` block. -/
theorem sharkBlockCoefficient_one_zero (q n : ℕ) :
    sharkBlockCoefficient q n 1 0 = 0 := by
  simp [sharkBlockCoefficient]

theorem finiteIntervalSubtypeSum_erase_one
    (f : ℕ → ℝ) (l : ℕ) (hl : 1 ≤ l) (hzero : f 1 = 0) :
    (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l}, f i.1) =
      ∑ i : {i : ℕ // i ∈ Finset.Icc 2 l}, f i.1 := by
  classical
  have hsingle : (∑ i : {i : ℕ // i ∈ Finset.Icc 1 1}, f i.1) = f 1 := by
    change (∑ i ∈ (Finset.Icc 1 1).attach, f i.1) = f 1
    rw [Finset.sum_attach]
    simp
  have hsplit := finiteIntervalSubtypeSum_split f 1 l hl
  rw [hsingle, hzero, zero_add] at hsplit
  exact hsplit

/-- The keyed mixed sums start at weight two because the `W₁` coefficient vanishes. -/
theorem keyedSharkTwoCore_activityToComplement_paperLowTail_le
    (u : A) (hu : u ≠ 0) {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n)
    (hq : 3 ≤ Fintype.card A) :
    ‖activityToComplementOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 2 l},
        ‖keyedSboxActivityComplementOperator S‖ ^ (2 * i.1) *
          (sharkBlockCoefficient (Fintype.card A) n i.1 0 /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^
              (2 * n - 2 * i.1))) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
  let f (i : ℕ) : ℝ :=
    ‖keyedSboxActivityComplementOperator S‖ ^ (2 * i) *
      (sharkBlockCoefficient (Fintype.card A) n i 0 /
        (Real.sqrt (Fintype.card A : ℝ) - 1) ^
          (2 * n - 2 * i))
  have hzero : f 1 = 0 := by
    simp [f, sharkBlockCoefficient_one_zero]
  have hsum := finiteIntervalSubtypeSum_erase_one f l hlo hzero
  have h := keyedSharkTwoCore_activityToComplement_lowTail_le
    u hu S L hMDS l hl hq
  change ‖activityToComplementOperator
    (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l}, f i.1) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) at h
  rw [hsum] at h
  exact h

/-- The paper's exact finite mixed sum and one high-weight tail, reverse direction. -/
theorem keyedSharkTwoCore_activityComplementToActivity_paperLowTail_le
    (u : A) (hu : u ≠ 0) {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n)
    (hq : 3 ≤ Fintype.card A) :
    ‖activityComplementToActivityOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 2 l},
        ‖keyedSboxActivityComplementOperator S‖ ^ (2 * i.1) *
          (sharkBlockCoefficient (Fintype.card A) n i.1 0 /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^
              (2 * n - 2 * i.1))) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
  let f (i : ℕ) : ℝ :=
    ‖keyedSboxActivityComplementOperator S‖ ^ (2 * i) *
      (sharkBlockCoefficient (Fintype.card A) n i 0 /
        (Real.sqrt (Fintype.card A : ℝ) - 1) ^
          (2 * n - 2 * i))
  have hzero : f 1 = 0 := by
    simp [f, sharkBlockCoefficient_one_zero]
  have hsum := finiteIntervalSubtypeSum_erase_one f l hlo hzero
  have h := keyedSharkTwoCore_activityComplementToActivity_lowTail_le
    u hu S L hMDS l hl hq
  change ‖activityComplementToActivityOperator
    (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 l}, f i.1) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) at h
  rw [hsum] at h
  exact h

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The paper's `l` high-weight tails in the keyed `V⊥ → V⊥` block. -/
theorem keyedSharkTwoCore_activityComplement_paperInteriorTail_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n) :
    ‖activityComplementOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1
            (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2) +
      (l : ℝ) * ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
  classical
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let σ := ‖keyedSboxActivityComplementOperator S‖
  let b := σ ^ (2 * (l + 1))
  have htail (i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)}) :
      ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
        (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
          (Finset.Icc (l - i.1 + 1) n)).subtypeL‖ ^ 2 ≤ b := by
    let T := (spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
      (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l - i.1 + 1) n)).subtypeL
    have h := keyedSharkTwoCore_spectralRow_highInput_norm_le S L i.1 l (by
      have hi := Finset.mem_Icc.mp i.property
      omega)
    change ‖T‖ ≤ σ ^ (l + 1) at h
    have hs : ‖T‖ ^ 2 ≤ (σ ^ (l + 1)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg T)
        (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)).2 h
    change _ ≤ σ ^ (2 * (l + 1))
    calc
      _ ≤ (σ ^ (l + 1)) ^ 2 := hs
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have houter :
      ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc l n)).orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
          ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL‖ ^ 2 ≤ b := by
    let R := (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
      (Finset.Icc l n)).orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
        ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL
    have h := keyedSharkTwoCore_highOutput_fromActivityComplement_norm_le S L (l - 1)
    rw [Nat.sub_add_cancel hlo] at h
    change ‖R‖ ≤ σ ^ (l - 1 + 2) at h
    have hs : ‖R‖ ^ 2 ≤ (σ ^ (l - 1 + 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg R)
        (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)).2 h
    change _ ≤ σ ^ (2 * (l + 1))
    calc
      _ ≤ (σ ^ (l + 1)) ^ 2 := by simpa only [show l - 1 + 2 = l + 1 by omega] using hs
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hsplit := activityComplementOperator_norm_sq_le_paperInteriorAndTails
    (A := A) (n := n) D l hlo hl
  have hsum :
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ((∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1 D‖ ^ 2) +
        ‖(spectralWeightHilbertSubspace (A := A) (n := n) i.1).orthogonalProjection ∘L
          Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D ∘L
          (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
            (Finset.Icc (l - i.1 + 1) n)).subtypeL‖ ^ 2)) ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ((∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1 D‖ ^ 2) + b)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact add_le_add_left (htail i) _
  have hcard : (Finset.Icc 1 (l - 1)).card + 1 = l := by
    rw [Nat.card_Icc]
    omega
  calc
    ‖activityComplementOperator D‖ ^ 2 ≤ _ := hsplit
    _ ≤ (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ((∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1 D‖ ^ 2) + b)) + b :=
      add_le_add hsum houter
    _ = (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1 D‖ ^ 2) +
        (l : ℝ) * b := by
      have hsumconst :
          (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)}, b) =
            ((Finset.Icc 1 (l - 1)).card : ℝ) * b := by
        change (∑ i ∈ (Finset.Icc 1 (l - 1)).attach, b) = _
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_attach]
      rw [Finset.sum_add_distrib, hsumconst]
      have hcast : ((Finset.Icc 1 (l - 1)).card : ℝ) + 1 = (l : ℝ) := by
        exact_mod_cast hcard
      rw [← hcast]
      ring

/-- Reindex interior spectral blocks by the total input and output weight. -/
def spectralInteriorTotalWeightEquiv (l : ℕ) :
    (Σ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
      {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)}) ≃
    (Σ k : {k : ℕ // k ∈ Finset.Icc 2 l},
      {i : ℕ // i ∈ Finset.Icc 1 (k.1 - 1)}) where
  toFun p :=
    ⟨⟨p.1.1 + p.2.1, by
      have hi := Finset.mem_Icc.mp p.1.2
      have hj := Finset.mem_Icc.mp p.2.2
      simp only [Finset.mem_Icc]
      omega⟩,
     ⟨p.1.1, by
      have hj := Finset.mem_Icc.mp p.2.2
      have hi := Finset.mem_Icc.mp p.1.2
      simp only [Finset.mem_Icc]
      omega⟩⟩
  invFun p :=
    ⟨⟨p.2.1, by
      have hk := Finset.mem_Icc.mp p.1.2
      have hi := Finset.mem_Icc.mp p.2.2
      simp only [Finset.mem_Icc]
      omega⟩,
     ⟨p.1.1 - p.2.1, by
      have hk := Finset.mem_Icc.mp p.1.2
      have hi := Finset.mem_Icc.mp p.2.2
      simp only [Finset.mem_Icc]
      omega⟩⟩
  left_inv p := by
    rcases p with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have h : i + j - i = j := by omega
    dsimp
    simp only [h]
  right_inv p := by
    rcases p with ⟨⟨k, hk⟩, ⟨i, hi⟩⟩
    have hi' : 1 ≤ i ∧ i ≤ k - 1 := by
      simpa only using (Finset.mem_Icc.mp hi)
    have h : i + (k - i) = k := by omega
    dsimp
    simp [h]
    exact (Subtype.heq_iff_coe_eq (by intro x; simp only [h])).2 rfl

/-- The paper's triangular double sum is a total-weight sum. -/
theorem spectralInterior_sum_reindex
    (f : ℕ → ℕ → ℝ) (l : ℕ) :
    (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
      ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)}, f i.1 j.1) =
    ∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (k.1 - 1)},
        f i.1 (k.1 - i.1) := by
  classical
  calc
    _ = ∑ p : (Σ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
          {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)}), f p.1.1 p.2.1 := by
        rw [Fintype.sum_sigma]
    _ = ∑ p : (Σ k : {k : ℕ // k ∈ Finset.Icc 2 l},
          {i : ℕ // i ∈ Finset.Icc 1 (k.1 - 1)}),
          f p.2.1 (p.1.1 - p.2.1) := by
        apply Fintype.sum_equiv (spectralInteriorTotalWeightEquiv l)
        intro p
        rcases p with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        dsimp [spectralInteriorTotalWeightEquiv]
        have hji := (Finset.mem_Icc.mp hj).2
        congr 1
        omega
    _ = _ := by rw [Fintype.sum_sigma]

/-- At total weight `k ≥ 2`, the two axes and the interior partition the block sum. -/
theorem spectralTotalWeight_sum_split (f : ℕ → ℕ → ℝ) (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (k + 1), f i (k - i)) =
      f 0 k + f k 0 +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (k - 1)}, f i.1 (k - i.1) := by
  have hset : Finset.range k = insert 0 (Finset.Icc 1 (k - 1)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [Finset.sum_range_succ, hset, Finset.sum_insert (by simp)]
  have hattach :
      (∑ i ∈ Finset.Icc 1 (k - 1), f i (k - i)) =
        ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (k - 1)}, f i.1 (k - i.1) := by
    change (∑ i ∈ Finset.Icc 1 (k - 1), f i (k - i)) =
      ∑ i ∈ (Finset.Icc 1 (k - 1)).attach, f i.1 (k - i.1)
    exact (Finset.sum_attach (Finset.Icc 1 (k - 1)) (fun i => f i (k - i))).symm
  rw [hattach]
  simp only [Nat.sub_zero, Nat.sub_self]
  ring

/-- The full finite spectral sum is the two mixed axes plus the paper's interior triangle. -/
theorem spectralTotalWeight_sum_eq_axes_add_interior
    (f : ℕ → ℕ → ℝ) (l : ℕ) :
    (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
      ∑ i ∈ Finset.range (k.1 + 1), f i (k.1 - i)) =
      (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l}, f 0 k.1) +
      (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l}, f k.1 0) +
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)}, f i.1 j.1) := by
  have hpoint (k : {k : ℕ // k ∈ Finset.Icc 2 l}) :
      (∑ i ∈ Finset.range (k.1 + 1), f i (k.1 - i)) =
        f 0 k.1 + f k.1 0 +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (k.1 - 1)},
            f i.1 (k.1 - i.1) :=
    spectralTotalWeight_sum_split f k.1 (Finset.mem_Icc.mp k.property).1
  calc
    _ = ∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
          (f 0 k.1 + f k.1 0 +
            ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (k.1 - 1)},
              f i.1 (k.1 - i.1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hpoint k
    _ = (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l}, f 0 k.1) +
        (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l}, f k.1 0) +
        (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (k.1 - 1)},
            f i.1 (k.1 - i.1)) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by rw [spectralInterior_sum_reindex]

/-- The paper's spectral block coefficient is symmetric in input and output weights. -/
theorem sharkBlockCoefficient_comm (q n i j : ℕ) :
    sharkBlockCoefficient q n i j = sharkBlockCoefficient q n j i := by
  unfold sharkBlockCoefficient
  rw [add_comm i j]
  ring

/-- The coefficient used when a spectral block has output weight `i` and input weight `j`. -/
noncomputable def sharkSpectralBlockTerm (q n : ℕ) (σ : ℝ) (i j : ℕ) : ℝ :=
  σ ^ (2 * (i + j)) *
    (sharkBlockCoefficient q n i j /
      (Real.sqrt (q : ℝ) - 1) ^ (2 * n - 2 * (i + j)))

theorem sharkSpectralBlockTerm_comm (q n : ℕ) (σ : ℝ) (i j : ℕ) :
    sharkSpectralBlockTerm q n σ i j = sharkSpectralBlockTerm q n σ j i := by
  simp only [sharkSpectralBlockTerm, add_comm i j, sharkBlockCoefficient_comm]

/-- The sum of the paper's block coefficients at total weight `k` is its `C(n,k)` term. -/
theorem sharkSpectralBlockTerm_totalWeight_sum
    (q n k : ℕ) (σ : ℝ) :
    (∑ i ∈ Finset.range (k + 1), sharkSpectralBlockTerm q n σ i (k - i)) =
      σ ^ (2 * k) *
        (sharkCoefficient q n k /
          (Real.sqrt (q : ℝ) - 1) ^ (2 * n - 2 * k)) := by
  let d : ℝ := (Real.sqrt (q : ℝ) - 1) ^ (2 * n - 2 * k)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      sharkSpectralBlockTerm q n σ i (k - i) =
        σ ^ (2 * k) * (sharkBlockCoefficient q n i (k - i) / d) := by
    have hik : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    simp only [sharkSpectralBlockTerm, Nat.add_sub_of_le hik, d]
  calc
    _ = ∑ i ∈ Finset.range (k + 1),
          σ ^ (2 * k) * (sharkBlockCoefficient q n i (k - i) / d) := by
        exact Finset.sum_congr rfl hterm
    _ = σ ^ (2 * k) *
          ((∑ i ∈ Finset.range (k + 1), sharkBlockCoefficient q n i (k - i)) / d) := by
        simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [sharkBlockCoefficient_sum_eq_sharkCoefficient]

/-- The paper's two mixed sums and interior sum combine to the closed-form `C(n,k)` sum. -/
theorem sharkSpectralBlockTerm_axes_interior_eq_closed
    (q n : ℕ) (σ : ℝ) (l : ℕ) :
    (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l}, sharkSpectralBlockTerm q n σ 0 k.1) +
    (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l}, sharkSpectralBlockTerm q n σ k.1 0) +
    (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
      ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
        sharkSpectralBlockTerm q n σ i.1 j.1) =
    ∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
      sharkCoefficient q n k.1 * σ ^ (2 * k.1) /
        (Real.sqrt (q : ℝ) - 1) ^ (2 * n - 2 * k.1) := by
  calc
    _ = ∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
          ∑ i ∈ Finset.range (k.1 + 1),
            sharkSpectralBlockTerm q n σ i (k.1 - i) :=
      (spectralTotalWeight_sum_eq_axes_add_interior
        (sharkSpectralBlockTerm q n σ) l).symm
    _ = ∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
          σ ^ (2 * k.1) *
            (sharkCoefficient q n k.1 /
              (Real.sqrt (q : ℝ) - 1) ^ (2 * n - 2 * k.1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sharkSpectralBlockTerm_totalWeight_sum q n k.1 σ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The paper's `V⊥ → V⊥` block, with its interior terms replaced by their MDS coefficients. -/
theorem keyedSharkTwoCore_activityComplement_paperCoefficient_le
    (u : A) (hu : u ≠ 0) {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n)
    (hq : 3 ≤ Fintype.card A) :
    ‖activityComplementOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          sharkSpectralBlockTerm (Fintype.card A) n
            ‖keyedSboxActivityComplementOperator S‖ i.1 j.1) +
      (l : ℝ) * ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  have hbase := keyedSharkTwoCore_activityComplement_paperInteriorTail_le S L l hlo hl
  have hsum :
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          ‖spectralWeightBlockOperator (n := n) i.1 j.1 D‖ ^ 2) ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
        ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
          sharkSpectralBlockTerm (Fintype.card A) n
            ‖keyedSboxActivityComplementOperator S‖ i.1 j.1) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hii := Finset.mem_Icc.mp i.property
    have hjj := Finset.mem_Icc.mp j.property
    have h := keyedSharkTwoCore_spectralWeightBlock_sq_le
      u hu S L hMDS i.1 j.1 (by omega) (by omega) hq
    simpa only [sharkSpectralBlockTerm, D] using h
  exact hbase.trans (add_le_add_right hsum _)

/-- The first mixed spectral term in the coefficient notation used for total-weight assembly. -/
theorem keyedSharkTwoCore_activityToComplement_paperTerm_le
    (u : A) (hu : u ≠ 0) {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n)
    (hq : 3 ≤ Fintype.card A) :
    ‖activityToComplementOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 2 l},
        sharkSpectralBlockTerm (Fintype.card A) n
          ‖keyedSboxActivityComplementOperator S‖ i.1 0) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
  simpa only [sharkSpectralBlockTerm, Nat.add_zero] using
    keyedSharkTwoCore_activityToComplement_paperLowTail_le
      u hu S L hMDS l hlo hl hq

/-- The reverse mixed spectral term in the coefficient notation used for total-weight assembly. -/
theorem keyedSharkTwoCore_activityComplementToActivity_paperTerm_le
    (u : A) (hu : u ≠ 0) {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n)
    (hq : 3 ≤ Fintype.card A) :
    ‖activityComplementToActivityOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (∑ i : {i : ℕ // i ∈ Finset.Icc 2 l},
        sharkSpectralBlockTerm (Fintype.card A) n
          ‖keyedSboxActivityComplementOperator S‖ 0 i.1) +
      ‖keyedSboxActivityComplementOperator S‖ ^ (2 * (l + 1)) := by
  have h := keyedSharkTwoCore_activityComplementToActivity_paperLowTail_le
    u hu S L hMDS l hlo hl hq
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [sharkSpectralBlockTerm_comm]
  simp only [sharkSpectralBlockTerm, Nat.add_zero]

/-- Theorem 7 of the paper, for independently keyed S-boxes. Here `σ` is the
norm of the one-word activity-complement operator. -/
theorem keyedSharkSpectralTerms_general
    (u : A) (hu : u ≠ 0) {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A)
    (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n)
    (hq : 3 ≤ Fintype.card A) :
    let s := Real.sqrt (Fintype.card A : ℝ)
    let C (k : ℕ) : ℝ := (1 + 1 / (s - 1)) ^ k * (Nat.choose (2 * n) k : ℝ) *
      ∑ i ∈ Finset.Icc 1 (k - 1), (Nat.choose (2 * n - k) (n - i) : ℝ) * 2 ^ i
    let σ := ‖keyedSboxActivityComplementOperator S‖
    ‖activityComplementToActivityOperator
        (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 +
      ‖activityToComplementOperator
        (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 +
      ‖activityComplementOperator
        (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ^ 2 ≤
      (l + 2 : ℕ) * σ ^ (2 * (l + 1)) +
        ∑ k ∈ Finset.Icc 2 l, C k * σ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) := by
  intro s C σ
  let t := σ ^ (2 * (l + 1))
  let F₀ : ℝ := ∑ i : {i : ℕ // i ∈ Finset.Icc 2 l},
    sharkSpectralBlockTerm (Fintype.card A) n σ 0 i.1
  let F₁ : ℝ := ∑ i : {i : ℕ // i ∈ Finset.Icc 2 l},
    sharkSpectralBlockTerm (Fintype.card A) n σ i.1 0
  let G : ℝ := ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (l - 1)},
    ∑ j : {j : ℕ // j ∈ Finset.Icc 1 (l - i.1)},
      sharkSpectralBlockTerm (Fintype.card A) n σ i.1 j.1
  have h₀ := keyedSharkTwoCore_activityComplementToActivity_paperTerm_le
    u hu S L hMDS l hlo hl hq
  have h₁ := keyedSharkTwoCore_activityToComplement_paperTerm_le
    u hu S L hMDS l hlo hl hq
  have h₂ := keyedSharkTwoCore_activityComplement_paperCoefficient_le
    u hu S L hMDS l hlo hl hq
  have hbound := add_le_add (add_le_add h₀ h₁) h₂
  have hcoeff := sharkSpectralBlockTerm_axes_interior_eq_closed
    (Fintype.card A) n σ l
  change F₀ + F₁ + G = _ at hcoeff
  calc
    _ ≤ (F₀ + t) + (F₁ + t) + (G + (l : ℝ) * t) := hbound
    _ = (l + 2 : ℕ) * t + (F₀ + F₁ + G) := by
      push_cast
      ring
    _ = _ := by
      rw [hcoeff]
      change (l + 2 : ℕ) * t +
        (∑ k : {k : ℕ // k ∈ Finset.Icc 2 l},
          sharkCoefficient (Fintype.card A) n k.1 * σ ^ (2 * k.1) /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^ (2 * n - 2 * k.1)) =
        (l + 2 : ℕ) * t +
        (∑ k ∈ Finset.Icc 2 l,
          sharkCoefficient (Fintype.card A) n k * σ ^ (2 * k) /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^ (2 * n - 2 * k))
      congr 1
      change (∑ k ∈ (Finset.Icc 2 l).attach,
          sharkCoefficient (Fintype.card A) n k.1 * σ ^ (2 * k.1) /
            (Real.sqrt (Fintype.card A : ℝ) - 1) ^ (2 * n - 2 * k.1)) = _
      exact Finset.sum_attach (Finset.Icc 2 l) (fun k =>
        sharkCoefficient (Fintype.card A) n k * σ ^ (2 * k) /
          (Real.sqrt (Fintype.card A : ℝ) - 1) ^ (2 * n - 2 * k))

/-- The closed-form SHARK coefficient is nonnegative in the paper's field-size range. -/
theorem sharkCoefficient_nonneg (q n k : ℕ) (hq : 2 ≤ q) :
    0 ≤ sharkCoefficient q n k := by
  have hqreal : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsqrt : 1 < Real.sqrt (q : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hqreal
  have hd : 0 < Real.sqrt (q : ℝ) - 1 := by linarith
  unfold sharkCoefficient
  positivity

/-- Theorem 3 for independently keyed S-boxes. -/
theorem theorem3_keyed_of_spectralBias_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (hMDS : IsMDS L) (hq : 4 ≤ Fintype.card A) (hn : 2 ≤ n)
    (σ : ℝ)
    (hσ : ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
      uniformDifferenceDistributionMatrix A‖ ≤ σ)
    (l : ℕ) (hlo : 1 ≤ l) (hl : l ≤ n - 1) :
    let s := Real.sqrt (Fintype.card A : ℝ)
    let C (k : ℕ) : ℝ := (1 + 1 / (s - 1)) ^ k * (Nat.choose (2 * n) k : ℝ) *
      ∑ i ∈ Finset.Icc 1 (k - 1), (Nat.choose (2 * n - k) (n - i) : ℝ) * 2 ^ i
    ‖differenceDistributionMatrix (keyedSharkTwoCore S L) -
      uniformDifferenceDistributionMatrix (State A n)‖ ^ 2 ≤
      (2 / (s - 1)) ^ (2 * n) +
        ∑ k ∈ Finset.Icc 2 l, C k * σ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) +
        (l + 2 : ℕ) * σ ^ (2 * (l + 1)) := by
  intro s C
  let D := differenceDistributionMatrix (keyedSharkTwoCore S L)
  let U := uniformDifferenceDistributionMatrix (State A n)
  let σ₀ := ‖keyedSboxActivityComplementOperator S‖
  have hσ₀ : σ₀ ≤ σ := (keyedSboxActivityComplementOperator_norm_le_sub_uniform S).trans hσ
  have hσ₀0 : 0 ≤ σ₀ := norm_nonneg (keyedSboxActivityComplementOperator S)
  have hd : 0 < s - 1 := by
    have hqreal : (1 : ℝ) < Fintype.card A := by
      exact_mod_cast (show 1 < Fintype.card A by omega)
    have hs : 1 < s := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hqreal
    linarith
  -- Theorem 6 bounds the block `V → V`.
  have htrunc : ‖activityTruncatedOperator (D - U)‖ ^ 2 ≤ (2 / (s - 1)) ^ (2 * n) := by
    have h := keyedSharkTwoCore_truncatedNorm_le_closedForm S L hMDS hq hn
    have hbase : 0 ≤ (2 / (s - 1)) ^ n := pow_nonneg (div_nonneg (by norm_num) hd.le) n
    have hsq := (sq_le_sq₀ (norm_nonneg (activityTruncatedOperator (D - U))) hbase).2 h
    simpa only [pow_mul, mul_comm] using hsq
  -- Theorem 7 bounds the other three blocks, with `σ₀` in place of `σ`.
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : A)
  have hspec :
      ‖activityComplementToActivityOperator D‖ ^ 2 +
          ‖activityToComplementOperator D‖ ^ 2 + ‖activityComplementOperator D‖ ^ 2 ≤
        (l + 2 : ℕ) * σ₀ ^ (2 * (l + 1)) +
          ∑ k ∈ Finset.Icc 2 l, C k * σ₀ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) :=
    keyedSharkSpectralTerms_general u hu S L hMDS l hlo (by omega) (by omega)
  -- The bound of Theorem 7 increases with `σ`.
  have hmono :
      (l + 2 : ℕ) * σ₀ ^ (2 * (l + 1)) +
          ∑ k ∈ Finset.Icc 2 l, C k * σ₀ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) ≤
        (l + 2 : ℕ) * σ ^ (2 * (l + 1)) +
          ∑ k ∈ Finset.Icc 2 l, C k * σ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ₀0 hσ₀ _) (Nat.cast_nonneg _)
    · apply Finset.sum_le_sum
      intro k _
      have hc : 0 ≤ C k / (s - 1) ^ (2 * n - 2 * k) :=
        div_nonneg (sharkCoefficient_nonneg (Fintype.card A) n k (by omega))
          (pow_nonneg hd.le _)
      calc
        C k * σ₀ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) =
            C k / (s - 1) ^ (2 * n - 2 * k) * σ₀ ^ (2 * k) := by ring
        _ ≤ C k / (s - 1) ^ (2 * n - 2 * k) * σ ^ (2 * k) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ₀0 hσ₀ _) hc
        _ = C k * σ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) := by ring
  -- The four blocks together bound `‖D − U‖`.
  have hblocks := activity_fourBlock_norm_sq_le (D - U)
  rw [activityComplementToActivityOperator_sub_uniform,
    activityToComplementOperator_sub_uniform,
    activityComplementOperator_sub_uniform] at hblocks
  change ‖D - U‖ ^ 2 ≤ (2 / (s - 1)) ^ (2 * n) +
    ∑ k ∈ Finset.Icc 2 l, C k * σ ^ (2 * k) / (s - 1) ^ (2 * n - 2 * k) +
    (l + 2 : ℕ) * σ ^ (2 * (l + 1))
  linarith

/-- The paper's decimal superbox bound is stronger than the rational bound used
by the exact Theorem 5 certificate. -/
theorem paper_superbox_decimal_le_rational :
    (2 : ℝ) ^ (-(10.146 : ℝ)) ≤ 1 / 1133 := by
  have hnum : (1133 : ℝ) ^ (500 : ℕ) ≤ (2 : ℝ) ^ (5073 : ℕ) := by
    norm_num
  have hpow : (1133 : ℝ) ^ (500 : ℝ) ≤
      ((2 : ℝ) ^ ((5073 : ℝ) / 500)) ^ (500 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    convert hnum using 1 <;> norm_num
  have hbase : (1133 : ℝ) ≤ (2 : ℝ) ^ ((5073 : ℝ) / 500) :=
    (Real.rpow_le_rpow_iff (by norm_num)
      (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0 : ℝ) < 500)).mp hpow
  have hpos : 0 < (2 : ℝ) ^ ((5073 : ℝ) / 500) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrecip : ((2 : ℝ) ^ ((5073 : ℝ) / 500))⁻¹ ≤ (1133 : ℝ)⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hbase
  convert hrecip using 1
  · rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  · norm_num

/-- Theorem 5 for independently keyed SHARK with four 32-bit words: the
paper's superbox bound `‖Dˢ − U‖ ≤ 2^(-10.146)` gives `‖D − U‖ ≤ 2^(-39)`.
Theorem 4 supplies the premise for the AES superbox. -/
theorem theorem5_keyedShark_of_paper_differenceDistributionMatrix_bound
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (hcard : Fintype.card A = 2 ^ 32)
    (S : κ → A ≃ A) (L : State A 4 ≃+ State A 4) (hMDS : IsMDS L)
    (hsuperbox :
      ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
        uniformDifferenceDistributionMatrix A‖ ≤
          (2 : ℝ) ^ (-(10.146 : ℝ))) :
    ‖differenceDistributionMatrix (keyedSharkTwoCore S L) -
      uniformDifferenceDistributionMatrix (State A 4)‖ ≤
        1 / (2 : ℝ) ^ 39 := by
  -- Theorem 3 with `q = 2^32`, `n = 4`, `σ = 1/1133` and `l = 3`.
  have h := theorem3_keyed_of_spectralBias_le S L hMDS (by rw [hcard]; norm_num)
    (by omega) (1 / 1133) (hsuperbox.trans paper_superbox_decimal_le_rational)
    3 (by omega) (by omega)
  rw [hcard] at h
  have hsqrt : Real.sqrt (4294967296 : ℝ) = 65536 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 65536 by norm_num) using 1; norm_num
  have hsq : ‖differenceDistributionMatrix (keyedSharkTwoCore S L) -
      uniformDifferenceDistributionMatrix (State A 4)‖ ^ 2 ≤ (1 / (2 : ℝ) ^ 39) ^ 2 := by
    refine le_trans h ?_
    norm_num [hsqrt, Finset.sum_Icc_succ_top, Nat.choose]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Theorem 3 of the paper; the statement is in `Theorem3.lean`. -/
theorem theorem3_shark : Theorem3 := by
  intro A _ _ _ n S L hMDS hq hn σ hσ l hlo hl
  rw [sharkTwoCore_differenceDistributionMatrix_eq_keyed]
  exact theorem3_keyed_of_spectralBias_le (fun _ : Unit => S) L hMDS hq hn σ hσ l hlo hl

end PairwiseIndependence
