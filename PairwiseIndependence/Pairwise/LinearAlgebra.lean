import PairwiseIndependence.Pairwise.DifferenceDistribution
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Linear algebra for difference-distribution matrices

This module contains norm estimates without any probability definitions.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

omit [AddCommGroup A] in
/-- Subtracting real matrices subtracts their Euclidean continuous linear
maps. This is used to remove the uniform matrix from spectral blocks. -/
theorem matrix_toEuclideanCLM_sub (M N : Matrix A A ℝ) :
    Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (M - N) =
      Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) M -
        Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) N := by
  apply ContinuousLinearMap.ext
  intro v
  apply (WithLp.linearEquiv 2 ℝ (A → ℝ)).injective
  change (M - N) *ᵥ ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v) =
    M *ᵥ ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v) -
      N *ᵥ ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v)
  exact Matrix.sub_mulVec M N _

omit [AddCommGroup A] [DecidableEq A] in
private theorem column_one_sum_sq_le_card_mul_two_sum_sq (v : A → ℝ) :
    (∑ b : A, |v b|) ^ 2 ≤
      (Fintype.card A : ℝ) * ∑ b : A, (v b) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun b : A => |v b|)
  simpa only [Finset.card_univ, sq_abs] using h

omit [AddCommGroup A] [DecidableEq A] in
private theorem column_one_sum_sq_le_card_mul_norm_sq
    (v : EuclideanSpace ℝ A) :
    (∑ b : A, |v b|) ^ 2 ≤ (Fintype.card A : ℝ) * ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [Real.norm_eq_abs, sq_abs] using
    column_one_sum_sq_le_card_mul_two_sum_sq (fun b => v b)

omit [AddCommGroup A] [DecidableEq A] in
private theorem column_norm_sq_le_card_mul_entry_bound_sq
    (N : Matrix A A ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hentry : ∀ b a, |N b a| ≤ p) (a : A) :
    ‖(WithLp.toLp 2 (fun b : A => N b a) : EuclideanSpace ℝ A)‖ ^ 2 ≤
      (Fintype.card A : ℝ) * p ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    (∑ b : A,
      ‖(WithLp.toLp 2 (fun c : A => N c a) : EuclideanSpace ℝ A) b‖ ^ 2) ≤
        ∑ _b : A, p ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      change |N b a| ^ 2 ≤ p ^ 2
      nlinarith [hentry b a, abs_nonneg (N b a)]
    _ = _ := by simp

/-- Mixed one/two norm estimate used in Lemma 6. If every entry of the right
matrix has magnitude at most `p`, its product with a left matrix has one norm
at most the state size times `p` times the spectral norm of the left matrix. -/
theorem matrixOneNorm_mul_le_card_mul_entry_bound_mul_twoNorm
    (M N : Matrix A A ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hentry : ∀ b a, |N b a| ≤ p) :
    matrixOneNorm (M * N) ≤ (Fintype.card A : ℝ) * p * ‖M‖ := by
  rw [matrixOneNorm_le_iff]
  intro a
  let v : EuclideanSpace ℝ A := WithLp.toLp 2 (fun b : A => N b a)
  let w : EuclideanSpace ℝ A :=
    (EuclideanSpace.equiv A ℝ).symm (M *ᵥ v)
  have hwentry (b : A) : w b = (M * N) b a := by
    simp [w, v, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]
  have hw : ‖w‖ ≤ ‖M‖ * ‖v‖ := Matrix.l2_opNorm_mulVec M v
  have hv : ‖v‖ ^ 2 ≤ (Fintype.card A : ℝ) * p ^ 2 :=
    column_norm_sq_le_card_mul_entry_bound_sq N p hp hentry a
  have hcol :
      (∑ b : A, |(M * N) b a|) ^ 2 ≤
        (Fintype.card A : ℝ) * ‖w‖ ^ 2 := by
    simpa only [hwentry] using column_one_sum_sq_le_card_mul_norm_sq w
  have hsq :
      (∑ b : A, |(M * N) b a|) ^ 2 ≤
        ((Fintype.card A : ℝ) * p * ‖M‖) ^ 2 := by
    calc
      _ ≤ (Fintype.card A : ℝ) * ‖w‖ ^ 2 := hcol
      _ ≤ (Fintype.card A : ℝ) * (‖M‖ * ‖v‖) ^ 2 := by gcongr
      _ ≤ (Fintype.card A : ℝ) *
          (‖M‖ ^ 2 * ((Fintype.card A : ℝ) * p ^ 2)) := by
        rw [mul_pow]
        gcongr
      _ = _ := by ring
  have hsum : 0 ≤ ∑ b : A, |(M * N) b a| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound : 0 ≤ (Fintype.card A : ℝ) * p * ‖M‖ := by positivity
  nlinarith

/-- The analytic core of the paper's Conversion Lemma (Lemma 6). The two
matrix hypotheses record exactly the centering identity and the centered
entry bound used by the proof. -/
theorem conversion_core
    (D₁ D₂ : Matrix A A ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hcenter :
      D₂ * D₁ - uniformDifferenceDistributionMatrix A =
        (D₂ - uniformDifferenceDistributionMatrix A) *
          (D₁ - uniformDifferenceDistributionMatrix A))
    (hentry : ∀ b a,
      |(D₁ - uniformDifferenceDistributionMatrix A) b a| ≤ p) :
    matrixOneNorm (D₂ * D₁ - uniformDifferenceDistributionMatrix A) ≤
      (Fintype.card A : ℝ) * p *
        ‖D₂ - uniformDifferenceDistributionMatrix A‖ := by
  rw [hcenter]
  exact matrixOneNorm_mul_le_card_mul_entry_bound_mul_twoNorm
    _ _ p hp hentry

omit [AddCommGroup A] in
/-- Positive powers of a matrix preserve a stationary projection on the right. -/
theorem power_mul_stationary_projection
    (D U : Matrix A A ℝ) (hDU : D * U = U) :
    ∀ r : ℕ, D ^ (r + 1) * U = U
  | 0 => by simpa using hDU
  | r + 1 => by
      rw [show r + 1 + 1 = (r + 1) + 1 by omega, pow_succ, mul_assoc, hDU]
      exact power_mul_stationary_projection D U hDU r

omit [AddCommGroup A] in
/-- The paper's identity `D^r - U = (D - U)^r` for positive `r`. -/
theorem centered_power
    (D U : Matrix A A ℝ)
    (hDU : D * U = U) (hUD : U * D = U) (hUU : U * U = U) :
    ∀ r : ℕ, D ^ (r + 1) - U = (D - U) ^ (r + 1)
  | 0 => by simp
  | r + 1 => by
      have ih := centered_power D U hDU hUD hUU r
      have hpow := power_mul_stationary_projection D U hDU r
      conv_lhs => rw [pow_succ]
      conv_rhs => rw [pow_succ, ← ih]
      rw [sub_mul, mul_sub, mul_sub, hpow, hUD, hUU]
      abel

omit [AddCommGroup A] [DecidableEq A] in
/-- A finite-dimensional Cauchy--Schwarz estimate for matrix-vector
multiplication, expressed as sums of squares. -/
theorem matrix_mulVec_sum_sq_le_frobeniusSq
    (M : Matrix A A ℝ) (v : A → ℝ) :
    (∑ i : A, ((M *ᵥ v) i) ^ 2) ≤
      (∑ i : A, ∑ j : A, (M i j) ^ 2) *
        (∑ j : A, (v j) ^ 2) := by
  have hrow (i : A) :
      ((M *ᵥ v) i) ^ 2 ≤
        (∑ j : A, (M i j) ^ 2) * (∑ j : A, (v j) ^ 2) := by
    simpa only [Matrix.mulVec, dotProduct] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
        (f := fun j : A => M i j) (g := v))
  calc
    (∑ i : A, ((M *ᵥ v) i) ^ 2) ≤
        ∑ i : A, (∑ j : A, (M i j) ^ 2) *
          (∑ j : A, (v j) ^ 2) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (∑ i : A, ∑ j : A, (M i j) ^ 2) *
          (∑ j : A, (v j) ^ 2) := by rw [Finset.sum_mul]

omit [AddCommGroup A] in
/-- The Euclidean operator norm of a real matrix is at most the square root
of the sum of squares of its entries (its Frobenius norm). -/
theorem matrixTwoNorm_le_sqrt_sum_entries_sq (M : Matrix A A ℝ) :
    ‖M‖ ≤ Real.sqrt (∑ i : A, ∑ j : A, (M i j) ^ 2) := by
  let F : ℝ := ∑ i : A, ∑ j : A, (M i j) ^ 2
  have hF : 0 ≤ F := by
    dsimp [F]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg (M i j)
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hsq := matrix_mulVec_sum_sq_le_frobeniusSq M
    ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v)
  have hv : ‖v‖ ^ 2 =
      ∑ j : A, (((WithLp.linearEquiv 2 ℝ (A → ℝ)) v) j) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq v
  have hw : ‖(Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) M) v‖ ^ 2 =
      ∑ i : A,
        ((M *ᵥ ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v)) i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  have hsq' : ‖(Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) M) v‖ ^ 2 ≤
      F * ‖v‖ ^ 2 := by
    rw [hw, hv]
    exact hsq
  calc
    ‖(Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) M) v‖ =
        Real.sqrt (‖(Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) M) v‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (F * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt F * ‖v‖ := by
      rw [Real.sqrt_mul hF, Real.sqrt_sq (norm_nonneg _)]


section RectangularFrobenius

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The Euclidean operator norm of a rectangular real matrix is at most its Frobenius norm. -/
theorem matrixTwoNorm_le_sqrt_sum_entries_sq_rectangular
    (M : Matrix ι κ ℝ) :
    ‖M‖ ≤ Real.sqrt (∑ i : ι, ∑ j : κ, (M i j) ^ 2) := by
  let F : ℝ := ∑ i : ι, ∑ j : κ, (M i j) ^ 2
  have hF : 0 ≤ F := by
    dsimp [F]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg (M i j)
  rw [Matrix.l2_opNorm_def]
  let T : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := ι) (n := κ) ≪≫ₗ
      LinearMap.toContinuousLinearMap) M
  change ‖T‖ ≤ _
  apply T.opNorm_le_bound (Real.sqrt_nonneg _)
  intro v
  have hrow (i : ι) :
      ((M *ᵥ v) i) ^ 2 ≤
        (∑ j : κ, (M i j) ^ 2) * (∑ j : κ, (v j) ^ 2) := by
    simpa only [Matrix.mulVec, dotProduct] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
        (f := fun j : κ => M i j) (g := v))
  have hsq : (∑ i : ι, ((M *ᵥ v) i) ^ 2) ≤
      F * (∑ j : κ, (v j) ^ 2) := by
    calc
      _ ≤ ∑ i : ι, (∑ j : κ, (M i j) ^ 2) *
          (∑ j : κ, (v j) ^ 2) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by rw [Finset.sum_mul]
  have hv : ‖v‖ ^ 2 = ∑ j : κ, (v j) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq v
  have hw : ‖T v‖ ^ 2 = ∑ i : ι, ((M *ᵥ v) i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  have hsq' : ‖T v‖ ^ 2 ≤ F * ‖v‖ ^ 2 := by
    rw [hw, hv]
    exact hsq
  calc
    ‖T v‖ = Real.sqrt (‖T v‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (F * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt F * ‖v‖ := by
      rw [Real.sqrt_mul hF, Real.sqrt_sq (norm_nonneg _)]

end RectangularFrobenius

end PairwiseIndependence
