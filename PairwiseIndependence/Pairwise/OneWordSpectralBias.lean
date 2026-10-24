import PairwiseIndependence.Pairwise.KeyedShark

/-!
# The one-word spectral parameter

The paper identifies the third singular value of a permutation family's
difference-distribution matrix with the norm of that matrix minus the uniform
benchmark.  This file proves that the same number is the norm of the
restriction to the orthogonal complement of the two activity directions.
The spectral estimates use the restricted operator because it acts directly
on the paper's `W_l` spaces.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

variable {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
  [Fintype κ]

/-- The uniform difference-distribution matrix fixes the zero-difference
indicator. -/
theorem uniform_word_fixes_zeroIndicator :
    uniformDifferenceDistributionMatrix A *ᵥ wordZeroIndicator (A := A) =
      wordZeroIndicator (A := A) := by
  classical
  funext b
  simp [Matrix.mulVec, dotProduct, uniformDifferenceDistributionMatrix_apply,
    wordZeroIndicator]

/-- The uniform difference-distribution matrix fixes the all-ones indicator.
The cardinality hypothesis is automatic for the paper's word alphabets. -/
theorem uniform_word_fixes_allIndicator
    (hcard : 2 ≤ Fintype.card A) :
    uniformDifferenceDistributionMatrix A *ᵥ wordAllIndicator (A := A) =
      wordAllIndicator (A := A) := by
  classical
  funext b
  change (∑ a : A, uniformDifferenceDistributionMatrix A b a * 1) = 1
  simp only [mul_one]
  by_cases hb : b = 0
  · subst b
    simp [uniformDifferenceDistributionMatrix_apply]
  · have hterm (a : A) :
        uniformDifferenceDistributionMatrix A b a =
          if a = 0 then 0 else 1 / ((Fintype.card A - 1 : ℕ) : ℝ) := by
      by_cases ha : a = 0 <;>
        simp [uniformDifferenceDistributionMatrix_apply, hb, ha]
    simp_rw [hterm]
    rw [sum_except_zero]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hnonzero : ((Fintype.card A - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : Fintype.card A - 1 ≠ 0)
    have hsub : ((Fintype.card A - 1 : ℕ) : ℝ) =
        (Fintype.card A : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : 1 ≤ Fintype.card A)
    rw [hsub]
    have hnonzero' : (Fintype.card A : ℝ) - 1 ≠ 0 := by
      rw [← hsub]
      exact hnonzero
    field_simp

/-- The uniform difference-distribution matrix acts as the identity on the
paper's two-dimensional one-word activity space. -/
theorem uniform_word_fixes_activity
    (hcard : 2 ≤ Fintype.card A) (v : A → ℝ)
    (hv : v ∈ wordActivitySubspace (A := A)) :
    uniformDifferenceDistributionMatrix A *ᵥ v = v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rw [hx]
        exact uniform_word_fixes_zeroIndicator
      · rw [hx]
        exact uniform_word_fixes_allIndicator hcard
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mulVec_smul, hx]

/-- The uniform benchmark is precisely orthogonal projection onto the
two one-word activity directions. -/
theorem uniform_word_eq_activity_projection
    (hcard : 2 ≤ Fintype.card A) (v : EuclideanSpace ℝ A) :
    Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (uniformDifferenceDistributionMatrix A) v =
      (wordActivityHilbertSubspace (A := A)).starProjection v := by
  let K := wordActivityHilbertSubspace (A := A)
  let Q := Kᗮ
  have hsplit : K.starProjection v + Q.starProjection v = v :=
    K.starProjection_add_starProjection_orthogonal v
  have hK : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (uniformDifferenceDistributionMatrix A) (K.starProjection v) =
        K.starProjection v := by
    apply (WithLp.linearEquiv 2 ℝ (A → ℝ)).injective
    simpa only [WithLp.linearEquiv_apply, Matrix.ofLp_toEuclideanCLM] using
      uniform_word_fixes_activity hcard _
        ((mem_wordActivityHilbertSubspace_iff _).mp
          (K.starProjection_apply_mem v))
  have hQ : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (uniformDifferenceDistributionMatrix A) (Q.starProjection v) = 0 := by
    apply (WithLp.linearEquiv 2 ℝ (A → ℝ)).injective
    change uniformDifferenceDistributionMatrix A *ᵥ
      ((WithLp.linearEquiv 2 ℝ (A → ℝ)) (Q.starProjection v)) = 0
    exact uniformDifferenceDistributionMatrix_word_mulVec_eq_zero_of_orthogonal
      _ ((inWordActivityOrthogonalComplement_iff_mem_orthogonal _).mpr
        (Q.starProjection_apply_mem v))
  conv_lhs => rw [← hsplit]
  rw [map_add, hK, hQ, add_zero]

/-- The norm of the averaged one-word difference-distribution matrix minus
the uniform benchmark equals the norm used on the activity complement in
the SHARK spectral proof. The paper calls the left-hand side its third
singular value (via its singular-value lemma). -/
theorem keyedSboxActivityComplementOperator_norm_eq_sub_uniform
    [Nonempty κ] (S : κ → A ≃ A)
    (hcard : 2 ≤ Fintype.card A) :
    ‖keyedSboxActivityComplementOperator S‖ =
      ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
        uniformDifferenceDistributionMatrix A‖ := by
  let K := wordActivityHilbertSubspace (A := A)
  let Q := Kᗮ
  let D := differenceDistributionMatrix (fun key : κ => fun a : A => S key a)
  let U := uniformDifferenceDistributionMatrix A
  let T := keyedSboxActivityComplementOperator S
  let F := Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (D - U)
  have hpoint (v : EuclideanSpace ℝ A) :
      F v = ((T (Q.orthogonalProjection v) : Q) : EuclideanSpace ℝ A) := by
    change Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (D - U) v = _
    rw [matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply,
      keyedSbox_activity_blockDiagonal S v,
      uniform_word_eq_activity_projection hcard v]
    exact add_sub_cancel_left _ _
  have hupper : ‖D - U‖ ≤ ‖T‖ := by
    change ‖F‖ ≤ ‖T‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro v
    rw [hpoint]
    calc
      ‖((T (Q.orthogonalProjection v) : Q) : EuclideanSpace ℝ A)‖ =
          ‖T (Q.orthogonalProjection v)‖ := (Submodule.coe_norm _).symm
      _ ≤ ‖T‖ * ‖Q.orthogonalProjection v‖ := T.le_opNorm _
      _ ≤ ‖T‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_left
          (Q.norm_orthogonalProjection_apply_le v) (norm_nonneg T)
  exact le_antisymm
    (keyedSboxActivityComplementOperator_norm_le_sub_uniform S) hupper

end PairwiseIndependence
