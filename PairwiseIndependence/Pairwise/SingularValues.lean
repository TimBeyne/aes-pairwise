import PairwiseIndependence.Pairwise.OneWordSpectralBias
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Ordered singular values of difference-distribution matrices

For a real matrix, the paper defines singular values as the square roots of
the eigenvalues of its transpose-times-self Gram matrix, in decreasing order.
Mathlib supplies the ordered eigenvalues of a self-adjoint matrix. The
definitions here make the paper's *third singular value* an actual Lean term,
distinct from the already-proved full-matrix norm `‖D - U‖`.
-/

namespace PairwiseIndependence

open scoped Matrix Matrix.Norms.L2Operator

private theorem secondEigenvalue_eq_one_of_two_fixed_directions
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ}
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℝ E = m) (hm2 : 2 ≤ m)
    (hfixed : 2 ≤ Module.finrank ℝ (Module.End.eigenspace T 1))
    (hle : ∀ i : Fin m, hT.eigenvalues hm i ≤ 1) :
    hT.eigenvalues hm ⟨1, hm2⟩ = 1 := by
  let j : Fin m := ⟨1, hm2⟩
  let z : Fin m := ⟨0, by omega⟩
  apply le_antisymm (hle j)
  by_contra hne
  have hj : hT.eigenvalues hm j < 1 := lt_of_not_ge hne
  let b := hT.eigenvectorBasis hm
  have htail (i : Fin m) (hi : i ≠ z) : hT.eigenvalues hm i < 1 := by
    have hji : j ≤ i := by
      apply Fin.le_iff_val_le_val.mpr
      have hiz : i.val ≠ 0 := by
        intro heq
        exact hi (Fin.ext heq)
      dsimp [j]
      omega
    exact lt_of_le_of_lt (hT.eigenvalues_antitone hm hji) hj
  have hsubset : Module.End.eigenspace T 1 ≤ Submodule.span ℝ ({b z} : Set E) := by
    intro v hv
    have hvT : T v = v := by
      simpa only [one_smul] using (Module.End.mem_eigenspace_iff.mp hv)
    have hcoord (i : Fin m) (hi : i ≠ z) : b.repr v i = 0 := by
      have h := hT.eigenvectorBasis_apply_self_apply hm v i
      rw [hvT] at h
      have hpos : 0 < 1 - hT.eigenvalues hm i := by
        linarith [htail i hi]
      have hnonzero : 1 - hT.eigenvalues hm i ≠ 0 := ne_of_gt hpos
      have hmul : (1 - hT.eigenvalues hm i) * b.repr v i = 0 := by
        change b.repr v i = hT.eigenvalues hm i * b.repr v i at h
        calc
          (1 - hT.eigenvalues hm i) * b.repr v i =
              b.repr v i - hT.eigenvalues hm i * b.repr v i := by ring
          _ = 0 := sub_eq_zero.mpr h
      exact (mul_eq_zero.mp hmul).resolve_left hnonzero
    have hsum : v = b.repr v z • b z := by
      calc
        v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
        _ = b.repr v z • b z := by
          apply Finset.sum_eq_single z
          · intro i _ hi
            simp [hcoord i hi]
          · simp
    exact Submodule.mem_span_singleton.mpr ⟨b.repr v z, hsum.symm⟩
  have hdimle : Module.finrank ℝ (Module.End.eigenspace T 1) ≤ 1 := by
    exact (Submodule.finrank_mono hsubset).trans
      (by simpa using
        (finrank_span_le_card ({b z} : Set E)))
  omega

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The paper's singular values, sorted from largest to smallest. -/
noncomputable def differenceMatrixSingularValue
    (D : Matrix A A ℝ) (i : Fin (Fintype.card A)) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_transpose_mul_self D).eigenvalues₀ i)

/-- The third singular value appearing in Theorem 3 and the paper's
singular-value lemma. The alphabet must have at least three elements. -/
noncomputable def differenceMatrixThirdSingularValue
    (D : Matrix A A ℝ) (hcard : 3 ≤ Fintype.card A) : ℝ :=
  differenceMatrixSingularValue D ⟨2, hcard⟩

/-- The singular values are nonnegative. -/
theorem differenceMatrixSingularValue_nonneg
    (D : Matrix A A ℝ) (i : Fin (Fintype.card A)) :
    0 ≤ differenceMatrixSingularValue D i :=
  Real.sqrt_nonneg _

/-- The indexing of `differenceMatrixSingularValue` follows the paper's
decreasing-order convention. -/
theorem differenceMatrixSingularValue_antitone
    (D : Matrix A A ℝ) :
    Antitone (differenceMatrixSingularValue D) := by
  intro i j hij
  unfold differenceMatrixSingularValue
  exact Real.sqrt_le_sqrt
    ((Matrix.isHermitian_iff_isSymmetric.mp
      (Matrix.isHermitian_transpose_mul_self D)).eigenvalues_antitone
      finrank_euclideanSpace hij)

/-- Squaring a singular value recovers the corresponding eigenvalue of
`DᵀD`; this records the paper's definition without an implicit sign choice. -/
theorem differenceMatrixSingularValue_sq
    (D : Matrix A A ℝ) (i : Fin (Fintype.card A)) :
    differenceMatrixSingularValue D i ^ 2 =
      (Matrix.isHermitian_transpose_mul_self D).eigenvalues₀ i := by
  unfold differenceMatrixSingularValue
  rw [Real.sq_sqrt]
  let e : Fin (Fintype.card A) ≃ A :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := Matrix.eigenvalues_conjTranspose_mul_self_nonneg D (e i)
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using h

/-- Every singular value is bounded by the Euclidean operator norm of its
matrix. This is the spectral fact used in the paper's singular-value lemma. -/
theorem differenceMatrixSingularValue_le_norm
    (D : Matrix A A ℝ) (i : Fin (Fintype.card A)) :
    differenceMatrixSingularValue D i ≤ ‖D‖ := by
  let G := Dᴴ * D
  let hG : G.IsHermitian := Matrix.isHermitian_transpose_mul_self D
  let e : Fin (Fintype.card A) ≃ A :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let v : EuclideanSpace ℝ A := hG.eigenvectorBasis (e i)
  have hvnorm : ‖v‖ = 1 := hG.eigenvectorBasis.norm_eq_one (e i)
  have hv : G *ᵥ (v : A → ℝ) = (hG.eigenvalues (e i)) • (v : A → ℝ) :=
    hG.mulVec_eigenvectorBasis (e i)
  have hv' : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) G v =
      hG.eigenvalues (e i) • v := by
    apply (WithLp.linearEquiv 2 ℝ (A → ℝ)).injective
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.linearEquiv_apply,
      WithLp.toLp_smul] using hv
  have hEigNonneg : 0 ≤ hG.eigenvalues (e i) :=
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg D (e i)
  have hEigLe : hG.eigenvalues (e i) ≤ ‖G‖ := by
    have h := (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) G).le_opNorm v
    rw [hv', norm_smul, hvnorm] at h
    simpa only [Matrix.cstar_norm_def, Real.norm_eq_abs,
      abs_of_nonneg hEigNonneg, mul_one] using h
  have hGnorm : ‖G‖ ≤ ‖D‖ ^ 2 := by
    calc
      ‖G‖ = ‖Dᴴ * D‖ := rfl
      _ ≤ ‖Dᴴ‖ * ‖D‖ := norm_mul_le _ _
      _ = ‖D‖ ^ 2 := by
        rw [← Matrix.star_eq_conjTranspose, norm_star]
        ring
  have hsq : differenceMatrixSingularValue D i ^ 2 ≤ ‖D‖ ^ 2 := by
    rw [differenceMatrixSingularValue_sq]
    simpa only [Matrix.IsHermitian.eigenvalues, e,
      Equiv.symm_apply_apply] using hEigLe.trans hGnorm
  nlinarith [differenceMatrixSingularValue_nonneg D i, norm_nonneg D]

theorem differenceMatrixThirdSingularValue_nonneg
    (D : Matrix A A ℝ) (hcard : 3 ≤ Fintype.card A) :
    0 ≤ differenceMatrixThirdSingularValue D hcard :=
  differenceMatrixSingularValue_nonneg D ⟨2, hcard⟩

/-- Every singular value of the averaged difference-distribution matrix of
a finite family of permutations is at most one, as in the first part of the
paper's singular-value lemma. -/
theorem keyedDifferenceDistributionMatrix_singularValue_le_one
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (i : Fin (Fintype.card A)) :
    differenceMatrixSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) i ≤ 1 := by
  exact (differenceMatrixSingularValue_le_norm _ i).trans
    (differenceDistributionMatrix_norm_le_one
      (fun key : κ => fun a : A => S key a)
      (fun key => (S key).bijective))

/-- The paper's third singular value is at most one for an independently
keyed permutation family. -/
theorem keyedDifferenceDistributionMatrix_thirdSingularValue_le_one
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A) :
    differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard ≤ 1 :=
  keyedDifferenceDistributionMatrix_singularValue_le_one S ⟨2, hcard⟩

section ActivityDirections

variable [AddCommGroup A]

/-- The paper's two-dimensional word-activity subspace lies in the
eigenvalue-one space of the difference-distribution Gram matrix. -/
theorem keyedDifferenceDistributionMatrix_wordActivity_le_one_eigenspace
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) :
    let D := differenceDistributionMatrix
      (fun key : κ => fun a : A => S key a)
    wordActivityHilbertSubspace (A := A) ≤
      Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℝ) (Dᴴ * D)) 1 := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let K := wordActivityHilbertSubspace (A := A)
  change K ≤ Module.End.eigenspace
    (Matrix.toEuclideanLin (𝕜 := ℝ) (Dᴴ * D)) 1
  intro v hv
  apply Module.End.mem_eigenspace_iff.mpr
  have hvfun := (mem_wordActivityHilbertSubspace_iff v).mp hv
  have hD := keyedSbox_fixes_wordActivitySubspace S _ hvfun
  have hDt := keyedSbox_transpose_fixes_wordActivitySubspace S _ hvfun
  have hGram : (Dᴴ * D) *ᵥ
      ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v) =
      ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v) := by
    rw [← Matrix.mulVec_mulVec,
      Matrix.conjTranspose_eq_transpose_of_trivial, hD, hDt]
  apply (WithLp.linearEquiv 2 ℝ (A → ℝ)).injective
  simpa only [one_smul, Matrix.toEuclideanLin_apply,
    WithLp.linearEquiv_apply] using hGram

/-- The Gram matrix of a keyed permutation family's difference-distribution
matrix has an eigenvalue-one space of dimension at least two. This is the
spectral content of the paper's two fixed singular vectors. -/
theorem keyedDifferenceDistributionMatrix_one_eigenspace_finrank
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (u : A) (hu : u ≠ 0) :
    let D := differenceDistributionMatrix
      (fun key : κ => fun a : A => S key a)
    2 ≤ Module.finrank ℝ
      (Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℝ) (Dᴴ * D)) 1) := by
  have hK := keyedDifferenceDistributionMatrix_wordActivity_le_one_eigenspace S
  have hdim := Submodule.finrank_mono hK
  rw [wordActivityHilbertSubspace_finrank u hu] at hdim
  exact hdim

/-- The first two *ordered* singular values of a finite family of
permutations' difference-distribution matrix are one. The paper's two
activity directions account for both positions, including multiplicity. -/
theorem keyedDifferenceDistributionMatrix_first_two_singularValues_eq_one
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A) :
    let D := differenceDistributionMatrix
      (fun key : κ => fun a : A => S key a)
    differenceMatrixSingularValue D ⟨0, by omega⟩ = 1 ∧
      differenceMatrixSingularValue D ⟨1, by omega⟩ = 1 := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let G := Dᴴ * D
  let hG : G.IsHermitian := Matrix.isHermitian_transpose_mul_self D
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) G
  let hT : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hG
  let j : Fin (Fintype.card A) := ⟨1, by omega⟩
  let z : Fin (Fintype.card A) := ⟨0, by omega⟩
  letI : Nontrivial A :=
    (Fintype.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : A)
  have hdim : 2 ≤ Module.finrank ℝ (Module.End.eigenspace T 1) :=
    keyedDifferenceDistributionMatrix_one_eigenspace_finrank S u hu
  have hEigLe (i : Fin (Fintype.card A)) :
      hT.eigenvalues finrank_euclideanSpace i ≤ 1 := by
    have hs := keyedDifferenceDistributionMatrix_singularValue_le_one S i
    have hsq := differenceMatrixSingularValue_sq D i
    have hsqle : differenceMatrixSingularValue D i ^ 2 ≤ 1 := by
      nlinarith [differenceMatrixSingularValue_nonneg D i]
    rw [hsq] at hsqle
    exact hsqle
  have hsecondEig : hT.eigenvalues finrank_euclideanSpace j = 1 :=
    secondEigenvalue_eq_one_of_two_fixed_directions
      T hT finrank_euclideanSpace (by omega) hdim hEigLe
  have hsecond : differenceMatrixSingularValue D j = 1 := by
    have hsq := differenceMatrixSingularValue_sq D j
    have hsq' : differenceMatrixSingularValue D j ^ 2 = 1 := by
      rw [hsq]
      exact hsecondEig
    nlinarith [differenceMatrixSingularValue_nonneg D j]
  have hfirst : differenceMatrixSingularValue D z = 1 := by
    have hge := (differenceMatrixSingularValue_antitone D)
      (show z ≤ j by simp [z, j])
    have hle := keyedDifferenceDistributionMatrix_singularValue_le_one S z
    rw [hsecond] at hge
    linarith
  exact ⟨hfirst, hsecond⟩

end ActivityDirections

end PairwiseIndependence
