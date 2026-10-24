import PairwiseIndependence.Pairwise.SingularValues

/-!
# The two fixed difference directions exhaust the unit eigenspace below a spectral gap

The paper identifies the third singular value after removing the two fixed
zero/nonzero activity directions. This file isolates the finite-dimensional
eigenspace-counting step needed for that identification.
-/

namespace PairwiseIndependence

/-- An operator diagonal in an orthonormal basis has norm bounded by a
uniform bound on its diagonal entries. The paper uses this fact through the
SVD; this real Hilbert-space version serves the Gram-matrix proof. -/
theorem norm_le_of_orthonormalBasis_diagonal
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (F : E →L[ℝ] E)
    (e : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hdiag : ∀ i, F (b i) = e i • b i)
    (he : ∀ i, |e i| ≤ c) : ‖F‖ ≤ c := by
  have hcoord (v : E) (i : ι) :
      b.repr (F v) i = e i * b.repr v i := by
    suffices h : ∀ w : EuclideanSpace ℝ ι,
        F (b.repr.symm w) = b.repr.symm (fun j => e j * w j) by
      simpa [OrthonormalBasis.sum_repr_symm] using
        congrArg (fun x => b.repr x i) (h (b.repr v))
    intro w
    simp_rw [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, hdiag]
    apply Fintype.sum_congr
    intro j
    rw [smul_smul, mul_comm]
  apply ContinuousLinearMap.opNorm_le_bound F hc
  intro v
  have hsq : ‖F v‖ ^ 2 ≤ c ^ 2 * ‖v‖ ^ 2 := by
    have hsum :
        (∑ i : ι, ‖e i * b.repr v i‖ ^ 2) ≤
          c ^ 2 * ∑ i : ι, ‖b.repr v i‖ ^ 2 := by
      calc
        (∑ i : ι, ‖e i * b.repr v i‖ ^ 2) ≤
            ∑ i : ι, c ^ 2 * ‖b.repr v i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_mul, Real.norm_eq_abs, mul_pow]
          have hsqle : |e i| ^ 2 ≤ c ^ 2 := by
            nlinarith [he i, abs_nonneg (e i)]
          exact mul_le_mul_of_nonneg_right hsqle (sq_nonneg _)
        _ = c ^ 2 * ∑ i : ι, ‖b.repr v i‖ ^ 2 := by rw [Finset.mul_sum]
    have hreprF := b.repr.norm_map (F v)
    have hreprV := b.repr.norm_map v
    rw [← hreprF, ← hreprV, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    simpa only [hcoord] using hsum
  have hnonneg : 0 ≤ c * ‖v‖ := mul_nonneg hc (norm_nonneg v)
  nlinarith [norm_nonneg (F v)]

private theorem eigenvector_mem_orthogonal_one_eigenspace_of_lt_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (v : E) (eig : ℝ) (hv : T v = eig • v) (hlt : eig < 1) :
    v ∈ (Module.End.eigenspace T 1)ᗮ := by
  apply ((Module.End.eigenspace T 1).mem_orthogonal' v).mpr
  intro w hw
  have hwEig : T w = w := by
    simpa only [one_smul] using (Module.End.mem_eigenspace_iff.mp hw)
  have hs := hT v w
  rw [hv, hwEig] at hs
  simp only [inner_smul_left] at hs
  have hs' : eig * inner ℝ v w = inner ℝ v w := by simpa using hs
  have hneq : eig - 1 ≠ 0 := by linarith
  apply (mul_eq_zero.mp ?_).resolve_left hneq
  calc
    (eig - 1) * inner ℝ v w = eig * inner ℝ v w - inner ℝ v w := by ring
    _ = 0 := sub_eq_zero.mpr hs'

/-- Three independent fixed vectors leave a fixed direction orthogonal to
any subspace of dimension at most two. -/
private theorem exists_fixed_orthogonal_of_three_fixed_vectors
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ}
    (T : E →ₗ[ℝ] E) (b : OrthonormalBasis (Fin m) ℝ E)
    (hm3 : 3 ≤ m) (K : Submodule ℝ E)
    (hKdim : Module.finrank ℝ K ≤ 2)
    (hfix : ∀ i : Fin 3, T (b (Fin.castLE hm3 i)) = b (Fin.castLE hm3 i)) :
    ∃ v : E, v ≠ 0 ∧ v ∈ Kᗮ ∧ T v = v := by
  let f : Fin 3 → E := fun i => b (Fin.castLE hm3 i)
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range f)
  have hLI : LinearIndependent ℝ f :=
    b.toBasis.linearIndependent.comp _ (Fin.castLE_injective hm3)
  have hWdim : Module.finrank ℝ W = 3 := by
    simpa [W, f] using (finrank_span_eq_card hLI)
  let P : W →ₗ[ℝ] K := K.orthogonalProjection.toLinearMap.comp W.subtype
  have hker : LinearMap.ker P ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    omega
  have hkerdim : 0 < Module.finrank ℝ (LinearMap.ker P) := by
    exact (Submodule.one_le_finrank_iff.mpr hker)
  obtain ⟨v, hvne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkerdim
  let w : W := v.1
  have hwne : w ≠ 0 := by
    intro hw
    apply hvne
    apply Subtype.ext
    exact hw
  have hwP : P w = 0 := v.2
  have hwQ : (w : E) ∈ Kᗮ := by
    apply K.orthogonalProjection_eq_zero_iff.mp
    exact hwP
  have hWfixed : W ≤ Module.End.eigenspace T 1 := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    apply Module.End.mem_eigenspace_iff.mpr
    simpa only [one_smul] using hfix i
  refine ⟨w, ?_, hwQ, ?_⟩
  · exact_mod_cast hwne
  · simpa only [one_smul] using
      (Module.End.mem_eigenspace_iff.mp (hWfixed w.2))

private theorem one_eigenspace_finrank_le_two_of_third_lt_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ}
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hm : Module.finrank ℝ E = m) (hm3 : 3 ≤ m)
    (hthird : hT.eigenvalues hm ⟨2, hm3⟩ < 1) :
    Module.finrank ℝ (Module.End.eigenspace T 1) ≤ 2 := by
  classical
  let z : Fin m := ⟨0, by omega⟩
  let o : Fin m := ⟨1, by omega⟩
  let t : Fin m := ⟨2, hm3⟩
  let b := hT.eigenvectorBasis hm
  have htail (i : Fin m) (hi : i ∉ ({z, o} : Finset (Fin m))) :
      hT.eigenvalues hm i < 1 := by
    have hit : t ≤ i := by
      apply Fin.le_iff_val_le_val.mpr
      have hiz : i.val ≠ 0 := by
        intro heq
        apply hi
        simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        apply Fin.ext
        simpa [z] using heq
      have hio : i.val ≠ 1 := by
        intro heq
        apply hi
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        apply Fin.ext
        simpa [o] using heq
      dsimp [t]
      omega
    exact lt_of_le_of_lt (hT.eigenvalues_antitone hm hit) hthird
  have hsubset : Module.End.eigenspace T 1 ≤
      Submodule.span ℝ ({b z, b o} : Set E) := by
    intro v hv
    have hvT : T v = v := by
      simpa only [one_smul] using (Module.End.mem_eigenspace_iff.mp hv)
    have hcoord (i : Fin m) (hi : i ∉ ({z, o} : Finset (Fin m))) :
        b.repr v i = 0 := by
      have h := hT.eigenvectorBasis_apply_self_apply hm v i
      rw [hvT] at h
      have hnonzero : 1 - hT.eigenvalues hm i ≠ 0 := by
        have := htail i hi
        linarith
      have hmul : (1 - hT.eigenvalues hm i) * b.repr v i = 0 := by
        change b.repr v i = hT.eigenvalues hm i * b.repr v i at h
        calc
          (1 - hT.eigenvalues hm i) * b.repr v i =
              b.repr v i - hT.eigenvalues hm i * b.repr v i := by ring
          _ = 0 := sub_eq_zero.mpr h
      exact (mul_eq_zero.mp hmul).resolve_left hnonzero
    have hsum : v = ∑ i ∈ ({z, o} : Finset (Fin m)), b.repr v i • b i := by
      calc
        v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
        _ = ∑ i ∈ ({z, o} : Finset (Fin m)), b.repr v i • b i := by
          apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro i _ hi
          simp [hcoord i hi]
    rw [hsum]
    apply Submodule.sum_mem
    intro i hi
    rcases Finset.mem_insert.mp hi with hiz | hio
    · subst i
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · have : i = o := by simpa using hio
      subst i
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact (Submodule.finrank_mono hsubset).trans
    ((finrank_span_le_card (R := ℝ) ({b z, b o} : Set E)).trans
      (by simpa using (Finset.card_le_two (a := b z) (b := b o))))

open scoped Matrix Matrix.Norms.L2Operator

/-- Centering a permutation-family difference-distribution matrix removes
exactly the two fixed directions from its Gram matrix. This is the matrix
identity behind the paper's third-singular-value argument. -/
theorem keyedDifferenceDistributionMatrix_centered_gram
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ] (S : κ → A ≃ A) :
    let D := differenceDistributionMatrix
      (fun key : κ => fun a : A => S key a)
    let U := uniformDifferenceDistributionMatrix A
    (D - U)ᴴ * (D - U) = Dᴴ * D - U := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let U := uniformDifferenceDistributionMatrix A
  change (D - U)ᴴ * (D - U) = Dᴴ * D - U
  have hUD : U * D = U :=
    uniform_mul_differenceDistributionMatrix _ (fun key => (S key).bijective)
  have hUstar : Uᴴ = U := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact uniformDifferenceDistributionMatrix_transpose A
  have hDstarU : Dᴴ * U = U := by
    have h := congrArg Matrix.conjTranspose hUD
    simpa only [Matrix.conjTranspose_mul, hUstar] using h
  have hUU : U * U = U := uniformDifferenceDistributionMatrix_mul_self
  rw [Matrix.conjTranspose_sub, hUstar, sub_mul, mul_sub, mul_sub,
    hDstarU, hUD, hUU]
  abel

/-- The squared Euclidean operator norm of the centered
difference-distribution matrix is the norm of the centered Gram matrix. -/
theorem keyedDifferenceDistributionMatrix_centered_norm_sq
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ] (S : κ → A ≃ A) :
    let D := differenceDistributionMatrix
      (fun key : κ => fun a : A => S key a)
    let U := uniformDifferenceDistributionMatrix A
    ‖D - U‖ ^ 2 = ‖Dᴴ * D - U‖ := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let U := uniformDifferenceDistributionMatrix A
  change ‖D - U‖ ^ 2 = ‖Dᴴ * D - U‖
  rw [← keyedDifferenceDistributionMatrix_centered_gram S]
  simpa only [pow_two, Matrix.star_eq_conjTranspose] using
    (CStarRing.norm_star_mul_self (x := D - U)).symm

/-- If the paper's third ordered singular value is below one, its two
zero/nonzero activity directions are *all* the singular directions with value
one. This is the eigenspace form of the spectral gap needed to identify the
third value with the norm of `D − U`. -/
theorem keyedDifferenceDistributionMatrix_one_eigenspace_eq_wordActivity_of_third_lt_one
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A)
    (hgap : differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard < 1) :
    let D := differenceDistributionMatrix
      (fun key : κ => fun a : A => S key a)
    wordActivityHilbertSubspace (A := A) =
      Module.End.eigenspace (Matrix.toEuclideanLin (𝕜 := ℝ) (Dᴴ * D)) 1 := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let G := Dᴴ * D
  let hG : G.IsHermitian := Matrix.isHermitian_transpose_mul_self D
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) G
  let hT : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hG
  let K := wordActivityHilbertSubspace (A := A)
  change K = Module.End.eigenspace T 1
  have hthird : hT.eigenvalues finrank_euclideanSpace ⟨2, hcard⟩ < 1 := by
    have hsq := differenceMatrixSingularValue_sq D ⟨2, hcard⟩
    have hsq' : differenceMatrixThirdSingularValue D hcard ^ 2 =
        hT.eigenvalues finrank_euclideanSpace ⟨2, hcard⟩ := hsq
    rw [← hsq']
    have hnonneg := differenceMatrixThirdSingularValue_nonneg D hcard
    nlinarith
  have hdimle : Module.finrank ℝ (Module.End.eigenspace T 1) ≤ 2 :=
    one_eigenspace_finrank_le_two_of_third_lt_one T hT
      finrank_euclideanSpace hcard hthird
  letI : Nontrivial A :=
    (Fintype.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : A)
  have hdimK : Module.finrank ℝ K = 2 := wordActivityHilbertSubspace_finrank u hu
  have hsub : K ≤ Module.End.eigenspace T 1 :=
    keyedDifferenceDistributionMatrix_wordActivity_le_one_eigenspace S
  have hdim : Module.finrank ℝ K =
      Module.finrank ℝ (Module.End.eigenspace T 1) := by
    have := Submodule.finrank_mono hsub
    omega
  exact Submodule.eq_of_le_of_finrank_eq hsub hdim

/-- One direction of the paper's third-singular-value identity, in the
spectral-gap case. The third Gram eigenvector is orthogonal to the two fixed
activity directions, so centering does not alter its eigenvalue. -/
theorem keyedDifferenceDistributionMatrix_thirdSingularValue_le_centered_norm_of_lt_one
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A)
    (hgap : differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard < 1) :
    differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard ≤
      ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
        uniformDifferenceDistributionMatrix A‖ := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let U := uniformDifferenceDistributionMatrix A
  let G := Dᴴ * D
  let hG : G.IsHermitian := Matrix.isHermitian_transpose_mul_self D
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) G
  let hT : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hG
  let K := wordActivityHilbertSubspace (A := A)
  let j : Fin (Fintype.card A) := ⟨2, hcard⟩
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  let v : EuclideanSpace ℝ A := b j
  let eig := hT.eigenvalues finrank_euclideanSpace j
  have hEigSq : eig = differenceMatrixThirdSingularValue D hcard ^ 2 := by
    exact (differenceMatrixSingularValue_sq D j).symm
  have hEigLt : eig < 1 := by
    rw [hEigSq]
    have hnonneg := differenceMatrixThirdSingularValue_nonneg D hcard
    nlinarith
  have hKeig : K = Module.End.eigenspace T 1 :=
    keyedDifferenceDistributionMatrix_one_eigenspace_eq_wordActivity_of_third_lt_one
      S hcard hgap
  have hvEig : T v = eig • v := hT.apply_eigenvectorBasis finrank_euclideanSpace j
  have hvQ : v ∈ Kᗮ := by
    apply (K.mem_orthogonal' v).mpr
    intro w hw
    have hwEig : T w = w := by
      have hw' : w ∈ Module.End.eigenspace T 1 := hKeig ▸ hw
      simpa only [one_smul] using (Module.End.mem_eigenspace_iff.mp hw')
    have hs := hT v w
    rw [hvEig, hwEig] at hs
    simp only [inner_smul_left] at hs
    have hs' : eig * inner ℝ v w = inner ℝ v w := by simpa using hs
    have hinner : inner ℝ v w = 0 := by
      have hneq : eig - 1 ≠ 0 := by linarith
      apply (mul_eq_zero.mp ?_).resolve_left hneq
      calc
        (eig - 1) * inner ℝ v w = eig * inner ℝ v w - inner ℝ v w := by ring
        _ = 0 := sub_eq_zero.mpr hs'
    exact hinner
  have hUv : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) U v = 0 := by
    rw [uniform_word_eq_activity_projection (by omega : 2 ≤ Fintype.card A)]
    simpa only [Submodule.starProjection_apply, Submodule.coe_eq_zero] using
      (K.orthogonalProjection_eq_zero_iff.mpr hvQ)
  have hGv : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) G v = eig • v := hvEig
  have hcenterEig : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (G - U) v = eig • v := by
    rw [matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply, hGv, hUv, sub_zero]
  have hvnorm : ‖v‖ = 1 := b.norm_eq_one j
  have hEigLe : eig ≤ ‖G - U‖ := by
    have h := (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (G - U)).le_opNorm v
    rw [hcenterEig, norm_smul, hvnorm, mul_one] at h
    have hEigNonneg : 0 ≤ eig := by rw [hEigSq]; positivity
    simpa only [Matrix.cstar_norm_def, Real.norm_eq_abs,
      abs_of_nonneg hEigNonneg, mul_one] using h
  have hnormsq : ‖D - U‖ ^ 2 = ‖G - U‖ :=
    keyedDifferenceDistributionMatrix_centered_norm_sq S
  have hnonneg := differenceMatrixThirdSingularValue_nonneg D hcard
  change differenceMatrixThirdSingularValue D hcard ≤ ‖D - U‖
  rw [hEigSq, ← hnormsq] at hEigLe
  nlinarith [norm_nonneg (D - U)]

/-- The converse spectral-gap bound: centering zeroes the first two Gram
eigenvalues and leaves the remaining eigenvalues unchanged. -/
theorem keyedDifferenceDistributionMatrix_centered_norm_le_thirdSingularValue_of_lt_one
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A)
    (hgap : differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard < 1) :
    ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
        uniformDifferenceDistributionMatrix A‖ ≤
      differenceMatrixThirdSingularValue
        (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let U := uniformDifferenceDistributionMatrix A
  let G := Dᴴ * D
  let hG : G.IsHermitian := Matrix.isHermitian_transpose_mul_self D
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) G
  let hT : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hG
  let K := wordActivityHilbertSubspace (A := A)
  let j : Fin (Fintype.card A) := ⟨2, hcard⟩
  let z : Fin (Fintype.card A) := ⟨0, by omega⟩
  let o : Fin (Fintype.card A) := ⟨1, by omega⟩
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  let eig := hT.eigenvalues finrank_euclideanSpace
  let F := Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (G - U)
  have hEigSq (i : Fin (Fintype.card A)) :
      eig i = differenceMatrixSingularValue D i ^ 2 := by
    exact (differenceMatrixSingularValue_sq D i).symm
  have hEigNonneg (i : Fin (Fintype.card A)) : 0 ≤ eig i := by
    rw [hEigSq]
    positivity
  have hEigGap : eig j < 1 := by
    rw [hEigSq]
    change differenceMatrixThirdSingularValue D hcard ^ 2 < 1
    have hnonneg := differenceMatrixThirdSingularValue_nonneg D hcard
    nlinarith
  have hKeig : K = Module.End.eigenspace T 1 :=
    keyedDifferenceDistributionMatrix_one_eigenspace_eq_wordActivity_of_third_lt_one
      S hcard hgap
  have hfirst : differenceMatrixSingularValue D z = 1 ∧
      differenceMatrixSingularValue D o = 1 :=
    keyedDifferenceDistributionMatrix_first_two_singularValues_eq_one S hcard
  have hfirstEig (i : Fin (Fintype.card A)) (hi : i.val < 2) : eig i = 1 := by
    have hcases : i = z ∨ i = o := by
      by_cases hzero : i.val = 0
      · left
        exact Fin.ext hzero
      · right
        have hone : i.val = 1 := by omega
        apply Fin.ext
        exact hone
    rcases hcases with hzero | hone
    · rw [hzero]
      rw [hEigSq, hfirst.1]
      norm_num
    · rw [hone]
      rw [hEigSq, hfirst.2]
      norm_num
  have hU (v : EuclideanSpace ℝ A) :
      Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) U v = K.starProjection v :=
    uniform_word_eq_activity_projection (A := A) (by omega) v
  have hdiag (i : Fin (Fintype.card A)) :
      F (b i) = (if i.val < 2 then 0 else eig i) • b i := by
    have hGbi : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) G (b i) = eig i • b i :=
      hT.apply_eigenvectorBasis finrank_euclideanSpace i
    by_cases hi : i.val < 2
    · have hbiK : b i ∈ K := by
        rw [hKeig]
        apply Module.End.mem_eigenspace_iff.mpr
        simpa [hfirstEig i hi] using hGbi
      have hUbi : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) U (b i) = b i := by
        rw [hU]
        exact K.starProjection_eq_self_iff.mpr hbiK
      simp only [F, matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply,
        hGbi, hUbi, hfirstEig i hi, one_smul, sub_self,
        if_pos hi, zero_smul]
    · have hji : j ≤ i := Fin.le_iff_val_le_val.mpr (by dsimp [j]; omega)
      have hlt : eig i < 1 := lt_of_le_of_lt
        (hT.eigenvalues_antitone finrank_euclideanSpace hji) hEigGap
      have hbiQ : b i ∈ Kᗮ := by
        rw [hKeig]
        exact eigenvector_mem_orthogonal_one_eigenspace_of_lt_one
          T hT (b i) (eig i)
          (hT.apply_eigenvectorBasis finrank_euclideanSpace i) hlt
      have hUbi : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) U (b i) = 0 := by
        rw [hU]
        simpa only [Submodule.starProjection_apply, Submodule.coe_eq_zero] using
          (K.orthogonalProjection_eq_zero_iff.mpr hbiQ)
      simp only [F, matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply,
        hGbi, hUbi, sub_zero, if_neg hi]
  have hdiagBound (i : Fin (Fintype.card A)) :
      |if i.val < 2 then (0 : ℝ) else eig i| ≤ eig j := by
    by_cases hi : i.val < 2
    · simp [hi, hEigNonneg j]
    · have hji : j ≤ i := Fin.le_iff_val_le_val.mpr (by dsimp [j]; omega)
      simpa [hi, abs_of_nonneg (hEigNonneg i)] using
        (hT.eigenvalues_antitone finrank_euclideanSpace hji)
  have hFle : ‖G - U‖ ≤ eig j := by
    exact norm_le_of_orthonormalBasis_diagonal b F
      (fun i => if i.val < 2 then 0 else eig i) (eig j)
      (hEigNonneg j) hdiag hdiagBound
  have hnormsq : ‖D - U‖ ^ 2 = ‖G - U‖ :=
    keyedDifferenceDistributionMatrix_centered_norm_sq S
  have hthirdsq : eig j = differenceMatrixThirdSingularValue D hcard ^ 2 :=
    hEigSq j
  have hthirdNonneg := differenceMatrixThirdSingularValue_nonneg D hcard
  change ‖D - U‖ ≤ differenceMatrixThirdSingularValue D hcard
  rw [← hnormsq, hthirdsq] at hFle
  nlinarith [norm_nonneg (D - U)]

/-- The paper's third-singular-value identity for a keyed permutation family
when its third ordered value has a strict gap below one. -/
theorem keyedDifferenceDistributionMatrix_thirdSingularValue_eq_centered_norm_of_lt_one
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A)
    (hgap : differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard < 1) :
    differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard =
      ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
        uniformDifferenceDistributionMatrix A‖ := by
  exact le_antisymm
    (keyedDifferenceDistributionMatrix_thirdSingularValue_le_centered_norm_of_lt_one
      S hcard hgap)
    (keyedDifferenceDistributionMatrix_centered_norm_le_thirdSingularValue_of_lt_one
      S hcard hgap)

/-- If the third ordered singular value is one, a third unit Gram direction
survives outside the paper's two-dimensional activity subspace. -/
theorem keyedDifferenceDistributionMatrix_centered_norm_eq_one_of_third_eq_one
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A)
    (hthird : differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard = 1) :
    ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
      uniformDifferenceDistributionMatrix A‖ = 1 := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  let U := uniformDifferenceDistributionMatrix A
  let G := Dᴴ * D
  let hG : G.IsHermitian := Matrix.isHermitian_transpose_mul_self D
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) G
  let hT : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hG
  let K := wordActivityHilbertSubspace (A := A)
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  letI : Nontrivial A :=
    (Fintype.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : A)
  have hKdim : Module.finrank ℝ K ≤ 2 := by
    rw [wordActivityHilbertSubspace_finrank u hu]
  have hfirst := keyedDifferenceDistributionMatrix_first_two_singularValues_eq_one
    S hcard
  have hfix (i : Fin 3) : T (b (Fin.castLE hcard i)) =
      b (Fin.castLE hcard i) := by
    have hsing : differenceMatrixSingularValue D (Fin.castLE hcard i) = 1 := by
      fin_cases i
      · simpa using hfirst.1
      · simpa using hfirst.2
      · simpa [differenceMatrixThirdSingularValue] using hthird
    have heig : hT.eigenvalues finrank_euclideanSpace (Fin.castLE hcard i) = 1 := by
      have hsq : differenceMatrixSingularValue D (Fin.castLE hcard i) ^ 2 =
          hT.eigenvalues finrank_euclideanSpace (Fin.castLE hcard i) :=
        differenceMatrixSingularValue_sq D _
      rw [hsing] at hsq
      norm_num at hsq
      exact hsq.symm
    rw [hT.apply_eigenvectorBasis, heig]
    simp [b]
  obtain ⟨v, hvne, hvQ, hvT⟩ :=
    exists_fixed_orthogonal_of_three_fixed_vectors T b hcard K hKdim hfix
  have hUv : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) U v = 0 := by
    rw [uniform_word_eq_activity_projection (A := A) (by omega) v]
    simpa only [Submodule.starProjection_apply, Submodule.coe_eq_zero] using
      (K.orthogonalProjection_eq_zero_iff.mpr hvQ)
  have hGv : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) G v = v := hvT
  have hcenterV : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (G - U) v = v := by
    rw [matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply, hGv, hUv, sub_zero]
  have hGnormge : 1 ≤ ‖G - U‖ := by
    have h := (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (G - U)).le_opNorm v
    rw [hcenterV] at h
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have h' : ‖v‖ ≤ ‖G - U‖ * ‖v‖ := by
      simpa only [Matrix.cstar_norm_def] using h
    nlinarith
  have hnormsq : ‖D - U‖ ^ 2 = ‖G - U‖ :=
    keyedDifferenceDistributionMatrix_centered_norm_sq S
  have hnormle : ‖D - U‖ ≤ 1 := by
    calc
      ‖D - U‖ = ‖keyedSboxActivityComplementOperator S‖ :=
        (keyedSboxActivityComplementOperator_norm_eq_sub_uniform S (by omega)).symm
      _ ≤ 1 := keyedSboxActivityComplementOperator_norm_le_one S
  change ‖D - U‖ = 1
  rw [← hnormsq] at hGnormge
  nlinarith [norm_nonneg (D - U)]

/-- The paper's singular-value lemma: after the two fixed zero/nonzero
difference directions, the third ordered singular value is exactly the norm
of the difference-distribution matrix minus the uniform benchmark. -/
theorem keyedDifferenceDistributionMatrix_thirdSingularValue_eq_centered_norm
    {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    [Fintype κ] [Nonempty κ]
    (S : κ → A ≃ A) (hcard : 3 ≤ Fintype.card A) :
    differenceMatrixThirdSingularValue
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) hcard =
      ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
        uniformDifferenceDistributionMatrix A‖ := by
  let D := differenceDistributionMatrix
    (fun key : κ => fun a : A => S key a)
  have hle : differenceMatrixThirdSingularValue D hcard ≤ 1 :=
    keyedDifferenceDistributionMatrix_thirdSingularValue_le_one S hcard
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact keyedDifferenceDistributionMatrix_thirdSingularValue_eq_centered_norm_of_lt_one
      S hcard hlt
  · rw [heq]
    exact (keyedDifferenceDistributionMatrix_centered_norm_eq_one_of_third_eq_one
      S hcard heq).symm

/-- The literal fixed-S-box form of the paper's third-singular-value lemma,
used in Theorem 3 for two-round SHARK. -/
theorem deterministicDifferenceDistributionMatrix_thirdSingularValue_eq_centered_norm
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (S : A ≃ A) (hcard : 3 ≤ Fintype.card A) :
    differenceMatrixThirdSingularValue
      (deterministicDifferenceDistributionMatrix (fun a : A => S a)) hcard =
      ‖deterministicDifferenceDistributionMatrix (fun a : A => S a) -
        uniformDifferenceDistributionMatrix A‖ := by
  exact keyedDifferenceDistributionMatrix_thirdSingularValue_eq_centered_norm
    (κ := Unit) (fun _ => S) hcard

end PairwiseIndependence
