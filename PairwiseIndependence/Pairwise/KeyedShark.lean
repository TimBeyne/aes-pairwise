import PairwiseIndependence.Pairwise.Spectral

namespace PairwiseIndependence
open scoped Matrix Matrix.Norms.L2Operator
variable {A κ : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] [Fintype κ]
variable {n : ℕ}

omit [Fintype κ] in
/-- A fixed choice of word keys has a product differential count. -/
theorem keyedSubstitute_differenceCount_eq_prod
    (S : κ → A ≃ A) (key : Fin n → κ) (b a : State A n) :
    differenceCount (keyedSubstitute S key) b a =
      ∏ i : Fin n, differenceCount (fun x : A => S (key i) x) (b i) (a i) := by
  classical
  change (∑ x : State A n,
    if keyedSubstitute S key (x + a) = keyedSubstitute S key x + b then 1 else 0) =
    ∏ i : Fin n, ∑ x : A,
      if S (key i) (x + a i) = S (key i) x + b i then 1 else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hiff : keyedSubstitute S key (x + a) = keyedSubstitute S key x + b ↔
      ∀ i : Fin n, S (key i) (x i + a i) = S (key i) (x i) + b i := by
    simp [keyedSubstitute, funext_iff, Pi.add_apply]
  simp only [hiff]
  simp [Fintype.prod_ite_zero]

/-- Averaging independent word keys gives the tensor power of the averaged
one-word difference-distribution matrix. -/
theorem keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix
    (S : κ → A ≃ A) :
    differenceDistributionMatrix (keyedSubstitute (n := n) S) =
      tensorWordMatrix (n := n)
        (differenceDistributionMatrix (fun key : κ => fun x : A => S key x)) := by
  classical
  ext b a
  simp only [tensorWordMatrix, differenceDistributionMatrix_eq_count]
  simp_rw [keyedSubstitute_differenceCount_eq_prod]
  simp only [Fintype.card_pi_const, Nat.cast_pow]
  rw [Finset.prod_div_distrib]
  rw [Fintype.prod_sum]
  simp only [Nat.cast_prod]
  simp only [Finset.prod_const, Finset.card_fin, mul_pow]

/-- An additive permutation on the input acts on the input-difference index
of an averaged family just as it does for a deterministic function. -/
theorem differenceDistributionMatrix_family_comp_addEquiv
    (f : κ → A → A) (L : A ≃+ A) :
    differenceDistributionMatrix (fun key x => f key (L x)) =
      differenceDistributionMatrix f *
        deterministicDifferenceDistributionMatrix (fun x => L x) := by
  classical
  ext b a
  rw [Matrix.mul_apply, differenceDistributionMatrix_eq_count]
  have hcount (key : κ) :
      differenceCount (fun x => f key (L x)) b a =
        differenceCount (f key) b (L a) := by
    unfold differenceCount
    simp only [map_add]
    exact Fintype.sum_equiv L.toEquiv _ _ (fun x => rfl)
  simp_rw [hcount]
  have hL (d : A) :
      deterministicDifferenceDistributionMatrix (fun x : A => L x) d a =
        if L a = d then 1 else 0 :=
    deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom d a
  simp_rw [hL]
  simp only [mul_ite, mul_one, mul_zero]
  simp
  exact (differenceDistributionMatrix_eq_count f b (L a)).symm

omit [DecidableEq A] [Fintype κ] in
/-- The paper's two-round SHARK core with a fixed S-box is the keyed core over
a one-element key space; the key reindexing forgets the trivial word keys. -/
theorem sharkTwoCore_differenceDistributionMatrix_eq_keyed
    (S : A ≃ A) (L : State A n ≃+ State A n) :
    differenceDistributionMatrix (sharkTwoCore S L) =
      differenceDistributionMatrix (keyedSharkTwoCore (fun _ : Unit => S) L) := by
  let e : (Fin n → Unit) × (Fin n → Unit) × State A n ≃ State A n :=
    { toFun := fun key => key.2.2
      invFun := fun key => (fun _ => (), fun _ => (), key)
      left_inv := fun key => Prod.ext (Subsingleton.elim _ _)
        (Prod.ext (Subsingleton.elim _ _) rfl)
      right_inv := fun _ => rfl }
  exact (differenceDistributionMatrix_key_reindex e (sharkTwoCore S L)).symm

/-- The keyed two-round core has exactly the paper's SHARK matrix sandwich,
with the averaged one-word difference-distribution matrix on both sides. -/
theorem keyedSharkTwoCore_differenceDistributionMatrix
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) :
    differenceDistributionMatrix (keyedSharkTwoCore S L) =
      tensorWordMatrix (n := n)
        (differenceDistributionMatrix (fun key : κ => fun x : A => S key x)) *
      deterministicDifferenceDistributionMatrix (fun x : State A n => L x) *
      tensorWordMatrix (n := n)
        (differenceDistributionMatrix (fun key : κ => fun x : A => S key x)) := by
  calc
    differenceDistributionMatrix (keyedSharkTwoCore S L) =
        differenceDistributionMatrix
          (independentlyKeyedComposition (keyedSubstitute S)
            (fun key x => keyedSubstitute S key (L x))) := rfl
    _ = differenceDistributionMatrix (fun key x => keyedSubstitute S key (L x)) *
          differenceDistributionMatrix (keyedSubstitute S) :=
      differenceDistributionMatrix_independentlyKeyedComposition _ _
    _ = _ := by
      rw [differenceDistributionMatrix_family_comp_addEquiv,
        keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix]

/-- The averaged one-word difference-distribution matrix fixes the zero-difference direction. -/
theorem keyedSbox_fixes_wordZeroIndicator [Nonempty κ] (S : κ → A ≃ A) :
    differenceDistributionMatrix (fun key : κ => fun x : A => S key x) *ᵥ
      wordZeroIndicator (A := A) = wordZeroIndicator (A := A) := by
  funext b
  change (∑ a : A,
    differenceDistributionMatrix (fun key : κ => fun x : A => S key x) b a *
      wordZeroIndicator (A := A) a) = wordZeroIndicator (A := A) b
  simp [wordZeroIndicator, differenceDistributionMatrix_zero_input]

/-- The transpose of the averaged one-word matrix fixes the same direction. -/
theorem keyedSbox_transpose_fixes_wordZeroIndicator [Nonempty κ]
    (S : κ → A ≃ A) :
    (differenceDistributionMatrix (fun key : κ => fun x : A => S key x))ᵀ *ᵥ
      wordZeroIndicator (A := A) = wordZeroIndicator (A := A) := by
  funext b
  change (∑ a : A,
    differenceDistributionMatrix (fun key : κ => fun x : A => S key x) a b *
      wordZeroIndicator (A := A) a) = wordZeroIndicator (A := A) b
  by_cases hb : b = 0
  · subst b
    simp [wordZeroIndicator, differenceDistributionMatrix_zero_input]
  · simp [wordZeroIndicator,
      differenceDistributionMatrix_zero_output
        (fun key : κ => fun x : A => S key x)
        (fun key => (S key).injective) hb, hb]

/-- The averaged matrix fixes the all-differences direction. -/
theorem keyedSbox_fixes_wordAllIndicator [Nonempty κ] (S : κ → A ≃ A) :
    differenceDistributionMatrix (fun key : κ => fun x : A => S key x) *ᵥ
      wordAllIndicator (A := A) = wordAllIndicator (A := A) := by
  funext b
  change (∑ a : A,
    differenceDistributionMatrix (fun key : κ => fun x : A => S key x) b a *
      wordAllIndicator (A := A) a) = wordAllIndicator (A := A) b
  simpa [wordAllIndicator] using
    differenceDistributionMatrix_row_sum
      (fun key : κ => fun x : A => S key x)
      (fun key => (S key).bijective) b

/-- The transpose fixes the all-differences direction by column stochasticity. -/
theorem keyedSbox_transpose_fixes_wordAllIndicator [Nonempty κ]
    (S : κ → A ≃ A) :
    (differenceDistributionMatrix (fun key : κ => fun x : A => S key x))ᵀ *ᵥ
      wordAllIndicator (A := A) = wordAllIndicator (A := A) := by
  funext b
  change (∑ a : A,
    differenceDistributionMatrix (fun key : κ => fun x : A => S key x) a b *
      wordAllIndicator (A := A) a) = wordAllIndicator (A := A) b
  simpa [wordAllIndicator] using
    differenceDistributionMatrix_column_sum
      (fun key : κ => fun x : A => S key x) b

/-- The averaged one-word matrix is the identity on the paper's activity space. -/
theorem keyedSbox_fixes_wordActivitySubspace [Nonempty κ]
    (S : κ → A ≃ A) (v : A → ℝ)
    (hv : v ∈ wordActivitySubspace (A := A)) :
    differenceDistributionMatrix (fun key : κ => fun x : A => S key x) *ᵥ v = v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rw [hx]
        exact keyedSbox_fixes_wordZeroIndicator S
      · rw [hx]
        exact keyedSbox_fixes_wordAllIndicator S
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mulVec_smul, hx]

/-- The transpose is also the identity on the word activity space. -/
theorem keyedSbox_transpose_fixes_wordActivitySubspace [Nonempty κ]
    (S : κ → A ≃ A) (v : A → ℝ)
    (hv : v ∈ wordActivitySubspace (A := A)) :
    (differenceDistributionMatrix (fun key : κ => fun x : A => S key x))ᵀ *ᵥ v = v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rw [hx]
        exact keyedSbox_transpose_fixes_wordZeroIndicator S
      · rw [hx]
        exact keyedSbox_transpose_fixes_wordAllIndicator S
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mulVec_smul, hx]

/-- The independently keyed parallel word layer fixes each activity-box
indicator exactly, as in the deterministic substitution calculation. -/
theorem keyedSubstitute_fixes_activityBox [Nonempty κ]
    (S : κ → A ≃ A) (z : Fin n → Bool) :
    differenceDistributionMatrix (keyedSubstitute (n := n) S) *ᵥ
      activityBoxIndicator (A := A) z =
        activityBoxIndicator (A := A) z := by
  rw [activityBoxIndicator_eq_spectralTensor,
    keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix,
    tensorWordMatrix_mulVec_spectralTensor]
  congr 1
  funext i
  cases hzi : z i
  · simpa [activityWordVector, hzi] using keyedSbox_fixes_wordZeroIndicator S
  · simpa [activityWordVector, hzi] using keyedSbox_fixes_wordAllIndicator S

/-- The averaged independent-key substitution matrix is the identity on the
paper's full-state activity space `V`. -/
theorem keyedSubstitute_fixes_activitySubspace [Nonempty κ]
    (S : κ → A ≃ A) (v : State A n → ℝ)
    (hv : v ∈ activitySubspace (A := A) (n := n)) :
    differenceDistributionMatrix (keyedSubstitute (n := n) S) *ᵥ v = v := by
  change v ∈ Submodule.span ℝ
    (Set.range (activityBoxIndicator (A := A) (n := n))) at hv
  induction hv using Submodule.span_induction with
  | mem _ h =>
      rcases h with ⟨z, rfl⟩
      exact keyedSubstitute_fixes_activityBox S z
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mulVec_smul, hx]

/-- The averaged one-word matrix preserves the word activity complement. -/
theorem keyedSbox_preserves_wordActivityOrthogonal [Nonempty κ]
    (S : κ → A ≃ A) (v : A → ℝ)
    (hv : InWordActivityOrthogonalComplement v) :
    InWordActivityOrthogonalComplement
      (differenceDistributionMatrix (fun key : κ => fun x : A => S key x) *ᵥ v) := by
  intro g hg
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    keyedSbox_transpose_fixes_wordActivitySubspace S g hg]
  exact hv g hg

/-- The averaged independent-key substitution matrix preserves each spectral
weight space `W_l` used in the paper's SHARK proof. -/
theorem keyedSbox_tensorWordMatrix_preserves_spectralWeightSubspace [Nonempty κ]
    (S : κ → A ≃ A) (l : ℕ) (v : State A n → ℝ)
    (hv : v ∈ spectralWeightSubspace (A := A) (n := n) l) :
    tensorWordMatrix (n := n)
      (differenceDistributionMatrix (fun key : κ => fun x : A => S key x)) *ᵥ v ∈
        spectralWeightSubspace (A := A) (n := n) l := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨I, f, hcard, horth, hact, rfl⟩ := hv
      rw [tensorWordMatrix_mulVec_spectralTensor]
      apply Submodule.subset_span
      refine ⟨I, (fun i => differenceDistributionMatrix
        (fun key : κ => fun x : A => S key x) *ᵥ f i), hcard, ?_, ?_, rfl⟩
      · intro i hi
        exact keyedSbox_preserves_wordActivityOrthogonal S (f i) (horth i hi)
      · intro i hi
        change differenceDistributionMatrix
          (fun key : κ => fun x : A => S key x) *ᵥ f i ∈ wordActivitySubspace
        rw [keyedSbox_fixes_wordActivitySubspace S (f i) (hact i hi)]
        exact hact i hi
  | zero => simp
  | add x y _ _ hx hy => simpa [Matrix.mulVec_add] using
      (Submodule.add_mem _ hx hy)
  | smul t x _ hx => simpa [Matrix.mulVec_smul] using
      (Submodule.smul_mem _ t hx)

/-- The actual independently keyed parallel substitution layer therefore
preserves each of the paper's spectral-weight spaces. -/
theorem keyedSubstitute_preserves_spectralWeightSubspace [Nonempty κ]
    (S : κ → A ≃ A) (l : ℕ) (v : State A n → ℝ)
    (hv : v ∈ spectralWeightSubspace (A := A) (n := n) l) :
    differenceDistributionMatrix (keyedSubstitute (n := n) S) *ᵥ v ∈
      spectralWeightSubspace (A := A) (n := n) l := by
  rw [keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix]
  exact keyedSbox_tensorWordMatrix_preserves_spectralWeightSubspace S l v hv

/-- The averaged keyed word matrix preserves the Hilbert-space complement of
the two activity directions. -/
theorem keyedSbox_preserves_wordHilbertOrthogonal [Nonempty κ]
    (S : κ → A ≃ A) (v : EuclideanSpace ℝ A)
    (hv : v ∈ (wordActivityHilbertSubspace (A := A))ᗮ) :
    Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) v ∈
        (wordActivityHilbertSubspace (A := A))ᗮ := by
  apply (inWordActivityOrthogonalComplement_iff_mem_orthogonal _).mp
  change InWordActivityOrthogonalComplement
    ((WithLp.linearEquiv 2 ℝ (A → ℝ))
      (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
        (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) v))
  simp only [WithLp.linearEquiv_apply, Matrix.ofLp_toEuclideanCLM]
  exact keyedSbox_preserves_wordActivityOrthogonal
    S _ ((inWordActivityOrthogonalComplement_iff_mem_orthogonal v).mpr hv)

/-- The quantitative one-word operator for an independently keyed S-box:
the averaged difference-distribution matrix restricted to the paper's
activity complement. -/
noncomputable def keyedSboxActivityComplementOperator (S : κ → A ≃ A) :
    (wordActivityHilbertSubspace (A := A))ᗮ →L[ℝ]
      (wordActivityHilbertSubspace (A := A))ᗮ :=
  ((wordActivityHilbertSubspace (A := A))ᗮ).orthogonalProjection ∘L
    Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) ∘L
        ((wordActivityHilbertSubspace (A := A))ᗮ).subtypeL

/-- The projected keyed operator agrees with the actual averaged matrix
action on vectors in the activity complement. -/
theorem keyedSboxActivityComplementOperator_apply [Nonempty κ]
    (S : κ → A ≃ A)
    (v : (wordActivityHilbertSubspace (A := A))ᗮ) :
    ((keyedSboxActivityComplementOperator S v :
      (wordActivityHilbertSubspace (A := A))ᗮ) : EuclideanSpace ℝ A) =
      Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
        (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) v := by
  let Q := (wordActivityHilbertSubspace (A := A))ᗮ
  have hmem : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a))
        (v : EuclideanSpace ℝ A) ∈ Q :=
    keyedSbox_preserves_wordHilbertOrthogonal S v v.property
  change ((Q.orthogonalProjection
      (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
        (differenceDistributionMatrix (fun key : κ => fun a : A => S key a))
        (v : EuclideanSpace ℝ A)) : Q) : EuclideanSpace ℝ A) = _
  exact congrArg Subtype.val
    (Q.orthogonalProjection_mem_subspace_eq_self ⟨_, hmem⟩)

/-- The one-word uniform difference-distribution matrix kills the paper's
activity complement. This is the bridge from a full-matrix superbox estimate
to the contraction parameter in keyed SHARK. -/
theorem uniformDifferenceDistributionMatrix_word_mulVec_eq_zero_of_orthogonal
    (v : A → ℝ) (hv : InWordActivityOrthogonalComplement v) :
    uniformDifferenceDistributionMatrix A *ᵥ v = 0 := by
  classical
  have hzero : v 0 = 0 := by
    have h := hv (wordZeroIndicator (A := A))
      (Submodule.subset_span (by simp :
        wordZeroIndicator (A := A) ∈
          ({wordZeroIndicator (A := A), wordAllIndicator (A := A)} : Set (A → ℝ))))
    simpa [wordActivitySubspace, wordZeroIndicator, dotProduct] using h
  have hsum : (∑ a : A, v a) = 0 := by
    have h := hv (wordAllIndicator (A := A))
      (Submodule.subset_span (by simp :
        wordAllIndicator (A := A) ∈
          ({wordZeroIndicator (A := A), wordAllIndicator (A := A)} : Set (A → ℝ))))
    simpa [wordActivitySubspace, wordAllIndicator, dotProduct] using h
  have hsum' : (∑ a : A, if a = 0 then (0 : ℝ) else v a) = 0 := by
    have hpartition : (∑ a : A, v a) =
        (∑ a : A, if a = 0 then v a else 0) +
          (∑ a : A, if a = 0 then 0 else v a) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    have hfirst : (∑ a : A, if a = 0 then v a else 0) = 0 := by
      simp [hzero]
    rw [hfirst] at hpartition
    linarith
  funext b
  by_cases hb : b = 0
  · subst b
    simp [Matrix.mulVec, dotProduct, uniformDifferenceDistributionMatrix_apply, hzero]
  · simp only [Pi.zero_apply, Matrix.mulVec, dotProduct,
      uniformDifferenceDistributionMatrix_apply, if_neg hb]
    calc
      (∑ a : A,
        (if a = 0 then (0 : ℝ)
          else 1 / ((Fintype.card A - 1 : ℕ) : ℝ)) * v a) =
          (1 / ((Fintype.card A - 1 : ℕ) : ℝ)) *
            (∑ a : A, if a = 0 then 0 else v a) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              by_cases ha : a = 0 <;> simp [ha]
      _ = 0 := by rw [hsum', mul_zero]

/-- The keyed superbox parameter is exactly the coordinate contraction of
the averaged one-word difference-distribution matrix on the paper's
activity complement. -/
theorem keyedSboxActivityComplementOperator_norm_le_iff [Nonempty κ]
    (S : κ → A ≃ A) (σ : ℝ) (hσ : 0 ≤ σ) :
    ‖keyedSboxActivityComplementOperator S‖ ≤ σ ↔
      ∀ v : A → ℝ, InWordActivityOrthogonalComplement v →
        ‖WithLp.toLp 2
          (differenceDistributionMatrix
            (fun key : κ => fun a : A => S key a) *ᵥ v)‖ ≤
          σ * ‖WithLp.toLp 2 v‖ := by
  let Q := (wordActivityHilbertSubspace (A := A))ᗮ
  let D := differenceDistributionMatrix (fun key : κ => fun a : A => S key a)
  constructor
  · intro hnorm v hv
    let qv : Q := ⟨WithLp.toLp 2 v,
      (inWordActivityOrthogonalComplement_iff_mem_orthogonal
        (WithLp.toLp 2 v)).mp (by simpa using hv)⟩
    have hbound := (keyedSboxActivityComplementOperator S).le_opNorm qv
    have hbound' : ‖keyedSboxActivityComplementOperator S qv‖ ≤
        σ * ‖qv‖ :=
      hbound.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg qv))
    simpa only [Submodule.coe_norm, keyedSboxActivityComplementOperator_apply,
      Matrix.toEuclideanCLM_toLp] using hbound'
  · intro hcontract
    apply ContinuousLinearMap.opNorm_le_bound _ hσ
    intro qv
    have hv : InWordActivityOrthogonalComplement
        ((WithLp.linearEquiv 2 ℝ (A → ℝ)) (qv : EuclideanSpace ℝ A)) :=
      (inWordActivityOrthogonalComplement_iff_mem_orthogonal
        (qv : EuclideanSpace ℝ A)).mpr qv.property
    have hbound := hcontract
      ((WithLp.linearEquiv 2 ℝ (A → ℝ)) (qv : EuclideanSpace ℝ A)) hv
    simpa only [Submodule.coe_norm, keyedSboxActivityComplementOperator_apply,
      Matrix.toEuclideanCLM_toLp] using hbound

/-- The keyed one-word activity-complement operator is a contraction,
because its averaged difference-distribution matrix is doubly stochastic. -/
theorem keyedSboxActivityComplementOperator_norm_le_one [Nonempty κ]
    (S : κ → A ≃ A) :
    ‖keyedSboxActivityComplementOperator S‖ ≤ 1 := by
  let D := differenceDistributionMatrix (fun key : κ => fun a : A => S key a)
  have hD : ‖D‖ ≤ 1 :=
    differenceDistributionMatrix_norm_le_one
      (fun key : κ => fun a : A => S key a) (fun key => (S key).bijective)
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  calc
    ‖keyedSboxActivityComplementOperator S v‖ =
        ‖Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) D
          (v : EuclideanSpace ℝ A)‖ := by
      simpa only [Submodule.coe_norm] using
        congrArg norm (keyedSboxActivityComplementOperator_apply S v)
    _ ≤ ‖D‖ * ‖(v : EuclideanSpace ℝ A)‖ := by
      simpa only [Matrix.cstar_norm_def] using
        (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) D).le_opNorm
          (v : EuclideanSpace ℝ A)
    _ ≤ 1 * ‖v‖ := by
      simpa only [Submodule.coe_norm] using
        mul_le_mul_of_nonneg_right hD (norm_nonneg v)

/-- A bound on the keyed superbox's full difference-distribution matrix
minus the uniform benchmark implies the contraction hypothesis used in
Theorem 3 for independently keyed SHARK. -/
theorem keyedSboxActivityComplementOperator_norm_le_sub_uniform [Nonempty κ]
    (S : κ → A ≃ A) :
    ‖keyedSboxActivityComplementOperator S‖ ≤
      ‖differenceDistributionMatrix (fun key : κ => fun a : A => S key a) -
        uniformDifferenceDistributionMatrix A‖ := by
  let D := differenceDistributionMatrix (fun key : κ => fun a : A => S key a)
  let U := uniformDifferenceDistributionMatrix A
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have hU : Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) U
      (v : EuclideanSpace ℝ A) = 0 := by
    apply (WithLp.linearEquiv 2 ℝ (A → ℝ)).injective
    change U *ᵥ ((WithLp.linearEquiv 2 ℝ (A → ℝ))
      (v : EuclideanSpace ℝ A)) = 0
    exact uniformDifferenceDistributionMatrix_word_mulVec_eq_zero_of_orthogonal
      _ ((inWordActivityOrthogonalComplement_iff_mem_orthogonal
        (v : EuclideanSpace ℝ A)).mpr v.property)
  calc
    ‖keyedSboxActivityComplementOperator S v‖ =
        ‖Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) D
          (v : EuclideanSpace ℝ A)‖ := by
      simpa only [Submodule.coe_norm] using
        congrArg norm (keyedSboxActivityComplementOperator_apply S v)
    _ = ‖Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (D - U)
          (v : EuclideanSpace ℝ A)‖ := by
      rw [matrix_toEuclideanCLM_sub, ContinuousLinearMap.sub_apply, hU, sub_zero]
    _ ≤ ‖D - U‖ * ‖(v : EuclideanSpace ℝ A)‖ := by
      simpa only [Matrix.cstar_norm_def] using
        (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) (D - U)).le_opNorm
          (v : EuclideanSpace ℝ A)
    _ = ‖D - U‖ * ‖v‖ := by simp only [Submodule.coe_norm]

/-- The averaged keyed word matrix fixes the paper's activity space in
Hilbert-space coordinates. -/
theorem keyedSbox_fixes_wordHilbertActivity [Nonempty κ]
    (S : κ → A ≃ A) (v : EuclideanSpace ℝ A)
    (hv : v ∈ wordActivityHilbertSubspace (A := A)) :
    Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) v = v := by
  apply (WithLp.linearEquiv 2 ℝ (A → ℝ)).injective
  simpa only [WithLp.linearEquiv_apply, Matrix.ofLp_toEuclideanCLM] using
    keyedSbox_fixes_wordActivitySubspace S
      ((WithLp.linearEquiv 2 ℝ (A → ℝ)) v)
      ((mem_wordActivityHilbertSubspace_iff v).mp hv)

/-- On the paper's two activity directions the averaged keyed word matrix is
the identity; on their orthogonal complement it is precisely the keyed
activity-complement operator. -/
theorem keyedSbox_activity_blockDiagonal [Nonempty κ]
    (S : κ → A ≃ A) (v : EuclideanSpace ℝ A) :
    Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) v =
      (wordActivityHilbertSubspace (A := A)).starProjection v +
        ((keyedSboxActivityComplementOperator S
          (((wordActivityHilbertSubspace (A := A))ᗮ).orthogonalProjection v) :
          (wordActivityHilbertSubspace (A := A))ᗮ) : EuclideanSpace ℝ A) := by
  let K := wordActivityHilbertSubspace (A := A)
  let Q := Kᗮ
  let F := Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
    (differenceDistributionMatrix (fun key : κ => fun a : A => S key a))
  have hsplit : K.starProjection v + Q.starProjection v = v :=
    K.starProjection_add_starProjection_orthogonal v
  have hK : F (K.starProjection v) = K.starProjection v :=
    keyedSbox_fixes_wordHilbertActivity S _ (K.starProjection_apply_mem v)
  have hQ : F (Q.starProjection v) =
      ((keyedSboxActivityComplementOperator S (Q.orthogonalProjection v) : Q) :
        EuclideanSpace ℝ A) := by
    have h := keyedSboxActivityComplementOperator_apply S (Q.orthogonalProjection v)
    simpa only [Q, Submodule.starProjection_apply] using h.symm
  change F v = K.starProjection v + _
  conv_lhs => rw [← hsplit]
  rw [map_add, hK, hQ]

/-- The averaged keyed word matrix preserves an exact choice of
complementary word positions. -/
theorem applyKeyedWordMatrixAt_preserves_spectralFactorSetSubspace [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n)) (i : Fin n)
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    applyWordMatrixAt
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) i v ∈
        spectralFactorSetSubspace (A := A) (n := n) I := by
  let D := differenceDistributionMatrix (fun key : κ => fun a : A => S key a)
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨f, horth, hact, rfl⟩ := hv
      rw [applyWordMatrixAt_spectralTensor]
      apply Submodule.subset_span
      refine ⟨Function.update f i (D *ᵥ f i), ?_, ?_, rfl⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa using keyedSbox_preserves_wordActivityOrthogonal
            S (f i) (horth i hj)
        · simpa [Function.update_of_ne hji] using horth j hj
      · intro j hj
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self]
          change D *ᵥ f i ∈ wordActivitySubspace (A := A)
          rw [keyedSbox_fixes_wordActivitySubspace S (f i) (hact i hj)]
          exact hact i hj
        · simpa [Function.update_of_ne hji] using hact j hj
  | zero =>
      have hzero : applyWordMatrixAt D i (0 : State A n → ℝ) = 0 := by
        funext x
        simp [applyWordMatrixAt]
      rw [hzero]
      exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
      rw [applyWordMatrixAt_add]
      exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
      rw [applyWordMatrixAt_smul]
      exact Submodule.smul_mem _ c hu

/-- One complementary word in an exact-factor-set summand contracts by the
restricted norm of the averaged keyed word matrix. -/
theorem applyKeyedWordMatrixAt_norm_le_of_factorSet [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n)) (i : Fin n) (hi : i ∈ I)
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    ‖WithLp.toLp 2
      (applyWordMatrixAt
        (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) i v)‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ * ‖WithLp.toLp 2 v‖ := by
  apply applyWordMatrixAt_norm_le_of_slice_bounds
    (differenceDistributionMatrix (fun key : κ => fun a : A => S key a))
    i v ‖keyedSboxActivityComplementOperator S‖
    (norm_nonneg (keyedSboxActivityComplementOperator S))
  intro x
  exact ((keyedSboxActivityComplementOperator_norm_le_iff S
    ‖keyedSboxActivityComplementOperator S‖
    (norm_nonneg (keyedSboxActivityComplementOperator S))).mp le_rfl)
    (stateWordSlice i x v)
    (spectralFactorSet_wordSlice_orthogonal I i hi v hv x)

/-- At an activity position, the averaged keyed word matrix acts as the
identity on the whole exact-factor-set summand. -/
theorem applyKeyedWordMatrixAt_eq_self_of_activityPosition [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n)) (i : Fin n) (hi : i ∉ I)
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    applyWordMatrixAt
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) i v = v := by
  funext x
  have h := congrFun
    (stateWordSlice_applyWordMatrixAt
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a))
      i x v) (x i)
  rw [stateWordSlice_originalWord,
    keyedSbox_fixes_wordActivitySubspace
      S _ (spectralFactorSet_wordSlice_activity I i hi v hv x),
    stateWordSlice_originalWord] at h
  exact h

/-- Applying the averaged keyed word matrix in a list of positions preserves
each exact-factor-set summand. -/
theorem applyKeyedWordMatrices_preserves_spectralFactorSetSubspace [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n)) (is : List (Fin n))
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    applyWordMatrices
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) is v ∈
        spectralFactorSetSubspace (A := A) (n := n) I := by
  induction is generalizing v with
  | nil => exact hv
  | cons i is ih =>
      exact ih _ (applyKeyedWordMatrixAt_preserves_spectralFactorSetSubspace
        S I i v hv)

/-- Applying the averaged word matrix at every state position is the same
as the difference-distribution matrix of independent keyed substitution. -/
theorem applyKeyedWordMatrices_finRange_eq_substitution [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n))
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    applyWordMatrices
      (differenceDistributionMatrix (fun key : κ => fun a : A => S key a))
      (List.finRange n) v =
      differenceDistributionMatrix (keyedSubstitute (n := n) S) *ᵥ v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨f, _, _, rfl⟩ := hv
      rw [applyWordMatrices_finRange_spectralTensor,
        keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix,
        tensorWordMatrix_mulVec_spectralTensor]
  | zero =>
      rw [applyWordMatrices_zero]
      simp
  | add u v _ _ hu hv =>
      rw [applyWordMatrices_add, Matrix.mulVec_add, hu, hv]
  | smul c u _ hu =>
      rw [applyWordMatrices_smul, Matrix.mulVec_smul, hu]

/-- Applying the averaged keyed word matrix successively contracts an
exact-factor-set summand once for every complementary position in the list. -/
theorem applyKeyedWordMatrices_norm_le_of_factorSet [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n)) (is : List (Fin n))
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    ‖WithLp.toLp 2
      (applyWordMatrices
        (differenceDistributionMatrix (fun key : κ => fun a : A => S key a)) is v)‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^
        is.countP (fun i => i ∈ I) * ‖WithLp.toLp 2 v‖ := by
  classical
  let D := differenceDistributionMatrix (fun key : κ => fun a : A => S key a)
  let σ := ‖keyedSboxActivityComplementOperator S‖
  have hσ : 0 ≤ σ := norm_nonneg (keyedSboxActivityComplementOperator S)
  induction is generalizing v with
  | nil =>
      simp [applyWordMatrices]
  | cons i is ih =>
      have hv' : applyWordMatrixAt D i v ∈
          spectralFactorSetSubspace (A := A) (n := n) I :=
        applyKeyedWordMatrixAt_preserves_spectralFactorSetSubspace S I i v hv
      by_cases hi : i ∈ I
      · have hstep := applyKeyedWordMatrixAt_norm_le_of_factorSet
          S I i hi v hv
        have htail := ih (applyWordMatrixAt D i v) hv'
        calc
          ‖WithLp.toLp 2 (applyWordMatrices D (i :: is) v)‖ =
              ‖WithLp.toLp 2
                (applyWordMatrices D is (applyWordMatrixAt D i v))‖ := rfl
          _ ≤ σ ^ is.countP (fun j => j ∈ I) *
              ‖WithLp.toLp 2 (applyWordMatrixAt D i v)‖ := htail
          _ ≤ σ ^ is.countP (fun j => j ∈ I) *
              (σ * ‖WithLp.toLp 2 v‖) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hσ _)
          _ = σ ^ (i :: is).countP (fun j => j ∈ I) *
              ‖WithLp.toLp 2 v‖ := by
            have hcount : (i :: is).countP (fun j => j ∈ I) =
                is.countP (fun j => j ∈ I) + 1 :=
              List.countP_cons_of_pos (by simpa using hi)
            rw [hcount, pow_succ]
            ring
      · have hfixed := applyKeyedWordMatrixAt_eq_self_of_activityPosition
          S I i hi v hv
        have htail := ih (applyWordMatrixAt D i v) hv'
        have hcount : (i :: is).countP (fun j => j ∈ I) =
            is.countP (fun j => j ∈ I) :=
          List.countP_cons_of_neg (by simpa using hi)
        rw [hfixed] at htail
        change ‖WithLp.toLp 2
          (applyWordMatrices D is (applyWordMatrixAt D i v))‖ ≤
          σ ^ (i :: is).countP (fun j => j ∈ I) * ‖WithLp.toLp 2 v‖
        rw [hfixed, hcount]
        simpa only [σ] using htail

/-- The `σ^l` bound extends from pure tensors to every vector with a fixed
set of complementary word positions. -/
theorem keyedSubstitute_spectralFactorSet_norm_le_complementOperator [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n))
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    ‖WithLp.toLp 2
      (differenceDistributionMatrix (keyedSubstitute (n := n) S) *ᵥ v)‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ I.card *
        ‖WithLp.toLp 2 v‖ := by
  rw [← applyKeyedWordMatrices_finRange_eq_substitution S I v hv]
  have h := applyKeyedWordMatrices_norm_le_of_factorSet
    S I (List.finRange n) v hv
  simpa only [finRange_countP_mem_eq_card] using h

/-- Independent keyed substitution preserves each exact-factor-set summand. -/
theorem keyedSubstitute_preserves_spectralFactorSetSubspace [Nonempty κ]
    (S : κ → A ≃ A) (I : Finset (Fin n))
    (v : State A n → ℝ)
    (hv : v ∈ spectralFactorSetSubspace (A := A) (n := n) I) :
    differenceDistributionMatrix (keyedSubstitute (n := n) S) *ᵥ v ∈
      spectralFactorSetSubspace (A := A) (n := n) I := by
  rw [← applyKeyedWordMatrices_finRange_eq_substitution S I v hv]
  exact applyKeyedWordMatrices_preserves_spectralFactorSetSubspace
    S I (List.finRange n) v hv

/-- The full paper-style `σ^l` contraction on `W_l` for independently keyed
word S-boxes. This is the keyed counterpart of the fixed-S-box result used
in Theorem 3. -/
theorem keyedSubstitute_spectralWeight_norm_le_complementOperator [Nonempty κ]
    (S : κ → A ≃ A) (l : ℕ)
    (v : EuclideanSpace ℝ (State A n))
    (hv : v ∈ spectralWeightHilbertSubspace (A := A) (n := n) l) :
    ‖Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (differenceDistributionMatrix (keyedSubstitute (n := n) S)) v‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ l * ‖v‖ := by
  let D := differenceDistributionMatrix (keyedSubstitute (n := n) S)
  let σ := ‖keyedSboxActivityComplementOperator S‖
  let T : EuclideanSpace ℝ (State A n) →ₗ[ℝ]
      EuclideanSpace ℝ (State A n) :=
    (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D).toLinearMap
  have hcoord (x : EuclideanSpace ℝ (State A n)) :
      (WithLp.linearEquiv 2 ℝ (State A n → ℝ)) (T x) =
        D *ᵥ ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) x) := by
    simp [T, WithLp.linearEquiv_apply, Matrix.ofLp_toEuclideanCLM]
  have hpres (I : {I : Finset (Fin n) // I.card = l})
      (x : EuclideanSpace ℝ (State A n))
      (hx : x ∈ spectralFactorSetHilbertSubspace (A := A) (n := n) I.1) :
      T x ∈ spectralFactorSetHilbertSubspace (A := A) (n := n) I.1 := by
    apply (mem_spectralFactorSetHilbertSubspace_iff I.1 (T x)).mpr
    rw [hcoord]
    exact keyedSubstitute_preserves_spectralFactorSetSubspace
      S I.1 _ ((mem_spectralFactorSetHilbertSubspace_iff I.1 x).mp hx)
  have hbound (I : {I : Finset (Fin n) // I.card = l})
      (x : EuclideanSpace ℝ (State A n))
      (hx : x ∈ spectralFactorSetHilbertSubspace (A := A) (n := n) I.1) :
      ‖T x‖ ≤ σ ^ l * ‖x‖ := by
    have hx' := (mem_spectralFactorSetHilbertSubspace_iff I.1 x).mp hx
    have h := keyedSubstitute_spectralFactorSet_norm_le_complementOperator
      S I.1 ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) x) hx'
    rw [I.2] at h
    simpa only [WithLp.linearEquiv_apply, Matrix.toEuclideanCLM_toLp] using h
  have hv' : v ∈ ⨆ I : {I : Finset (Fin n) // I.card = l},
      spectralFactorSetHilbertSubspace (A := A) (n := n) I.1 := by
    rw [← spectralWeightHilbertSubspace_eq_iSup_factorSet]
    exact hv
  exact orthogonalFamily_norm_le_of_summand_bounds
    (fun I : {I : Finset (Fin n) // I.card = l} =>
      spectralFactorSetHilbertSubspace (A := A) (n := n) I.1)
    (spectralFactorSetHilbertSubspaces_orthogonalFamily l)
    T (σ ^ l)
    (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)
    hpres hbound v hv'

/-- Replacing every key's S-box by its inverse transposes the averaged
one-word difference-distribution matrix. -/
theorem keyedSbox_symm_differenceDistributionMatrix_eq_transpose
    (S : κ → A ≃ A) :
    differenceDistributionMatrix (fun key : κ => fun x : A => (S key).symm x) =
      (differenceDistributionMatrix (fun key : κ => fun x : A => S key x))ᵀ := by
  ext b a
  rw [Matrix.transpose_apply]
  simp only [differenceDistributionMatrix_eq_count]
  have hcount (key : κ) :
      differenceCount (fun x : A => (S key).symm x) b a =
        differenceCount (fun x : A => S key x) a b := by
    unfold differenceCount
    calc
      (∑ y : A, if (S key).symm (y + a) = (S key).symm y + b then 1 else 0) =
          ∑ x : A, if (S key).symm (S key x + a) =
            (S key).symm (S key x) + b then 1 else 0 := by
        exact (Fintype.sum_equiv (S key) _ _ (fun x => rfl)).symm
      _ = ∑ x : A, if S key (x + b) = S key x + a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        have hiff : (S key).symm (S key x + a) =
            (S key).symm (S key x) + b ↔
            S key (x + b) = S key x + a := by
          simp only [Equiv.symm_apply_apply]
          constructor
          · intro h
            calc
              S key (x + b) = S key ((S key).symm (S key x + a)) := by rw [h]
              _ = S key x + a := (S key).apply_symm_apply _
          · intro h
            rw [← h, (S key).symm_apply_apply]
        simp only [hiff]
  simp_rw [hcount]

/-- The same inverse-family transpose identity holds for independently
keyed parallel substitution on the whole state. -/
theorem keyedSubstitute_symm_differenceDistributionMatrix_eq_transpose
    (S : κ → A ≃ A) :
    differenceDistributionMatrix
      (keyedSubstitute (n := n) (fun key => (S key).symm)) =
      (differenceDistributionMatrix (keyedSubstitute (n := n) S))ᵀ := by
  rw [keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix,
    keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix,
    keyedSbox_symm_differenceDistributionMatrix_eq_transpose]
  ext b a
  simp [tensorWordMatrix, Matrix.transpose_apply]

/-- Inverting every word S-box and the mixing layer transposes the keyed
two-round SHARK difference-distribution matrix. -/
theorem keyedSharkTwoCore_symm_differenceDistributionMatrix_eq_transpose
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) :
    differenceDistributionMatrix
      (keyedSharkTwoCore (fun key => (S key).symm) L.symm) =
      (differenceDistributionMatrix (keyedSharkTwoCore S L))ᵀ := by
  simp only [keyedSharkTwoCore_differenceDistributionMatrix,
    ← keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix]
  have hS := keyedSubstitute_symm_differenceDistributionMatrix_eq_transpose
    (n := n) S
  have hL := deterministicDifferenceDistributionMatrix_inverse_transpose
    L.toEquiv
  change deterministicDifferenceDistributionMatrix
    (fun x : State A n => L.symm x) =
    (deterministicDifferenceDistributionMatrix
      (fun x : State A n => L x))ᵀ at hL
  rw [hS, hL, Matrix.transpose_mul, Matrix.transpose_mul, mul_assoc]

/-- The transpose of independent keyed substitution also fixes the paper's
full-state activity space `V`. -/
theorem keyedSubstitute_transpose_fixes_activitySubspace [Nonempty κ]
    (S : κ → A ≃ A) (v : State A n → ℝ)
    (hv : v ∈ activitySubspace (A := A) (n := n)) :
    (differenceDistributionMatrix (keyedSubstitute (n := n) S))ᵀ *ᵥ v = v := by
  rw [← keyedSubstitute_symm_differenceDistributionMatrix_eq_transpose]
  exact keyedSubstitute_fixes_activitySubspace (fun key => (S key).symm) v hv

/-- The averaged keyed complement operator for inverse word S-boxes is
the Hilbert adjoint of the forward complement operator. -/
theorem keyedSboxActivityComplementOperator_symm_eq_adjoint
    (S : κ → A ≃ A) :
    keyedSboxActivityComplementOperator (fun key => (S key).symm) =
      ContinuousLinearMap.adjoint (keyedSboxActivityComplementOperator S) := by
  let Q := (wordActivityHilbertSubspace (A := A))ᗮ
  let D := differenceDistributionMatrix (fun key : κ => fun a : A => S key a)
  have hmatrix :
      Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
        (differenceDistributionMatrix
          (fun key : κ => fun a : A => (S key).symm a)) =
      ContinuousLinearMap.adjoint
        (Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) D) := by
    rw [keyedSbox_symm_differenceDistributionMatrix_eq_transpose]
    have hstar : star D = Dᵀ := by
      rw [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [← hstar, map_star, ContinuousLinearMap.star_eq_adjoint]
  change (Q.orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ)
        (differenceDistributionMatrix
          (fun key : κ => fun a : A => (S key).symm a)) ∘L
        Q.subtypeL) =
    ContinuousLinearMap.adjoint
      (Q.orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := A) (𝕜 := ℝ) D ∘L Q.subtypeL)
  rw [hmatrix]
  simp only [ContinuousLinearMap.adjoint_comp,
    Q.adjoint_subtypeL, Q.adjoint_orthogonalProjection]
  ext x
  rfl

/-- The forward and inverse averaged keyed word matrices have the same
operator norm on the paper's activity complement. -/
theorem keyedSboxActivityComplementOperator_symm_norm_eq
    (S : κ → A ≃ A) :
    ‖keyedSboxActivityComplementOperator (fun key => (S key).symm)‖ =
      ‖keyedSboxActivityComplementOperator S‖ := by
  rw [keyedSboxActivityComplementOperator_symm_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map (keyedSboxActivityComplementOperator S)

/-- Any sum of paper spectral-weight spaces of weight at least `k`
contracts by `σ^k` under independent keyed substitution. -/
theorem keyedSubstitute_spectralWeightIndexSet_norm_le_complementOperator
    [Nonempty κ] (S : κ → A ≃ A) (J : Finset ℕ) (k : ℕ)
    (hJ : ∀ l ∈ J, k ≤ l)
    (v : EuclideanSpace ℝ (State A n))
    (hv : v ∈ spectralWeightIndexSetHilbertSubspace (A := A) (n := n) J) :
    ‖Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (differenceDistributionMatrix (keyedSubstitute (n := n) S)) v‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ k * ‖v‖ := by
  let D := differenceDistributionMatrix (keyedSubstitute (n := n) S)
  let T : EuclideanSpace ℝ (State A n) →ₗ[ℝ]
      EuclideanSpace ℝ (State A n) :=
    (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D).toLinearMap
  let U (l : {l : ℕ // l ∈ J}) :=
    spectralWeightHilbertSubspace (A := A) (n := n) l.1
  have horth : OrthogonalFamily ℝ (fun l => U l)
      (fun l => (U l).subtypeₗᵢ) := by
    intro i j hij x y
    have hweights : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    apply spectralWeightSubspaces_euclidean_orthogonal i.1 j.1 hweights
    · exact (mem_spectralWeightHilbertSubspace_iff i.1 _).mp x.property
    · exact (mem_spectralWeightHilbertSubspace_iff j.1 _).mp y.property
  have hpres (l : {l : ℕ // l ∈ J})
      (x : EuclideanSpace ℝ (State A n)) (hx : x ∈ U l) :
      T x ∈ U l := by
    apply (mem_spectralWeightHilbertSubspace_iff l.1 (T x)).mpr
    change D *ᵥ ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) x) ∈
      spectralWeightSubspace (A := A) (n := n) l.1
    exact keyedSubstitute_preserves_spectralWeightSubspace
      S l.1 _ ((mem_spectralWeightHilbertSubspace_iff l.1 x).mp hx)
  have hbound (l : {l : ℕ // l ∈ J})
      (x : EuclideanSpace ℝ (State A n)) (hx : x ∈ U l) :
      ‖T x‖ ≤ ‖keyedSboxActivityComplementOperator S‖ ^ k * ‖x‖ := by
    have hfirst := keyedSubstitute_spectralWeight_norm_le_complementOperator
      S l.1 x hx
    have hpow : ‖keyedSboxActivityComplementOperator S‖ ^ l.1 ≤
        ‖keyedSboxActivityComplementOperator S‖ ^ k :=
      pow_le_pow_of_le_one
        (norm_nonneg (keyedSboxActivityComplementOperator S))
        (keyedSboxActivityComplementOperator_norm_le_one S) (hJ l.1 l.2)
    exact hfirst.trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg x))
  exact orthogonalFamily_norm_le_of_summand_bounds U horth T
    (‖keyedSboxActivityComplementOperator S‖ ^ k)
    (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)
    hpres hbound v hv

/-- The transpose has the same `σ^k` contraction on a sum of high-weight
spectral spaces. -/
theorem keyedSubstitute_spectralWeightIndexSet_transpose_norm_le_complementOperator
    [Nonempty κ] (S : κ → A ≃ A) (J : Finset ℕ) (k : ℕ)
    (hJ : ∀ l ∈ J, k ≤ l)
    (v : EuclideanSpace ℝ (State A n))
    (hv : v ∈ spectralWeightIndexSetHilbertSubspace (A := A) (n := n) J) :
    ‖Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (differenceDistributionMatrix (keyedSubstitute (n := n) S))ᵀ v‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ k * ‖v‖ := by
  have h := keyedSubstitute_spectralWeightIndexSet_norm_le_complementOperator
    (fun key => (S key).symm) J k hJ v hv
  rw [keyedSboxActivityComplementOperator_symm_norm_eq] at h
  rwa [keyedSubstitute_symm_differenceDistributionMatrix_eq_transpose] at h

/-- Projection of keyed substitution onto a high-weight spectral sum
contracts by the minimum weight's `σ` power, for arbitrary input. -/
theorem keyedSubstitute_spectralWeightIndexSet_projection_norm_le
    [Nonempty κ] (S : κ → A ≃ A) (J : Finset ℕ) (k : ℕ)
    (hJ : ∀ l ∈ J, k ≤ l)
    (v : EuclideanSpace ℝ (State A n)) :
    ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n) J).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
        (differenceDistributionMatrix (keyedSubstitute (n := n) S)) v)‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ k * ‖v‖ := by
  let Q := spectralWeightIndexSetHilbertSubspace (A := A) (n := n) J
  let T := differenceDistributionMatrix (keyedSubstitute (n := n) S)
  let F : EuclideanSpace ℝ (State A n) →L[ℝ] Q :=
    Q.orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T
  let G : Q →L[ℝ] EuclideanSpace ℝ (State A n) :=
    Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) Tᵀ ∘L Q.subtypeL
  have hG : ‖G‖ ≤ ‖keyedSboxActivityComplementOperator S‖ ^ k := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)
    intro x
    have hb := keyedSubstitute_spectralWeightIndexSet_transpose_norm_le_complementOperator
      S J k hJ (x : EuclideanSpace ℝ (State A n)) x.property
    simpa only [G, ContinuousLinearMap.comp_apply, Submodule.coe_norm] using hb
  have hmatrix : Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) Tᵀ =
      ContinuousLinearMap.adjoint
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T) := by
    have hstar : star T = Tᵀ := by
      rw [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [← hstar, map_star, ContinuousLinearMap.star_eq_adjoint]
  have hF : F = ContinuousLinearMap.adjoint G := by
    change (Q.orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T) =
      ContinuousLinearMap.adjoint
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) Tᵀ ∘L Q.subtypeL)
    rw [hmatrix]
    simp only [ContinuousLinearMap.adjoint_comp, Q.adjoint_subtypeL,
      ContinuousLinearMap.adjoint_adjoint]
  have hFnorm : ‖F‖ ≤ ‖keyedSboxActivityComplementOperator S‖ ^ k := by
    rw [hF, ContinuousLinearMap.adjoint.norm_map]
    exact hG
  have hb := F.le_opNorm v
  exact hb.trans (mul_le_mul_of_nonneg_right hFnorm (norm_nonneg v))

/-- The two independent keyed word layers contribute the minimum input and
output spectral weights on any two unions of paper weight spaces. -/
theorem keyedSharkTwoCore_spectralWeightIndexSets_projection_norm_le
    [Nonempty κ] (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (Jout Jin : Finset ℕ) (kout kin : ℕ)
    (hout : ∀ l ∈ Jout, kout ≤ l)
    (hin : ∀ l ∈ Jin, kin ≤ l)
    (v : EuclideanSpace ℝ (State A n))
    (hv : v ∈ spectralWeightIndexSetHilbertSubspace (A := A) (n := n) Jin) :
    ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n) Jout).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
        (differenceDistributionMatrix (keyedSharkTwoCore S L)) v)‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ (kout + kin) * ‖v‖ := by
  let T := differenceDistributionMatrix (keyedSubstitute (n := n) S)
  let M := deterministicDifferenceDistributionMatrix
    (fun x : State A n => L x)
  let σ := ‖keyedSboxActivityComplementOperator S‖
  have hM : ‖M‖ ≤ 1 :=
    differenceDistributionMatrix_norm_le_one
      (fun _ : Unit => (fun x : State A n => L x))
      (fun _ => L.bijective)
  have hact (x : EuclideanSpace ℝ (State A n)) :
      ‖Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖M‖ * ‖x‖ := by
        simpa only [Matrix.cstar_norm_def] using
          (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M).le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hfactor : Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (differenceDistributionMatrix (keyedSharkTwoCore S L)) v =
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
          (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T v)) := by
    rw [keyedSharkTwoCore_differenceDistributionMatrix]
    rw [← keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix]
    apply (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).injective
    simp only [WithLp.linearEquiv_apply, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec_mulVec]
    rw [mul_assoc]
  have hinput := keyedSubstitute_spectralWeightIndexSet_norm_le_complementOperator
    S Jin kin hin v hv
  have houtput := keyedSubstitute_spectralWeightIndexSet_projection_norm_le
    S Jout kout hout
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T v))
  rw [hfactor]
  calc
    _ ≤ σ ^ kout * ‖Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
        (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T v)‖ := houtput
    _ ≤ σ ^ kout * ‖Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) T v‖ :=
      mul_le_mul_of_nonneg_left (hact _)
        (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)
    _ ≤ σ ^ kout * (σ ^ kin * ‖v‖) :=
      mul_le_mul_of_nonneg_left hinput
        (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)
    _ = σ ^ (kout + kin) * ‖v‖ := by rw [pow_add]; ring

/-- The operator between two unions of spectral-weight spaces has the
paper's minimum-weight contraction for the keyed SHARK core. -/
theorem keyedSharkTwoCore_spectralWeightIndexSetBlock_norm_le
    [Nonempty κ] (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (Jout Jin : Finset ℕ) (kout kin : ℕ)
    (hout : ∀ l ∈ Jout, kout ≤ l)
    (hin : ∀ l ∈ Jin, kin ≤ l) :
    ‖spectralWeightIndexSetBlockOperator (A := A) (n := n) Jout Jin
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ (kout + kin) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (pow_nonneg (norm_nonneg (keyedSboxActivityComplementOperator S)) _)
  intro v
  have h := keyedSharkTwoCore_spectralWeightIndexSets_projection_norm_le
    S L Jout Jin kout kin hout hin
    (v : EuclideanSpace ℝ (State A n)) v.property
  simpa only [spectralWeightIndexSetBlockOperator,
    ContinuousLinearMap.comp_apply, Submodule.coe_norm] using h

/-- The mixed tail from the activity space `V` to weights above `l`. -/
theorem keyedSharkTwoCore_activityToHighWeight_norm_le [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) (l : ℕ) :
    ‖activityToHighWeightOperator (n := n) l
      (differenceDistributionMatrix (keyedSharkTwoCore S L))‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ (l + 1) := by
  have h := keyedSharkTwoCore_spectralWeightIndexSetBlock_norm_le
    S L (Finset.Icc (l + 1) n) {0} (l + 1) 0
    (by intro k hk; exact (Finset.mem_Icc.mp hk).1)
    (by intro k hk; simp only [Finset.mem_singleton] at hk; omega)
  rw [spectralWeightIndexSetBlockOperator,
    spectralWeightIndexSet_singleton_eq,
    spectralWeightZeroHilbert_eq_activity] at h
  simpa only [activityToHighWeightOperator, Nat.add_zero] using h

/-- The high-output, positive-input block has both paper minimum weights. -/
theorem keyedSharkTwoCore_highOutput_fromActivityComplement_norm_le [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) (l : ℕ) :
    ‖(spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
      (Finset.Icc (l + 1) n)).orthogonalProjection ∘L
        Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
          (differenceDistributionMatrix (keyedSharkTwoCore S L)) ∘L
        ((activityHilbertSubspace (A := A) (n := n))ᗮ).subtypeL‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ (l + 2) := by
  have h := keyedSharkTwoCore_spectralWeightIndexSetBlock_norm_le
    S L (Finset.Icc (l + 1) n) (Finset.Icc 1 n) (l + 1) 1
    (by intro k hk; exact (Finset.mem_Icc.mp hk).1)
    (by intro k hk; exact (Finset.mem_Icc.mp hk).1)
  rw [spectralWeightIndexSetBlockOperator,
    spectralWeightIndexSet_Icc_one_eq_activityOrthogonal] at h
  simpa only [show l + 1 + 1 = l + 2 by omega] using h

/-- The high-input tail of an individual `V⊥ → W_i` row. -/
theorem keyedSharkTwoCore_spectralRow_highInput_norm_le [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (i l : ℕ) (hi : i ≤ l) :
    ‖(spectralWeightHilbertSubspace (A := A) (n := n) i).orthogonalProjection ∘L
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
        (differenceDistributionMatrix (keyedSharkTwoCore S L)) ∘L
      (spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
        (Finset.Icc (l - i + 1) n)).subtypeL‖ ≤
        ‖keyedSboxActivityComplementOperator S‖ ^ (l + 1) := by
  have h := keyedSharkTwoCore_spectralWeightIndexSetBlock_norm_le
    S L {i} (Finset.Icc (l - i + 1) n) i (l - i + 1)
    (by intro k hk; exact le_of_eq (Finset.mem_singleton.mp hk).symm)
    (by intro k hk; exact (Finset.mem_Icc.mp hk).1)
  let F := Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
    (differenceDistributionMatrix (keyedSharkTwoCore S L))
  let T := spectralWeightIndexSetHilbertSubspace (A := A) (n := n)
    (Finset.Icc (l - i + 1) n)
  let f (U : Submodule ℝ (EuclideanSpace ℝ (State A n))) : ℝ :=
    ‖U.orthogonalProjection ∘L F ∘L T.subtypeL‖
  have heq := congrArg f (spectralWeightIndexSet_singleton_eq (A := A) (n := n) i)
  change f (spectralWeightIndexSetHilbertSubspace (A := A) (n := n) {i}) ≤
    ‖keyedSboxActivityComplementOperator S‖ ^ (i + (l - i + 1)) at h
  change f (spectralWeightHilbertSubspace (A := A) (n := n) i) ≤
    ‖keyedSboxActivityComplementOperator S‖ ^ (l + 1)
  rw [heq, show i + (l - i + 1) = l + 1 by omega] at h
  exact h

/-- The transpose of independently keyed substitution preserves each
spectral-weight space. -/
theorem keyedSubstitute_transpose_preserves_spectralWeightSubspace [Nonempty κ]
    (S : κ → A ≃ A) (l : ℕ) (v : State A n → ℝ)
    (hv : v ∈ spectralWeightSubspace (A := A) (n := n) l) :
    (differenceDistributionMatrix (keyedSubstitute (n := n) S))ᵀ *ᵥ v ∈
      spectralWeightSubspace (A := A) (n := n) l := by
  have h := keyedSubstitute_preserves_spectralWeightSubspace
    (fun key => (S key).symm) l v hv
  rwa [keyedSubstitute_symm_differenceDistributionMatrix_eq_transpose] at h

/-- The projection of an averaged keyed substitution output on `W_l`
depends only on the input's projection on `W_l`, and contracts by `σ^l`. -/
theorem keyedSubstitute_spectralWeight_projection_norm_le [Nonempty κ]
    (S : κ → A ≃ A) (l : ℕ) (y : EuclideanSpace ℝ (State A n)) :
    ‖(spectralWeightHilbertSubspace (A := A) (n := n) l).orthogonalProjection
      (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
        (differenceDistributionMatrix (keyedSubstitute (n := n) S)) y)‖ ≤
    ‖keyedSboxActivityComplementOperator S‖ ^ l *
      ‖(spectralWeightHilbertSubspace (A := A) (n := n) l).orthogonalProjection y‖ := by
  let W := spectralWeightHilbertSubspace (A := A) (n := n) l
  let D := differenceDistributionMatrix (keyedSubstitute (n := n) S)
  let T := Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D
  have hstar : star D = Dᵀ := by
    rw [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hadj : T.adjoint =
      Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) Dᵀ := by
    dsimp [T]
    rw [← hstar, map_star, ContinuousLinearMap.star_eq_adjoint]
  have hpres : ∀ u ∈ W, T.adjoint u ∈ W := by
    intro u hu
    rw [hadj]
    apply (mem_spectralWeightHilbertSubspace_iff l _).mpr
    change Dᵀ *ᵥ ((WithLp.linearEquiv 2 ℝ (State A n → ℝ)) u) ∈
      spectralWeightSubspace (A := A) (n := n) l
    exact keyedSubstitute_transpose_preserves_spectralWeightSubspace
      S l _ ((mem_spectralWeightHilbertSubspace_iff l u).mp hu)
  have hproj := projection_after_adjoint_invariant W T hpres y
  calc
    ‖W.orthogonalProjection (T y)‖ =
      ‖W.orthogonalProjection (T (W.starProjection y))‖ := congrArg norm hproj
    _ ≤ ‖T (W.starProjection y)‖ := W.norm_orthogonalProjection_apply_le _
    _ ≤ ‖keyedSboxActivityComplementOperator S‖ ^ l * ‖W.starProjection y‖ := by
      exact keyedSubstitute_spectralWeight_norm_le_complementOperator
        S l _ (W.starProjection_apply_mem y)
    _ = ‖keyedSboxActivityComplementOperator S‖ ^ l *
        ‖W.orthogonalProjection y‖ := rfl

set_option maxHeartbeats 800000 in
/-- Each `W_{l₂} → W_{l₁}` block of the independently keyed SHARK matrix
sandwich inherits the paper's `σ^(l₁+l₂)` factor from its two keyed word
layers, where `σ` is the norm of the averaged one-word complement operator. -/
theorem keyedSpectralWeightBlock_sandwich_norm_le [Nonempty κ]
    (S : κ → A ≃ A) (M : Matrix (State A n) (State A n) ℝ)
    (l₁ l₂ : ℕ) :
    ‖spectralWeightBlockOperator (n := n) l₁ l₂
      (differenceDistributionMatrix (keyedSubstitute (n := n) S) * M *
        differenceDistributionMatrix (keyedSubstitute (n := n) S))‖ ≤
      ‖keyedSboxActivityComplementOperator S‖ ^ (l₁ + l₂) *
        ‖spectralWeightBlockOperator (n := n) l₁ l₂ M‖ := by
  let W₁ := spectralWeightHilbertSubspace (A := A) (n := n) l₁
  let W₂ := spectralWeightHilbertSubspace (A := A) (n := n) l₂
  let D := differenceDistributionMatrix (keyedSubstitute (n := n) S)
  let T := Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) D
  let L := Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ) M
  let B := spectralWeightBlockOperator (n := n) l₁ l₂ M
  let σ := ‖keyedSboxActivityComplementOperator S‖
  let P := spectralWeightBlockOperator (n := n) l₁ l₂ (D * M * D)
  change ‖P‖ ≤ σ ^ (l₁ + l₂) * ‖B‖
  have hs : 0 ≤ σ := by
    dsimp [σ]
    exact norm_nonneg (keyedSboxActivityComplementOperator S)
  apply P.opNorm_le_bound (mul_nonneg (pow_nonneg hs _) (norm_nonneg B))
  intro x
  have hzmem : T (x : EuclideanSpace ℝ (State A n)) ∈ W₂ := by
    apply (mem_spectralWeightHilbertSubspace_iff l₂ _).mpr
    change D *ᵥ ((WithLp.linearEquiv 2 ℝ (State A n → ℝ))
      (x : EuclideanSpace ℝ (State A n))) ∈
      spectralWeightSubspace (A := A) (n := n) l₂
    exact keyedSubstitute_preserves_spectralWeightSubspace
      S l₂ _ ((mem_spectralWeightHilbertSubspace_iff l₂ _).mp x.property)
  let z : W₂ := ⟨T (x : EuclideanSpace ℝ (State A n)), hzmem⟩
  have hfactor : Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (D * M * D) (x : EuclideanSpace ℝ (State A n)) =
      T (L (T (x : EuclideanSpace ℝ (State A n)))) := by
    dsimp only [T, L]
    apply (WithLp.linearEquiv 2 ℝ (State A n → ℝ)).injective
    simp only [WithLp.linearEquiv_apply, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec_mulVec]
    rw [mul_assoc]
  have hright : ‖z‖ ≤ σ ^ l₂ * ‖x‖ := by
    change ‖T (x : EuclideanSpace ℝ (State A n))‖ ≤ _
    exact keyedSubstitute_spectralWeight_norm_le_complementOperator S l₂ _ x.property
  have hmiddle : ‖W₁.orthogonalProjection
      (L (T (x : EuclideanSpace ℝ (State A n))))‖ ≤
      ‖B‖ * ‖z‖ := by
    change ‖B z‖ ≤ ‖B‖ * ‖z‖
    exact B.le_opNorm z
  change ‖W₁.orthogonalProjection
    (Matrix.toEuclideanCLM (n := State A n) (𝕜 := ℝ)
      (D * M * D) (x : EuclideanSpace ℝ (State A n)))‖ ≤ _
  rw [hfactor]
  calc
    ‖W₁.orthogonalProjection (T (L (T (x : EuclideanSpace ℝ (State A n)))))‖ ≤
      σ ^ l₁ * ‖W₁.orthogonalProjection
        (L (T (x : EuclideanSpace ℝ (State A n))))‖ :=
        keyedSubstitute_spectralWeight_projection_norm_le S l₁ _
    _ ≤ σ ^ l₁ * (‖B‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left hmiddle (pow_nonneg hs _)
    _ ≤ σ ^ l₁ * (‖B‖ * (σ ^ l₂ * ‖x‖)) := by
      gcongr
    _ = (σ ^ (l₁ + l₂) * ‖B‖) * ‖x‖ := by
      rw [pow_add]
      ring

/-- Between vectors of the paper's activity space `V`, both averaged keyed
word layers disappear from the two-round SHARK matrix product. -/
theorem keyedSharkTwoCore_activity_pairing [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (v w : State A n → ℝ)
    (hv : v ∈ activitySubspace (A := A) (n := n))
    (hw : w ∈ activitySubspace (A := A) (n := n)) :
    v ⬝ᵥ differenceDistributionMatrix (keyedSharkTwoCore S L) *ᵥ w =
      v ⬝ᵥ deterministicDifferenceDistributionMatrix
        (fun x : State A n => L x) *ᵥ w := by
  let D := differenceDistributionMatrix (keyedSubstitute (n := n) S)
  let M := deterministicDifferenceDistributionMatrix
    (fun x : State A n => L x)
  have hright : D *ᵥ w = w :=
    keyedSubstitute_fixes_activitySubspace S w hw
  have hleft : Dᵀ *ᵥ v = v :=
    keyedSubstitute_transpose_fixes_activitySubspace S v hv
  rw [keyedSharkTwoCore_differenceDistributionMatrix]
  rw [← keyedSubstitute_differenceDistributionMatrix_eq_tensorWordMatrix]
  change v ⬝ᵥ ((D * M) * D) *ᵥ w = v ⬝ᵥ M *ᵥ w
  rw [← Matrix.mulVec_mulVec, hright, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hleft]

/-- The centered truncated-differential pairing of keyed two-round SHARK
equals the pairing of its linear mixing layer. -/
theorem keyedSharkTwoCore_centered_activity_pairing [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n)
    (v w : State A n → ℝ)
    (hv : v ∈ activitySubspace (A := A) (n := n))
    (hw : w ∈ activitySubspace (A := A) (n := n)) :
    v ⬝ᵥ
      (differenceDistributionMatrix (keyedSharkTwoCore S L) -
        uniformDifferenceDistributionMatrix (State A n)) *ᵥ w =
      v ⬝ᵥ
        (deterministicDifferenceDistributionMatrix
          (fun x : State A n => L x) -
          uniformDifferenceDistributionMatrix (State A n)) *ᵥ w := by
  simp only [Matrix.sub_mulVec, dotProduct_sub]
  rw [keyedSharkTwoCore_activity_pairing S L v w hv hw]

/-- The paper's exact truncated-differential reduction also holds for
independently keyed word layers. -/
theorem keyedSharkTwoCore_truncatedOperator_eq_linear [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) :
    activityTruncatedOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L) -
        uniformDifferenceDistributionMatrix (State A n)) =
      activityTruncatedOperator
        (deterministicDifferenceDistributionMatrix
          (fun x : State A n => L x) -
          uniformDifferenceDistributionMatrix (State A n)) := by
  apply activityTruncatedOperator_eq_of_pairing_eq
  intro v w hv hw
  exact keyedSharkTwoCore_centered_activity_pairing S L v w hv hw

/-- The truncated-differential bound for keyed two-round SHARK depends only
on its MDS mixing layer, exactly as for the fixed-S-box model. -/
theorem keyedSharkTwoCore_truncatedNorm_le_closedForm [Nonempty κ]
    (S : κ → A ≃ A) (L : State A n ≃+ State A n) (hMDS : IsMDS L)
    (hq : 4 ≤ Fintype.card A) (hn : 2 ≤ n) :
    ‖activityTruncatedOperator
      (differenceDistributionMatrix (keyedSharkTwoCore S L) -
        uniformDifferenceDistributionMatrix (State A n))‖ ≤
      (2 / (Real.sqrt (Fintype.card A : ℝ) - 1)) ^ n := by
  rw [keyedSharkTwoCore_truncatedOperator_eq_linear]
  exact sharkTruncatedDifferential L hMDS hq hn

end PairwiseIndependence
