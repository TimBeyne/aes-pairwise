import PairwiseIndependence.Pairwise.Spectral
import PairwiseIndependence.Pairwise.KeyedShark
import PairwiseIndependence.Pairwise.Stochastic

/-!
# MDS graph product bound for differential probabilities

This is the finite product-sum step behind the fourth-power use of a
two-round superbox differential bound. It is independent of the AES S-box
and of pairwise independence. Four bounded factors can be removed from a
product on an MDS graph; the other four factors sum to one because any four
graph coordinates determine the codeword.
-/

namespace PairwiseIndependence

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Precomposing a keyed permutation family by an additive equivalence
permutes its input-difference columns. -/
theorem differenceDistributionMatrix_family_comp_addEquiv_apply
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → A → A) (L : A ≃+ A) (b a : A) :
    differenceDistributionMatrix (fun key x => f key (L x)) b a =
      differenceDistributionMatrix f b (L a) := by
  classical
  rw [differenceDistributionMatrix_family_comp_addEquiv, Matrix.mul_apply]
  have hdet (d : A) :
      deterministicDifferenceDistributionMatrix (fun x : A => L x) d a =
        if L a = d then 1 else 0 :=
    deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom d a
  simp_rw [hdet]
  simp

/-- A product of eight normalized word distributions on a four-word MDS
graph is bounded by the product of four pointwise bounds. The sets `T` and
`S` partition the input/output graph coordinates into four positions each. -/
theorem IsMDS.graphProbabilityProduct_le_pow_four
    (L : State A 4 ≃+ State A 4) (hMDS : IsMDS L)
    (P : Sum (Fin 4) (Fin 4) → A → ℝ)
    (hPnonneg : ∀ j a, 0 ≤ P j a)
    (hPsum : ∀ j, ∑ a : A, P j a = 1)
    (T S : Finset (Sum (Fin 4) (Fin 4)))
    (hTS : Disjoint T S) (hcover : T ∪ S = Finset.univ)
    (hTcard : T.card = 4) (hScard : S.card = 4)
    (μ : ℝ)
    (hTbound : ∀ j ∈ T, ∀ a, P j a ≤ μ) :
    (∑ x : State A 4,
      ∏ j : Sum (Fin 4) (Fin 4), P j (mdsGraphCoordinate L x j)) ≤
      μ ^ 4 := by
  classical
  let e : State A 4 ≃ (S → A) :=
    Equiv.ofBijective (mdsGraphProjection L S)
      (hMDS.graphProjection_bijective L S hScard)
  have hsumS :
      (∑ x : State A 4,
        ∏ j ∈ S, P j (mdsGraphCoordinate L x j)) = 1 := by
    calc
      _ = ∑ y : S → A, ∏ j : S, P j.1 (y j) := by
        apply Fintype.sum_equiv e
        intro x
        simpa only [e, mdsGraphProjection] using
          (Finset.prod_subtype S (by simp)
            (fun j => P j (mdsGraphCoordinate L x j)))
      _ = ∏ j : S, ∑ a : A, P j.1 a := by
        rw [Fintype.prod_sum]
      _ = 1 := by simp [hPsum]
  have hpoint (x : State A 4) :
      (∏ j : Sum (Fin 4) (Fin 4), P j (mdsGraphCoordinate L x j)) ≤
        μ ^ 4 * (∏ j ∈ S, P j (mdsGraphCoordinate L x j)) := by
    have hsplit :
        (∏ j : Sum (Fin 4) (Fin 4), P j (mdsGraphCoordinate L x j)) =
          (∏ j ∈ T, P j (mdsGraphCoordinate L x j)) *
            (∏ j ∈ S, P j (mdsGraphCoordinate L x j)) := by
      rw [← hcover, Finset.prod_union hTS]
    rw [hsplit]
    have hT : (∏ j ∈ T, P j (mdsGraphCoordinate L x j)) ≤ μ ^ 4 := by
      calc
        _ ≤ ∏ _j ∈ T, μ := Finset.prod_le_prod
          (fun j _ => hPnonneg j _) (fun j hj => hTbound j hj _)
        _ = μ ^ 4 := by simp [hTcard]
    exact mul_le_mul_of_nonneg_right hT
      (Finset.prod_nonneg (fun j _ => hPnonneg j _))
  calc
    _ ≤ ∑ x : State A 4,
          μ ^ 4 * (∏ j ∈ S, P j (mdsGraphCoordinate L x j)) := by
        exact Finset.sum_le_sum (fun x _ => hpoint x)
    _ = μ ^ 4 := by rw [← Finset.mul_sum, hsumS, mul_one]

/-- The exact four-round keyed-SHARK differential entry is a product sum on
the graph of its middle MDS word layer. The left factors are rows of the
averaged one-superbox difference-distribution matrix and the right factors
are columns. -/
theorem keyedSharkTwoCore_differenceDistributionMatrix_apply_eq_graphProduct
    {W κ : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    [Fintype κ] [Nonempty κ]
    (S : κ → W ≃ W) (L : State W 4 ≃+ State W 4)
    (a b : State W 4) :
    differenceDistributionMatrix (keyedSharkTwoCore S L) b a =
      ∑ x : State W 4,
        ∏ j : Sum (Fin 4) (Fin 4),
          (Sum.elim
            (fun i z => differenceDistributionMatrix
              (fun key : κ => fun w : W => S key w) z (a i))
            (fun i z => differenceDistributionMatrix
              (fun key : κ => fun w : W => S key w) (b i) z)
            j) (mdsGraphCoordinate L x j) := by
  classical
  rw [keyedSharkTwoCore_differenceDistributionMatrix]
  have hM (y x : State W 4) :
      deterministicDifferenceDistributionMatrix (fun z : State W 4 => L z) y x =
        if L x = y then 1 else 0 := by
    exact deterministicDifferenceDistributionMatrix_addHom L.toAddMonoidHom y x
  simp only [Matrix.mul_apply]
  simp_rw [hM]
  simp [tensorWordMatrix, mdsGraphCoordinate, Fintype.prod_sum_type,
    mul_comm]

/-- The fourth-power differential bound follows from the one-superbox
maximum whenever four input/output word positions are active. The MDS graph
lemma sums the other four probability factors exactly. -/
theorem keyedSharkTwoCore_differential_le_four_of_active_positions
    {W κ : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    [Fintype κ] [Nonempty κ]
    (S : κ → W ≃ W) (L : State W 4 ≃+ State W 4)
    (hMDS : IsMDS L) (a b : State W 4)
    (μ : ℝ)
    (hword : ∀ u v : W, u ≠ 0 ∨ v ≠ 0 →
      differenceDistributionMatrix
        (fun key : κ => fun w : W => S key w) v u ≤ μ)
    (T R : Finset (Sum (Fin 4) (Fin 4)))
    (hTR : Disjoint T R) (hcover : T ∪ R = Finset.univ)
    (hTcard : T.card = 4) (hRcard : R.card = 4)
    (hactive : ∀ j ∈ T,
      match j with
      | Sum.inl i => a i ≠ 0
      | Sum.inr i => b i ≠ 0) :
    differenceDistributionMatrix (keyedSharkTwoCore S L) b a ≤ μ ^ 4 := by
  classical
  let D := differenceDistributionMatrix
    (fun key : κ => fun w : W => S key w)
  let P : Sum (Fin 4) (Fin 4) → W → ℝ :=
    Sum.elim (fun i z => D z (a i)) (fun i z => D (b i) z)
  have hentry : differenceDistributionMatrix (keyedSharkTwoCore S L) b a =
      ∑ x : State W 4,
        ∏ j : Sum (Fin 4) (Fin 4), P j (mdsGraphCoordinate L x j) := by
    simpa only [P, D] using
      keyedSharkTwoCore_differenceDistributionMatrix_apply_eq_graphProduct
        S L a b
  rw [hentry]
  apply hMDS.graphProbabilityProduct_le_pow_four L P
    (fun j z => by cases j <;> exact differenceDistributionMatrix_nonneg _ _ _)
    (fun j => by
      cases j with
      | inl i => exact differenceDistributionMatrix_column_sum _ (a i)
      | inr i =>
        exact differenceDistributionMatrix_row_sum _
          (fun key => (S key).bijective) (b i))
    T R hTR hcover hTcard hRcard μ
  intro j hj z
  cases j with
  | inl i => exact hword (a i) z (Or.inl (hactive _ hj))
  | inr i => exact hword z (b i) (Or.inr (hactive _ hj))

/-- The active-factor selection is automatic once at least four endpoint
words are active. The separate low-activity case is the remaining MDS
support argument in the concrete four-round application. -/
theorem keyedSharkTwoCore_differential_le_four_of_endpoint_activity
    {W κ : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    [Fintype κ] [Nonempty κ]
    (S : κ → W ≃ W) (L : State W 4 ≃+ State W 4)
    (hMDS : IsMDS L) (a b : State W 4)
    (μ : ℝ)
    (hword : ∀ u v : W, u ≠ 0 ∨ v ≠ 0 →
      differenceDistributionMatrix
        (fun key : κ => fun w : W => S key w) v u ≤ μ)
    (hactivity : 4 ≤ activeCoordinates a + activeCoordinates b) :
    differenceDistributionMatrix (keyedSharkTwoCore S L) b a ≤ μ ^ 4 := by
  classical
  let active : Finset (Sum (Fin 4) (Fin 4)) :=
    (Finset.univ.filter (fun i : Fin 4 => a i ≠ 0)).disjSum
      (Finset.univ.filter (fun i : Fin 4 => b i ≠ 0))
  have hacard : active.card = activeCoordinates a + activeCoordinates b := by
    simp [active, activeCoordinates, Finset.card_disjSum]
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := active) (hacard ▸ hactivity)
  let R : Finset (Sum (Fin 4) (Fin 4)) := Finset.univ \ T
  have hRcard : R.card = 4 := by
    simp [R, Finset.card_sdiff, hTcard, Fintype.card_sum]
  apply keyedSharkTwoCore_differential_le_four_of_active_positions
    S L hMDS a b μ hword T R
    (Finset.disjoint_sdiff)
    (Finset.union_sdiff_of_subset (Finset.subset_univ T))
    hTcard hRcard
  intro j hj
  have hja : j ∈ active := hTsub hj
  cases j with
  | inl i =>
    simpa only [active, Finset.inl_mem_disjSum, Finset.mem_filter,
      Finset.mem_univ, true_and] using hja
  | inr i =>
    simpa only [active, Finset.inr_mem_disjSum, Finset.mem_filter,
      Finset.mem_univ, true_and] using hja

/-- A nonzero input cannot produce a differential whose input and output
activity totals at most four, by the MDS branch number of the middle word
layer. This is the support half of the Keliher--Sui fourth-power reduction. -/
theorem keyedSharkTwoCore_differential_eq_zero_of_low_endpoint_activity
    {W κ : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    [Fintype κ] [Nonempty κ]
    (S : κ → W ≃ W) (L : State W 4 ≃+ State W 4)
    (hMDS : IsMDS L) (a b : State W 4) (ha : a ≠ 0)
    (hactivity : activeCoordinates a + activeCoordinates b ≤ 4) :
    differenceDistributionMatrix (keyedSharkTwoCore S L) b a = 0 := by
  classical
  let D := differenceDistributionMatrix
    (fun key : κ => fun w : W => S key w)
  let P : Sum (Fin 4) (Fin 4) → W → ℝ :=
    Sum.elim (fun i z => D z (a i)) (fun i z => D (b i) z)
  rw [show differenceDistributionMatrix (keyedSharkTwoCore S L) b a =
      ∑ x : State W 4,
        ∏ j : Sum (Fin 4) (Fin 4), P j (mdsGraphCoordinate L x j) by
      simpa only [P, D] using
        keyedSharkTwoCore_differenceDistributionMatrix_apply_eq_graphProduct
          S L a b]
  apply Finset.sum_eq_zero
  intro x _
  by_contra hprod
  have hfactor (j : Sum (Fin 4) (Fin 4)) :
      P j (mdsGraphCoordinate L x j) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ _)
  have hxin (i : Fin 4) : x i ≠ 0 → a i ≠ 0 := by
    intro hxi hai
    have h := hfactor (Sum.inl i)
    simp only [P, Sum.elim_inl, mdsGraphCoordinate] at h
    dsimp only [D] at h
    rw [hai, differenceDistributionMatrix_zero_input] at h
    simp [hxi] at h
  have hyout (i : Fin 4) : (L x) i ≠ 0 → b i ≠ 0 := by
    intro hyi hbi
    have h := hfactor (Sum.inr i)
    simp only [P, Sum.elim_inr, mdsGraphCoordinate] at h
    dsimp only [D] at h
    rw [hbi, differenceDistributionMatrix_zero_output _
      (fun key => (S key).injective) hyi] at h
    exact h rfl
  have hx : x ≠ 0 := by
    intro hx
    apply ha
    funext i
    change a i = 0
    by_contra hai
    have h := hfactor (Sum.inl i)
    simp only [P, Sum.elim_inl, mdsGraphCoordinate] at h
    dsimp only [D] at h
    rw [hx, Pi.zero_apply, differenceDistributionMatrix_zero_output _
      (fun key => (S key).injective) hai] at h
    exact h rfl
  have hxle : activeCoordinates x ≤ activeCoordinates a := by
    unfold activeCoordinates
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hxin i hi
  have hyle : activeCoordinates (L x) ≤ activeCoordinates b := by
    unfold activeCoordinates
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hyout i hi
  have hbranch := hMDS x hx
  omega

/-- Abstract fourth-power theorem for four-word keyed SHARK. An MDS middle
layer turns a bound on every nontrivial one-word differential into a bound
on every nontrivial four-word differential. The low-activity case vanishes;
in the other case, four active factors are bounded and the complementary
four factors sum to one. -/
theorem keyedSharkTwoCore_differential_le_four
    {W κ : Type*} [AddCommGroup W] [Fintype W] [DecidableEq W]
    [Fintype κ] [Nonempty κ]
    (S : κ → W ≃ W) (L : State W 4 ≃+ State W 4)
    (hMDS : IsMDS L) (μ : ℝ)
    (hword : ∀ u v : W, u ≠ 0 ∨ v ≠ 0 →
      differenceDistributionMatrix
        (fun key : κ => fun w : W => S key w) v u ≤ μ)
    (a b : State W 4) (ha : a ≠ 0) :
    differenceDistributionMatrix (keyedSharkTwoCore S L) b a ≤ μ ^ 4 := by
  by_cases hactivity : 4 ≤ activeCoordinates a + activeCoordinates b
  · exact keyedSharkTwoCore_differential_le_four_of_endpoint_activity
      S L hMDS a b μ hword hactivity
  · have hlow : activeCoordinates a + activeCoordinates b ≤ 4 := by omega
    rw [keyedSharkTwoCore_differential_eq_zero_of_low_endpoint_activity
      S L hMDS a b ha hlow]
    positivity

end PairwiseIndependence
